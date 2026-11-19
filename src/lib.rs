use crate::{
    flaws::{atom_flaw::AtomFlaw, bool_flaw::BoolFlaw, clause_flaw::ClauseFlaw, disjunction_flaw::DisjunctionFlaw, enum_flaw::EnumFlaw},
    graph::{Flaw, FlawId, Graph, Resolver, ResolverId},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    delegate_env, delegate_scope,
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, Var, to_cnf},
    language::{AtomKind, Disjunction, ResolutionConstraint},
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use semitone::{
    Lit, SeMiTONE, ast,
    rational::{InfRational, Rational},
};
use serde_json::{Value, json};
use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    error, fmt,
    rc::{Rc, Weak},
    str::FromStr,
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};

mod flaws;
mod graph;
mod objects;

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    smt: RefCell<SeMiTONE>,
    notified_len: Cell<usize>,
    graph: RefCell<Graph>,
    atom_sigma: RefCell<Vec<Option<ResolverId>>>,
    atom_flaw: RefCell<Vec<FlawId>>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl SolverState {
    fn new(tx_event: broadcast::Sender<SolverEvent>) -> Rc<Self> {
        let slv = Rc::new_cyclic(|core| SolverState {
            core: {
                let core: Weak<SolverState> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            smt: RefCell::new(SeMiTONE::new()),
            notified_len: Cell::new(0),
            graph: RefCell::new(Graph::new(tx_event.clone())),
            atom_sigma: RefCell::new(Vec::new()),
            atom_flaw: RefCell::new(Vec::new()),
            tx_event,
        });
        slv
    }

    fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::runtime(format!("Failed to read RiDDle script: {:?}", e)))
    }

    fn solve(&self) -> Result<(), SolverError> {
        info!("Solving problem...");
        loop {
            let prop_result = self.smt.borrow_mut().propagate();
            match prop_result {
                Ok(_) => {
                    let new_literals = self.smt.borrow().get_trail_delta(self.notified_len.get()).to_vec();
                    self.graph.borrow_mut().propagate(&new_literals);
                    self.notified_len.set(self.smt.borrow().current_trail_len());
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::StateUpdate { json: self.to_json() });

                    if !self.graph.borrow().has_estimated_solution() {
                        trace!("Expanding graph...");
                        self.cancel_until(0);
                        let flw_id = self.graph.borrow_mut().pop_flaw().ok_or(SolverError::Inconsistent)?;
                        self.expand_flaw(flw_id)?;
                    } else {
                        trace!("Picking branching literal...");
                        let decision = self.graph.borrow().pick_branching_literal();
                        if let Some(decision_var) = decision {
                            self.graph.borrow_mut().push();
                            self.smt.borrow_mut().decide(decision_var);
                        } else {
                            trace!("No more decisions to make, checking timelines for new flaws...");
                            trace!("No more decisions to make, solution found");
                            break;
                        }
                    }
                }
                Err((bt_level, lemma)) => {
                    let mut smt = self.smt.borrow_mut();
                    let mut graph = self.graph.borrow_mut();
                    if !self.backtrack_and_learn(&mut smt, &mut graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
        Ok(())
    }

    pub fn add_flaw(&self, smt: &mut SeMiTONE, graph: &mut Graph, causes: Vec<ResolverId>, flw: Box<dyn Flaw>) -> Result<FlawId, SolverError> {
        let mut cause_lits: Vec<Lit> = graph.rhos(&causes);
        cause_lits.sort_unstable();
        cause_lits.dedup();

        let phi = match cause_lits.as_slice() {
            [] => Lit::TRUE,
            &[lit] => lit, // ϕ = ρ if there's only one cause
            _ => {
                let phi = smt.new_lit();
                // (ρ₁ ∧ ... ∧ ρₙ) → ϕ (the activation of all causes implies the activation of the flaw)
                let mut clause: Vec<Lit> = cause_lits.iter().map(|&r| !r).collect();
                clause.push(phi);
                self.add_clause(smt, graph, clause)?;
                // ϕ → ρᵢ for each cause ρᵢ (the flaw's activation implies the application of all of its causes)
                for &rho in &cause_lits {
                    self.add_clause(smt, graph, vec![!phi, rho])?;
                }
                phi
            }
        };

        let status = smt.get_lit_val(phi);
        let cost = smt.new_dl_var();

        for &res_id in &causes {
            let rho = graph.rho(res_id);
            let res_cost = graph.resolver_cost_var(res_id);
            // ρ → (cost(ρ) >= cost(ϕ))
            let dl_cnstr = self.track_expr(smt, graph, ast::BoolExpr::DlGe(res_cost, cost, rug::Rational::from(0)))?;
            self.add_clause(smt, graph, vec![!rho, dl_cnstr])?;
        }

        Ok(graph.add_flaw(causes, phi, status, cost, flw))
    }

    pub fn add_resolver(&self, smt: &mut SeMiTONE, graph: &mut Graph, rho: Lit, res: Box<dyn Resolver>) -> Result<ResolverId, SolverError> {
        let (flaw_id, phi) = graph.current_flaw().ok_or(SolverError::runtime("No current flaw when adding resolver"))?;
        // ρ → ϕ (the activation of the resolver implies the activation of the flaw)
        self.add_clause(smt, graph, vec![!rho, phi])?;

        let status = smt.get_lit_val(rho);
        let cost = smt.new_dl_var();

        let parent_cost_var = graph.flaw_cost_var(flaw_id);
        // ρ → (cost(ϕ) >= cost(ρ) + intrinsic_cost(ρ))
        let dl_cnstr = self.track_expr(smt, graph, ast::BoolExpr::DlGe(parent_cost_var, cost, res.intrinsic_cost()))?;
        self.add_clause(smt, graph, vec![!rho, dl_cnstr])?;

        Ok(graph.add_resolver(rho, status, cost, res))
    }

    /// Expands `flw_id`, applies its resolvers, adds the closure clause, and propagates heuristic costs.
    fn expand_flaw(&self, flw_id: FlawId) -> Result<(), SolverError> {
        let phi = self.graph.borrow().phi(flw_id);
        let flaw = self.graph.borrow_mut().take_flaw(flw_id).expect("Flaw should exist in graph");
        flaw.expand(self)?;
        let resolvers = self.graph.borrow().flaw_resolvers(flw_id).to_vec();

        // ϕ → (ρ₁ ∨ ρ₂ ∨ ... ∨ ρₙ) (the activation of the flaw implies the application of at least one of its resolvers)
        let mut clause = Vec::with_capacity(resolvers.len() + 1);
        clause.push(!phi);
        for res_id in resolvers {
            let rho = self.graph.borrow().rho(res_id);
            clause.push(rho);
            let resolver = self.graph.borrow_mut().take_resolver(res_id).expect("Resolver should exist in graph");
            resolver.apply(self)?;
            self.graph.borrow_mut().return_resolver(resolver);
        }

        let mut graph = self.graph.borrow_mut();
        graph.return_flaw(flaw);

        let mut smt = self.smt.borrow_mut();
        self.add_clause(&mut smt, &mut graph, clause)?;

        let current_len = smt.current_trail_len();
        if current_len > self.notified_len.get() {
            graph.propagate(smt.get_trail_delta(self.notified_len.get()));
        }
        self.notified_len.set(current_len);
        graph.propagate_costs(&[flw_id]);

        Ok(())
    }

    fn track_expr(&self, smt: &mut SeMiTONE, graph: &mut Graph, expr: impl AsRef<ast::BoolExpr>) -> Result<Lit, SolverError> {
        loop {
            match smt.track_expr(&expr) {
                Ok(lit) => {
                    return Ok(lit);
                }
                Err((bt_level, lemma)) => {
                    if !self.backtrack_and_learn(smt, graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    fn add_clause(&self, smt: &mut SeMiTONE, graph: &mut Graph, clause: impl IntoIterator<Item = Lit>) -> Result<(), SolverError> {
        let clause: Vec<Lit> = clause.into_iter().collect();
        loop {
            match smt.add_clause(clause.clone()) {
                Ok(()) => {
                    return Ok(());
                }
                Err((bt_level, lemma)) => {
                    if !self.backtrack_and_learn(smt, graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    fn backtrack_and_learn(&self, smt: &mut SeMiTONE, graph: &mut Graph, bt_level: usize, lemma: Vec<Lit>) -> bool {
        if smt.decision_level() == 0 {
            return false;
        }
        let vars_to_undo = smt.cancel_until(bt_level);
        self.notified_len.set(smt.current_trail_len());
        graph.cancel_until(bt_level, &vars_to_undo);
        smt.add_clause(lemma).is_ok()
    }

    fn cancel_until(&self, bt_level: usize) {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let vars_to_undo = smt.cancel_until(bt_level);
        self.notified_len.set(smt.current_trail_len());
        graph.cancel_until(bt_level, &vars_to_undo);
    }

    fn to_json(&self) -> Value {
        let smt = self.smt.borrow();
        let env = to_json(&smt, self);
        let mut objects_map = serde_json::Map::new();
        for object in &self.core.get_objects() {
            let mut obj = json!({
                "class": object.class().full_name(),
                "env": to_json(&smt, object.as_ref()),
            });
            if let Some(name) = self.core.get_object_name(object.id()) {
                obj["name"] = json!(name);
            }
            objects_map.insert(object.id().to_string(), obj);
        }
        let mut atoms_map = serde_json::Map::new();
        for atom in &self.core.get_atoms() {
            atoms_map.insert(
                atom.id().to_string(),
                json!({
                    "predicate": atom.predicate().full_name(),
                    "fact": match atom.kind() {
                        AtomKind::Fact => true,
                        AtomKind::Goal => false,
                    },
                    "env": to_json(&smt, atom.as_ref()),
                }),
            );
        }

        drop(smt);

        json!({
            "env": env,
            "objects": Value::Object(objects_map),
            "atoms": Value::Object(atoms_map),
            "flaws": Vec::<Value>::new(),
            "resolvers": Vec::<Value>::new(),
            "timelines": Vec::<Value>::new(),
        })
    }
}

delegate_scope!(SolverState, core);
delegate_env!(SolverState, core);

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Slot {
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), if value { ast::BoolExpr::True } else { ast::BoolExpr::False })))
    }
    fn new_bool_var(&self) -> Slot {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let var = smt.new_bool();
        let causes = graph.current_causes();
        self.add_flaw(&mut smt, &mut graph, causes, Box::new(BoolFlaw::new(var.clone()))).expect("Failed to add BoolFlaw to graph");
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), var)))
    }
    fn new_int(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), ast::ArithExpr::Const(rug::Rational::from_str(value).expect("Invalid integer literal")))))
    }
    fn new_int_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), self.smt.borrow_mut().new_int())))
    }
    fn new_real(&self, num: &str, den: &str) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), ast::ArithExpr::Const(rug::Rational::from_str(&format!("{}/{}", num, den)).expect("Invalid rational literal")))))
    }
    fn new_real_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), self.smt.borrow_mut().new_real())))
    }
    fn new_string(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), value.into())))
    }
    fn new_string_var(&self) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), String::new())))
    }

    fn sum(&self, sum: &[Slot]) -> Result<Slot, RiddleError> {
        Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_type(self, sum)?, ast::ArithExpr::Add(sum.iter().map(extract_arith).collect::<Result<Vec<_>, _>>()?)))))
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        if let Slot::Primitive(p) = &term {
            if let Some(bool_var) = p.downcast::<BoolVar>() {
                Ok(Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), ast::BoolExpr::Not(Box::new(bool_var.lit.clone()))))))
            } else if let Some(arith_var) = p.downcast::<ArithVar>() {
                Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_var.var_type().clone(), ast::ArithExpr::Neg(Box::new(arith_var.lin.clone()))))))
            } else {
                Err(RiddleError::TypeError(format!("Expected a boolean variable, got {}", term)))
            }
        } else {
            Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", term)))
        }
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_type(self, mul)?, ast::ArithExpr::Mul(mul.iter().map(extract_arith).collect::<Result<Vec<_>, _>>()?)))))
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_type(self, &[left.clone(), right.clone()])?, ast::ArithExpr::Div(Box::new(extract_arith(&left)?), Box::new(extract_arith(&right)?))))))
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();

        let expr = match self.track_expr(&mut smt, &mut graph, expr_to_bool(&term)) {
            Ok(lit) => lit,
            Err(_) => return false,
        };

        if let Some((_c_res, rho)) = graph.current_resolver() {
            if self.add_clause(&mut smt, &mut graph, vec![!rho, expr]).is_err() {
                return false;
            }
        } else if self.add_clause(&mut smt, &mut graph, vec![expr]).is_err() {
            return false;
        }

        let cnf_expr = to_cnf(&term);
        match cnf_expr.as_ref() {
            BoolExpr::And { terms, .. } => {
                for clause in terms {
                    if let BoolExpr::Or { terms, .. } = clause.as_ref()
                        && terms.len() > 1
                    {
                        let causes = graph.current_causes();
                        let terms = terms.iter().map(expr_to_bool).collect::<Vec<_>>();
                        self.add_flaw(&mut smt, &mut graph, causes, Box::new(ClauseFlaw::new(terms))).expect("Failed to add ClauseFlaw to graph");
                    }
                }
            }
            BoolExpr::Or { terms, .. } if terms.len() > 1 => {
                let causes = graph.current_causes();
                let terms = terms.iter().map(expr_to_bool).collect::<Vec<_>>();
                self.add_flaw(&mut smt, &mut graph, causes, Box::new(ClauseFlaw::new(terms))).expect("Failed to add ClauseFlaw to graph");
            }
            _ => {}
        }

        true
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        if instances.is_empty() {
            return Err(RiddleError::InconsistencyError(format!("Cannot create a new variable of type {} with no instances", tp.full_name())));
        }

        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let var = smt.new_enum(instances.iter().map(|&id| *id));
        let causes = graph.current_causes();
        self.add_flaw(&mut smt, &mut graph, causes, Box::new(EnumFlaw::new(var.clone(), instances.to_vec()))).expect("Failed to add EnumFlaw to graph");
        Ok(Slot::Primitive(Rc::new(EnumVar::new(self.slv.clone(), tp, var))))
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let causes = graph.current_causes();
        self.add_flaw(&mut smt, &mut graph, causes, Box::new(DisjunctionFlaw::new(disjunction))).expect("Failed to add DisjunctionFlaw to graph");
    }

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        let obj = self.core.new_object(class.clone());
        trace!("Created new object {} of class {}", obj, class.full_name());
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewObject { obj_id: obj, name: self.core.get_object_name(obj), class: class.full_name() });
        obj
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        self.core.get_object(id)
    }
    fn new_atom(&self, predicate: Rc<Predicate>, kind: AtomKind, args: HashMap<String, Slot>, resolution_constraint: ResolutionConstraint) -> Result<AtomId, RiddleError> {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let atm = self.core.new_atom(predicate.clone(), kind, args, resolution_constraint)?;
        trace!("Created new atom {} with predicate {}", atm, predicate.full_name());
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewAtom {
            atom_id: atm,
            predicate: predicate.full_name(),
            kind,
            args: to_json(&smt, self.core.get_atom(atm).expect("Atom should exist in core").as_ref()),
            resolution_constraint,
        });
        self.atom_sigma.borrow_mut().push(None);
        let causes = graph.current_causes();
        let flaw = self.add_flaw(&mut smt, &mut graph, causes, Box::new(AtomFlaw::new(atm))).expect("Failed to add AtomFlaw to graph");
        self.atom_flaw.borrow_mut().push(flaw);
        Ok(atm)
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

#[derive(Debug)]
pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

impl SolverError {
    fn runtime(msg: impl Into<String>) -> Self {
        Self::RuntimeError(msg.into())
    }
}

impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverError::RuntimeError(msg) => write!(f, "Runtime error: {msg}"),
            SolverError::Inconsistent => write!(f, "Problem is inconsistent"),
        }
    }
}

impl error::Error for SolverError {}

#[derive(Clone)]
pub enum SolverEvent {
    NewObject { obj_id: ObjectId, name: Option<String>, class: String },
    NewAtom { atom_id: AtomId, predicate: String, kind: AtomKind, args: Value, resolution_constraint: ResolutionConstraint },
    NewFlaw { flaw_id: FlawId, phi: String, causes: Vec<ResolverId>, required_by: Vec<ResolverId>, status: Option<bool>, cost: f64, data: Value },
    FlawCostUpdate { flaw_id: FlawId, cost: f64 },
    FlawStatusUpdate { flaw_id: FlawId, status: Option<bool> },
    CurrentFlaw(Option<FlawId>),
    NewResolver { resolver_id: ResolverId, rho: String, flaw_id: FlawId, preconditions: Vec<FlawId>, intrinsic_cost: f64, status: Option<bool>, data: Value },
    ResolverStatusUpdate { resolver_id: ResolverId, status: Option<bool> },
    CurrentResolver(Option<ResolverId>),
    NewCausalLink { flaw_id: FlawId, resolver_id: ResolverId },
    ToSolveFlaw { flaw_id: FlawId },
    SolvedFlaw { flaw_id: FlawId },
    StateUpdate { json: Value },
}

fn bool_expr(p: &Rc<dyn Var>) -> Option<ast::BoolExpr> {
    if let Some(var) = p.downcast::<BoolVar>() { Some(var.lit.clone()) } else { p.downcast::<BoolExpr>().map(expr_to_bool) }
}

fn expr_to_bool(expr: impl AsRef<BoolExpr>) -> ast::BoolExpr {
    match expr.as_ref() {
        BoolExpr::Term { term, .. } => {
            if let Slot::Primitive(var) = term
                && let Some(var) = var.downcast::<BoolVar>()
            {
                return var.lit.clone();
            }
            unreachable!("Expected BoolVar in BoolExpr::Term");
        }
        BoolExpr::Eq { left, right, .. } => eq_to_bool(left, right),
        BoolExpr::Lt { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>())
            {
                return left.lin.lt(&right.lin);
            }
            unreachable!("Expected compatible primitive types in BoolExpr::Lt");
        }
        BoolExpr::Leq { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>())
            {
                return left.lin.le(&right.lin);
            }
            unreachable!("Expected compatible primitive types in BoolExpr::Leq");
        }
        BoolExpr::Or { terms, .. } => ast::BoolExpr::Or(terms.iter().map(expr_to_bool).collect::<Vec<_>>()),
        BoolExpr::And { terms, .. } => ast::BoolExpr::And(terms.iter().map(expr_to_bool).collect::<Vec<_>>()),
        BoolExpr::Not { term, .. } => !expr_to_bool(term),
    }
}

fn eq_to_bool(left: &Slot, right: &Slot) -> ast::BoolExpr {
    match (left, right) {
        (Slot::Primitive(left), Slot::Primitive(right)) => {
            if let (Some(left), Some(right)) = (bool_expr(left), bool_expr(right)) {
                return left.eq(&right);
            } else if let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>()) {
                return left.lin.eq(&right.lin);
            } else if let (Some(left), Some(right)) = (left.downcast::<EnumVar>(), right.downcast::<EnumVar>()) {
                return left.var.eq(&right.var);
            }
        }
        (Slot::Primitive(left), Slot::ObjectRef(right)) => {
            if let Some(left) = left.downcast::<EnumVar>() {
                return left.var.eq(**right);
            }
        }
        (Slot::ObjectRef(left), Slot::Primitive(right)) => {
            if let Some(right) = right.downcast::<EnumVar>() {
                return right.var.eq(**left);
            }
        }
        (Slot::ObjectRef(left), Slot::ObjectRef(right)) => {
            return if left == right { ast::BoolExpr::True } else { ast::BoolExpr::False };
        }
        _ => return ast::BoolExpr::False,
    }
    unreachable!("Expected compatible types in equality");
}

fn extract_arith(slot: &Slot) -> Result<ast::ArithExpr, RiddleError> {
    if let Slot::Primitive(p) = slot {
        if let Some(arith_var) = p.downcast::<ArithVar>() {
            return Ok(arith_var.lin.clone());
        }
    }
    Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", slot)))
}

fn to_json(smt: &SeMiTONE, env: &dyn Env) -> Value {
    let mut env_json = serde_json::Map::new();
    for (name, slot) in env.get_slots() {
        match slot {
            Slot::Primitive(p) => {
                if let Some(bool_expr) = bool_expr(&p) {
                    match smt.get_bool_val(&bool_expr) {
                        Some(val) => {
                            env_json.insert(name, json!(val));
                        }
                        None => {
                            env_json.insert(name, json!({ "type": "bool_var", "lit": bool_expr.to_string() }));
                        }
                    }
                } else if let Some(arith_var) = p.downcast::<ArithVar>() {
                    let value = smt.get_arith_val(&arith_var.lin).expect("Expected an arithmetic variable to have a value");
                    env_json.insert(name, inf_rat_to_json(&value));
                } else if let Some(string_var) = p.downcast::<StringVar>() {
                    env_json.insert(name, json!(string_var.value));
                } else if let Some(enum_var) = p.downcast::<EnumVar>() {
                    if let Some(val) = smt.get_enum_val(&enum_var.var) {
                        env_json.insert(
                            name,
                            json!({
                                "type": "object_ref",
                                "id": format!("obj-{}", val)
                            }),
                        );
                    } else {
                        env_json.insert(
                            name,
                            json!({
                                "type": "enum_var",
                                "var": enum_var.var.to_string()
                            }),
                        );
                    }
                } else {
                    unreachable!("Unexpected primitive type in slot {}", name);
                }
            }
            Slot::ObjectRef(obj_id) => {
                env_json.insert(
                    name,
                    json!({
                        "type": "object_ref",
                        "id": obj_id.to_string()
                    }),
                );
            }
            Slot::AtomRef(atm_id) => {
                env_json.insert(
                    name,
                    json!({
                        "type": "atom_ref",
                        "id": atm_id.to_string()
                    }),
                );
            }
        }
    }
    Value::Object(env_json)
}

pub fn inf_rat_to_json(val: &InfRational) -> Value {
    let mut json = rat_to_json(val.rational_part());
    if !val.infinitesimal_part().is_zero() {
        let inf = val.infinitesimal_part();
        json.as_object_mut().unwrap().insert(
            String::from("inf"),
            json!({
                "num": inf.numer().to_string(),
                "den": inf.denom().to_string()
            }),
        );
    }
    json
}

pub fn rat_to_json(val: &Rational) -> Value {
    match val {
        Rational::Finite(r) => json!({
            "num": r.numer().to_string(),
            "den": r.denom().to_string()
        }),
        Rational::PositiveInf => json!({
            "num": 1,
            "den": 0
        }),
        Rational::NegativeInf => json!({
            "num": -1,
            "den": 0
        }),
    }
}

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

#[derive(Clone)]
pub struct Solver {
    tx_cmd: mpsc::Sender<SolverCommand>,
    pub tx_event: broadcast::Sender<SolverEvent>,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Self {
        let (tx_cmd, mut rx_cmd) = mpsc::channel(100);
        let (tx_event, _) = broadcast::channel(100);
        let tx_event_clone = tx_event.clone();
        tokio::task::spawn_blocking(move || {
            let state = SolverState::new(tx_event_clone);

            while let Some(cmd) = rx_cmd.blocking_recv() {
                match cmd {
                    SolverCommand::ReadRiDDle(riddle, responder) => {
                        let result = state.read(&riddle);
                        let is_err = result.is_err();
                        let _ = responder.send(result);
                        if is_err {
                            break;
                        }
                    }
                    SolverCommand::Solve(responder) => {
                        let result = state.solve();
                        let is_err = result.is_err();
                        let _ = responder.send(result);
                        if is_err {
                            break;
                        }
                    }
                    SolverCommand::ToJson(responder) => {
                        let _ = responder.send(Ok(state.to_json()));
                    }
                }
            }
        });
        Self { tx_cmd, tx_event }
    }

    async fn send_command<T>(&self, make_cmd: impl FnOnce(CommandResult<T>) -> SolverCommand) -> Result<T, SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(make_cmd(reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Solver worker terminated: {e}")))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Solver worker dropped response: {e}")))?
    }

    pub async fn read(&self, riddle: impl Into<String>) -> Result<(), SolverError> {
        let riddle = riddle.into();
        self.send_command(|tx| SolverCommand::ReadRiDDle(riddle, tx)).await
    }

    pub async fn solve(&self) -> Result<(), SolverError> {
        self.send_command(SolverCommand::Solve).await
    }

    pub async fn to_json(&self) -> Result<Value, SolverError> {
        self.send_command(SolverCommand::ToJson).await
    }
}
