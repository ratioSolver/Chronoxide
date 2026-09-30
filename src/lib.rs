use crate::{
    flaws::{atom_flaw::AtomFlaw, bool_flaw::BoolFlaw, clause_flaw::ClauseFlaw, disjunction_flaw::DisjunctionFlaw, enum_flaw::EnumFlaw},
    graph::{Flaw, FlawId, Graph, Resolver, ResolverId},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
    timelines::Timeline,
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, Var, to_cnf},
    language::Disjunction,
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
    rc::{Rc, Weak},
    str::FromStr,
};
use timelines::state_variable::StateVariable;
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};

mod flaws;
mod graph;
mod objects;
mod timelines;

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    timelines: RefCell<Vec<Rc<dyn Timeline>>>,
    smt: RefCell<SeMiTONE>,
    graph: RefCell<Graph>,
    sigma: RefCell<Vec<ast::BoolExpr>>,
    atom_flaw: RefCell<Vec<FlawId>>,
    notified_len: Cell<usize>,
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
            timelines: RefCell::new(Vec::new()),
            smt: RefCell::new(SeMiTONE::new()),
            graph: RefCell::new(Graph::new(tx_event.clone())),
            sigma: RefCell::new(Vec::new()),
            atom_flaw: RefCell::new(Vec::new()),
            notified_len: Cell::new(0),
            tx_event,
        });
        if slv.read(include_str!("init.rddl")).is_err() {
            panic!("Failed to initialize solver");
        }
        slv.add_timeline(StateVariable::new(Rc::downgrade(&slv) as _));
        slv
    }

    pub fn add_timeline(&self, timeline: Rc<dyn Timeline>) {
        self.core.add_type(timeline.clone());
        self.timelines.borrow_mut().push(timeline);
    }

    fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    fn solve(&self) -> Result<(), SolverError> {
        info!("Solving problem...");
        loop {
            let prop_result = self.smt.borrow_mut().propagate();
            match prop_result {
                Ok(_) => {
                    let new_literals = &self.smt.borrow().get_trail_delta(self.notified_len.get()).to_vec();
                    self.graph.borrow_mut().propagate(new_literals.as_slice());
                    self.notified_len.set(self.smt.borrow().current_trail_len());
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::StateUpdate { json: self.to_json() });

                    if !self.graph.borrow().has_estimated_solution() {
                        trace!("Expanding graph...");
                        let (mut flaw, flw_id) = {
                            let mut graph = self.graph.borrow_mut();
                            let flw_id = graph.pop_flaw().ok_or(SolverError::Inconsistent)?;
                            (graph.take_flaw(flw_id).expect("Flaw should exist in graph"), flw_id)
                        };

                        flaw.expand(self)?;
                        let resolvers = flaw.resolvers();

                        // ϕ → (ρ₁ ∨ ρ₂ ∨ ... ∨ ρₙ) (solving the flaw implies applying at least one of its resolvers)
                        let mut clause = Vec::with_capacity(resolvers.len() + 1);
                        clause.push(!self.graph.borrow().phi(flw_id));
                        for res_id in resolvers {
                            clause.push(self.graph.borrow().rho(res_id));
                            let mut resolver = self.graph.borrow_mut().take_resolver(res_id).expect("Resolver should exist in graph");
                            resolver.apply(self)?;
                            self.graph.borrow_mut().return_resolver(resolver);
                        }
                        {
                            let mut smt = self.smt.borrow_mut();
                            let mut graph = self.graph.borrow_mut();
                            self.add_clause(&mut smt, &mut graph, clause)?;
                        }

                        let mut graph = self.graph.borrow_mut();
                        graph.return_flaw(flaw);
                        graph.propagate_costs(&[flw_id]);
                        continue;
                    } else {
                        trace!("Picking branching literal...");
                        let decision = self.graph.borrow().pick_branching_literal();
                        if let Some(decision_var) = decision {
                            self.graph.borrow_mut().push();
                            self.smt.borrow_mut().decide(decision_var);
                        } else {
                            trace!("No more decisions to make, checking timelines for new flaws...");
                            let mut extracted_flaws = Vec::new();
                            for timeline in self.timelines.borrow().iter() {
                                extracted_flaws.extend(timeline.extract_flaws(self)?);
                            }
                            if !extracted_flaws.is_empty() {
                                trace!("Extracted {} new flaws from timelines", extracted_flaws.len());
                                let mut graph = self.graph.borrow_mut();
                                let mut smt = self.smt.borrow_mut();
                                for flaw in extracted_flaws {
                                    self.add_flaw(&mut smt, &mut graph, flaw)?;
                                }
                                if self.notified_len.get() > smt.current_trail_len() {
                                    let new_literals = &smt.get_trail_delta(self.notified_len.get()).to_vec();
                                    graph.propagate(new_literals.as_slice());
                                    self.notified_len.set(smt.current_trail_len());
                                }
                                continue;
                            }

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

    /// Backtracks `smt` and `graph` to `bt_level` and learns `lemma`.
    /// Returns `false` if the conflict is at the root level and cannot be recovered from.
    fn backtrack_and_learn(&self, smt: &mut SeMiTONE, graph: &mut Graph, bt_level: usize, lemma: Vec<Lit>) -> bool {
        if smt.decision_level() == 0 {
            return false;
        }
        let vars_to_undo = smt.cancel_until(bt_level);
        self.notified_len.set(smt.current_trail_len());
        graph.cancel_until(bt_level, vars_to_undo.as_slice());
        smt.add_clause(lemma).is_ok()
    }

    /// Notifies `graph` of any SAT literals assigned since the last sync (e.g. forced by a clause
    /// just added), keeping its flaw/resolver status and agenda consistent with `smt`'s trail.
    /// A no-op while a flaw/resolver is checked out (`graph.is_busy()`): the sync is deferred to the
    /// next safe point, i.e. the top of the solve loop.
    fn sync_graph(&self, smt: &SeMiTONE, graph: &mut Graph) {
        if graph.is_busy() {
            return;
        }
        let current_len = smt.current_trail_len();
        if current_len > self.notified_len.get() {
            let new_literals = smt.get_trail_delta(self.notified_len.get()).to_vec();
            graph.propagate(new_literals.as_slice());
        }
        self.notified_len.set(current_len);
    }

    /// Tracks `expr` as a SAT literal. Each time the encoding conflicts, backtracks, learns the
    /// conflict clause and retries: after backtracking to `bt_level`, re-encoding always succeeds
    /// unless the conflict is at the root level, in which case the problem is truly inconsistent.
    pub fn track_expr(&self, smt: &mut SeMiTONE, graph: &mut Graph, expr: impl AsRef<ast::BoolExpr>) -> Result<Lit, SolverError> {
        loop {
            match smt.track_expr(expr.as_ref()) {
                Ok(lit) => {
                    self.sync_graph(smt, graph);
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

    /// Adds `clause` to the SAT core, retrying after backtrack-and-learn on conflict (see `track_expr`).
    pub fn add_clause(&self, smt: &mut SeMiTONE, graph: &mut Graph, clause: impl IntoIterator<Item = Lit>) -> Result<(), SolverError> {
        let clause: Vec<Lit> = clause.into_iter().collect();
        loop {
            match smt.add_clause(clause.clone()) {
                Ok(()) => {
                    self.sync_graph(smt, graph);
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

    /// Registers a new flaw: allocates its ϕ literal (and the causes → ϕ clause) in `smt`, then
    /// delegates bookkeeping to `graph`. This is the only place where a flaw's SAT encoding is created.
    pub fn add_flaw(&self, smt: &mut SeMiTONE, graph: &mut Graph, flw: Box<dyn Flaw>) -> Result<FlawId, SolverError> {
        let causes = flw.causes();
        let phi = if causes.is_empty() {
            Lit::TRUE
        } else {
            let phi = smt.new_lit();
            // (ρ₁ ∧ ρ₂ ∧ ... ∧ ρₙ) → ϕ (the flaw is active if all its causes are active)
            let mut clause: Vec<Lit> = graph.resolver_rhos(&causes).into_iter().map(|r| !r).collect();
            clause.push(phi);
            self.add_clause(smt, graph, clause)?;
            phi
        };
        let status = smt.get_lit_val(phi);
        let cost = smt.new_dl_var();
        Ok(graph.add_flaw(flw, phi, status, cost))
    }

    /// Registers a new resolver: adds its ρ → ϕ implication and DL cost constraint to `smt`, then
    /// delegates bookkeeping to `graph`.
    pub fn add_resolver(&self, smt: &mut SeMiTONE, graph: &mut Graph, res: Box<dyn Resolver>, rho: Lit) -> Result<ResolverId, SolverError> {
        assert!(smt.get_lit_val(rho) != Some(false), "Cannot add resolver with a false ρ");

        let flaw_id = res.flaw();
        let phi = graph.phi(flaw_id);
        // ρ → ϕ (applying the resolver implies solving the flaw)
        self.add_clause(smt, graph, vec![!rho, phi])?;

        let cost = smt.new_dl_var();
        let parent_cost_var = graph.flaw_cost(flaw_id);
        let dl_cnstr = self.track_expr(smt, graph, ast::BoolExpr::DlGe(parent_cost_var, cost, res.intrinsic_cost()))?;
        self.add_clause(smt, graph, vec![!rho, dl_cnstr])?;

        let status = smt.get_lit_val(rho);
        Ok(graph.add_resolver(res, rho, status, cost))
    }

    /// Adds a causal link from the current resolver to `flw_id`, wiring the ρ → ϕ clause into `smt`.
    pub(crate) fn add_causal_link(&self, smt: &mut SeMiTONE, graph: &mut Graph, flw_id: FlawId) -> Result<(), SolverError> {
        let (rho, phi) = graph.add_causal_link(flw_id)?;
        self.add_clause(smt, graph, vec![!rho, phi])
    }

    fn to_json(&self) -> Value {
        let smt = self.smt.borrow();
        let env = to_json(&smt, self);
        let mut objects_map = serde_json::Map::new();
        for object in &self.core.get_objects() {
            objects_map.insert(object.id().to_string(), to_json(&smt, object.as_ref()));
        }
        let mut atoms_map = serde_json::Map::new();
        for atom in &self.core.get_atoms() {
            atoms_map.insert(atom.id().to_string(), to_json(&smt, atom.as_ref()));
        }

        drop(smt);

        let mut timelines_map = serde_json::Map::new();
        for timeline in self.timelines.borrow().iter() {
            let timeline_json = timeline.to_json(self);
            if let Value::Object(map) = timeline_json {
                timelines_map.extend(map);
            }
        }

        json!({
            "env": env,
            "objects": Value::Object(objects_map),
            "atoms": Value::Object(atoms_map),
            "flaws": Vec::<Value>::new(),
            "resolvers": Vec::<Value>::new(),
            "timelines": Value::Object(timelines_map),
        })
    }
}

impl Scope for SolverState {
    fn core(&self) -> Rc<dyn Core> {
        self.slv.upgrade().expect("SolverState should never be dropped while in use")
    }
    fn scope(&self) -> Option<Rc<dyn Scope>> {
        None
    }

    fn get_fields(&self) -> Vec<Rc<Field>> {
        self.core.get_fields()
    }
    fn get_field(&self, name: &str) -> Option<Rc<Field>> {
        self.core.get_field(name)
    }
    fn get_function(&self, name: &str, types: &[Rc<dyn Type>]) -> Option<Rc<Function>> {
        self.core.get_function(name, types)
    }
    fn get_type(&self, name: &str) -> Option<Rc<dyn Type>> {
        self.core.get_type(name)
    }
    fn get_predicate(&self, name: &str) -> Option<Rc<Predicate>> {
        self.core.get_predicate(name)
    }
}

impl Env for SolverState {
    fn parent(&self) -> Option<Rc<dyn Env>> {
        None
    }

    fn get_slots(&self) -> HashMap<String, Slot> {
        self.core.get_slots()
    }

    fn get(&self, name: &str) -> Option<Slot> {
        self.core.get(name)
    }

    fn set(&self, name: String, value: Slot) {
        self.core.set(name, value);
    }
}

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Slot {
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), if value { ast::BoolExpr::True } else { ast::BoolExpr::False })))
    }
    fn new_bool_var(&self) -> Slot {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let var = smt.new_bool();
        let cause = graph.current_resolver().map(|(res_id, _)| res_id);
        self.add_flaw(&mut smt, &mut graph, Box::new(BoolFlaw::new(cause, var.clone()))).expect("Failed to add BoolFlaw to graph");
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
        let tp = arith_type(self, sum)?;
        let sum = sum
            .iter()
            .map(|s| match s {
                Slot::Primitive(p) => {
                    if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                        Ok(arith_var.lin.clone())
                    } else {
                        Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", s)))
                    }
                }
                _ => Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", s))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Add(sum)))))
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        if let Slot::Primitive(p) = &term {
            if let Some(bool_var) = p.clone().as_any().downcast_ref::<BoolVar>() {
                Ok(Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), ast::BoolExpr::Not(Box::new(bool_var.lit.clone()))))))
            } else if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_var.var_type().clone(), ast::ArithExpr::Neg(Box::new(arith_var.lin.clone()))))))
            } else {
                Err(RiddleError::TypeError(format!("Expected a boolean variable, got {}", term)))
            }
        } else {
            Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", term)))
        }
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        let tp = arith_type(self, mul)?;
        let mul = mul
            .iter()
            .map(|s| match s {
                Slot::Primitive(p) => {
                    if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                        Ok(arith_var.lin.clone())
                    } else {
                        Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", s)))
                    }
                }
                _ => Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", s))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Mul(mul)))))
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        let tp = arith_type(self, &[left.clone(), right.clone()])?;
        let left_lin = if let Slot::Primitive(p) = &left {
            if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                arith_var.lin.clone()
            } else {
                return Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", left)));
            }
        } else {
            return Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", left)));
        };
        let right_lin = if let Slot::Primitive(p) = &right {
            if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                arith_var.lin.clone()
            } else {
                return Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", right)));
            }
        } else {
            return Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", right)));
        };
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Div(Box::new(left_lin), Box::new(right_lin))))))
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();

        let expr = match self.track_expr(&mut smt, &mut graph, expr_to_bool(term.as_ref())) {
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

        let cnf_expr = to_cnf(term.clone());
        match cnf_expr.as_ref() {
            BoolExpr::And { terms, .. } => {
                for clause in terms {
                    if let BoolExpr::Or { terms, .. } = clause.as_ref()
                        && terms.len() > 1
                    {
                        let cause = graph.current_resolver().map(|(res_id, _)| res_id);
                        let terms = terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>();
                        self.add_flaw(&mut smt, &mut graph, Box::new(ClauseFlaw::new(cause, terms))).expect("Failed to add ClauseFlaw to graph");
                    }
                }
            }
            BoolExpr::Or { terms, .. } if terms.len() > 1 => {
                let cause = graph.current_resolver().map(|(res_id, _)| res_id);
                let terms = terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>();
                self.add_flaw(&mut smt, &mut graph, Box::new(ClauseFlaw::new(cause, terms))).expect("Failed to add ClauseFlaw to graph");
            }
            _ => {}
        }

        true
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let domain = instances.iter().map(|id| **id as i32).collect::<Vec<_>>();
        let var = smt.new_enum(domain.clone());
        let cause = graph.current_resolver().map(|(res_id, _)| res_id);
        self.add_flaw(&mut smt, &mut graph, Box::new(EnumFlaw::new(cause, var.clone(), domain))).expect("Failed to add EnumFlaw to graph");
        Ok(Slot::Primitive(Rc::new(EnumVar::new(tp, var))))
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let cause = graph.current_resolver().map(|(res_id, _)| res_id);
        self.add_flaw(&mut smt, &mut graph, Box::new(DisjunctionFlaw::new(cause, disjunction))).expect("Failed to add DisjunctionFlaw to graph");
    }

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        self.core.new_object(class)
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        self.core.get_object(id)
    }
    fn new_atom(&self, predicate: Rc<Predicate>, fact: bool, args: HashMap<String, Slot>) -> AtomId {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let atm = self.core.new_atom(predicate.clone(), fact, args);
        trace!("Created new atom {} with predicate {}", atm, predicate.full_name());
        self.sigma.borrow_mut().push(smt.new_bool());
        let cause = graph.current_resolver().map(|(res_id, _)| res_id);
        let flaw = self.add_flaw(&mut smt, &mut graph, Box::new(AtomFlaw::new(cause, atm))).expect("Failed to add AtomFlaw to graph");
        self.atom_flaw.borrow_mut().push(flaw);
        atm
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

fn expr_to_bool(expr: &BoolExpr) -> ast::BoolExpr {
    match expr {
        BoolExpr::Term { term, .. } => {
            if let Slot::Primitive(var) = term
                && let Some(var) = var.clone().as_any().downcast_ref::<BoolVar>()
            {
                return var.lit.clone();
            }
            unreachable!("Expected BoolVar in BoolExpr::Term");
        }
        BoolExpr::Eq { left, right, .. } => eq_to_bool(left, right),
        BoolExpr::Lt { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<ArithVar>(), right.clone().as_any().downcast_ref::<ArithVar>())
            {
                return left.lin.lt(&right.lin);
            }
            unreachable!("Expected compatible primitive types in BoolExpr::Lt");
        }
        BoolExpr::Leq { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<ArithVar>(), right.clone().as_any().downcast_ref::<ArithVar>())
            {
                return left.lin.le(&right.lin);
            }
            unreachable!("Expected compatible primitive types in BoolExpr::Leq");
        }
        BoolExpr::Or { terms, .. } => ast::BoolExpr::Or(terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::And { terms, .. } => ast::BoolExpr::And(terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::Not { term, .. } => !expr_to_bool(term),
    }
}

fn eq_to_bool(left: &Slot, right: &Slot) -> ast::BoolExpr {
    match (left, right) {
        (Slot::Primitive(left), Slot::Primitive(right)) => {
            if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<BoolVar>(), right.clone().as_any().downcast_ref::<BoolVar>()) {
                return left.lit.eq(&right.lit);
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<ArithVar>(), right.clone().as_any().downcast_ref::<ArithVar>()) {
                return left.lin.eq(&right.lin);
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<EnumVar>(), right.clone().as_any().downcast_ref::<EnumVar>()) {
                return left.var.eq(&right.var);
            }
        }
        (Slot::Primitive(left), Slot::ObjectRef(right)) => {
            if let Some(left) = left.clone().as_any().downcast_ref::<EnumVar>() {
                return left.var.eq(**right as i32);
            }
        }
        (Slot::ObjectRef(left), Slot::Primitive(right)) => {
            if let Some(right) = right.clone().as_any().downcast_ref::<EnumVar>() {
                return right.var.eq(**left as i32);
            }
        }
        _ => {
            unreachable!("Expected compatible types in equality");
        }
    }
    unreachable!("Expected compatible types in equality");
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

    pub async fn read(&self, riddle: String) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ReadRiDDle(riddle, reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send ReadRiDDle command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive ReadRiDDle response: {:?}", e)))?
    }

    pub async fn solve(&self) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::Solve(reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send Solve command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive Solve response: {:?}", e)))?
    }

    pub async fn to_json(&self) -> Result<Value, SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ToJson(reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send ToJson command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive ToJson response: {:?}", e)))?
    }
}

fn to_json(smt: &SeMiTONE, env: &dyn Env) -> Value {
    let mut env_json = serde_json::Map::new();
    for (name, slot) in env.get_slots() {
        match slot {
            Slot::Primitive(p) => {
                if let Some(bool_var) = p.clone().as_any().downcast_ref::<BoolVar>() {
                    match smt.get_bool_val(&bool_var.lit) {
                        Some(true) => {
                            env_json.insert(name, json!(true));
                        }
                        Some(false) => {
                            env_json.insert(name, json!(false));
                        }
                        None => {
                            env_json.insert(name, serde_json::Value::Null);
                        }
                    }
                } else if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                    let value = smt.get_arith_val(&arith_var.lin).expect("Expected an arithmetic variable to have a value");
                    env_json.insert(name, inf_rat_to_json(&value));
                } else if let Some(string_var) = p.clone().as_any().downcast_ref::<StringVar>() {
                    env_json.insert(name, json!(string_var.value));
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
            "inf".to_string(),
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

#[derive(Debug)]
pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

#[derive(Clone)]
pub enum SolverEvent {
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
