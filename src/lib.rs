mod flaws;
mod graph;
mod objects;

use crate::{
    flaws::{atom_flw::AtomFlaw, bool_flw::BoolFlaw, clause_flw::ClauseFlaw, enum_flw::EnumFlaw},
    graph::{Flaw, FlawId, Graph, ResolverId},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, to_cnf},
    language::Disjunction,
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use semitone::{Lit, SeMiTONE, ast};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::{Rc, Weak},
    str::FromStr,
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    smt: RefCell<SeMiTONE>,
    planner_state: RefCell<PlannerState>,
    tx_event: broadcast::Sender<SolverEvent>,
}

struct PlannerState {
    graph: Graph,
    agenda: HashSet<FlawId>,
    atom_sigma: Vec<usize>,
    notified_len: usize,
}

impl SolverState {
    fn new(tx_event: broadcast::Sender<SolverEvent>) -> Rc<Self> {
        Rc::new_cyclic(|core| SolverState {
            core: {
                let core: Weak<SolverState> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            smt: RefCell::new(SeMiTONE::new()),
            planner_state: RefCell::new(PlannerState {
                graph: Graph::new(tx_event.clone()),
                agenda: HashSet::new(),
                atom_sigma: Vec::new(),
                notified_len: 0,
            }),
            tx_event,
        })
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
                Ok(()) => {
                    self.sync_agenda();
                    self.build_graph()?;

                    if let Some(flaw_id) = self.select_flaw() {
                        trace!("Deciding on flaw {}", flaw_id);
                        let resolver_id = self.select_resolver(flaw_id)?;
                        trace!("Applying resolver {}", resolver_id);
                        let rho = {
                            let planner = self.planner_state.borrow();
                            planner.graph.get_resolver(resolver_id).rho()
                        };
                        trace!("Deciding on literal {}", rho);
                        self.smt.borrow_mut().decide(rho);
                    } else {
                        let check_result = self.smt.borrow_mut().check_ints();
                        match check_result {
                            Ok(()) => {
                                info!("Problem solved successfully");
                                return Ok(());
                            }
                            Err((bt_level, lemma)) => {
                                if self.smt.borrow().decision_level() == 0 {
                                    return Err(SolverError::Inconsistent);
                                }
                                self.cancel_until(bt_level);
                                if self.smt.borrow_mut().add_clause(lemma).is_err() {
                                    return Err(SolverError::Inconsistent);
                                }
                            }
                        }
                    }
                }
                Err((bt_level, lemma)) => {
                    if self.smt.borrow().decision_level() == 0 {
                        return Err(SolverError::Inconsistent);
                    }
                    self.cancel_until(bt_level);
                    if self.smt.borrow_mut().add_clause(lemma).is_err() {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    fn select_flaw(&self) -> Option<FlawId> {
        let planner = self.planner_state.borrow();
        planner.agenda.iter().copied().max_by(|&a, &b| {
            let cost_a = planner.graph.get_flaw(a).estimated_cost();
            let cost_b = planner.graph.get_flaw(b).estimated_cost();
            cost_a.partial_cmp(&cost_b).unwrap_or(std::cmp::Ordering::Equal)
        })
    }

    fn select_resolver(&self, flaw_id: FlawId) -> Result<ResolverId, SolverError> {
        let planner = self.planner_state.borrow();
        let flaw = planner.graph.get_flaw(flaw_id);
        let best_resolver = flaw.resolvers().iter().copied().filter(|&res_id| planner.graph.get_resolver(res_id).status() != Some(false)).min_by(|&a, &b| {
            let cost_a = planner.graph.get_resolver_estimated_cost(a);
            let cost_b = planner.graph.get_resolver_estimated_cost(b);
            cost_a.partial_cmp(&cost_b).unwrap_or(std::cmp::Ordering::Equal)
        });

        best_resolver.ok_or(SolverError::Inconsistent)
    }

    pub fn add_flaw(&self, flaw: Box<dyn Flaw>) {
        let status = flaw.status();
        let atom_id = flaw.atom_id();
        let mut planner = self.planner_state.borrow_mut();

        let flaw_id = planner.graph.add_flaw(flaw);
        if let Some(atom_id) = atom_id {
            planner.graph.atom_to_flaw.insert(atom_id, flaw_id);
        }
        if status == Some(true) {
            planner.agenda.insert(flaw_id);
        }
    }

    pub(crate) fn add_causal_link(&self, unif_resolver_id: ResolverId, target_atom_id: AtomId) -> Result<(), SolverError> {
        let mut planner = self.planner_state.borrow_mut();

        let target_flaw_id = *planner.graph.atom_to_flaw.get(&target_atom_id).ok_or_else(|| SolverError::RuntimeError(format!("Atom ID {} has no corresponding Flaw", target_atom_id)))?;

        let target_flaw = planner.graph.get_flaw_mut(target_flaw_id);
        target_flaw.add_support(unif_resolver_id);

        trace!("Causal link created: Resolver {} supports Flaw {}", unif_resolver_id, target_flaw_id);
        let _ = self.tx_event.send(SolverEvent::NewCausalLink { flaw_id: target_flaw_id, resolver_id: unif_resolver_id });
        Ok(())
    }

    fn sync_agenda(&self) {
        let mut planner = self.planner_state.borrow_mut();
        let smt = self.smt.borrow();

        let current_trail_len = smt.current_trail_len();
        if planner.notified_len == current_trail_len {
            return;
        }

        let new_literals = smt.get_trail_delta(planner.notified_len);

        for lit in new_literals {
            let var_id = lit.var();

            if let Some(flaw_ids) = planner.graph.lit_to_flaw.get(&var_id).cloned() {
                for flaw_id in flaw_ids {
                    let status = smt.get_lit_val(planner.graph.get_flaw(flaw_id).phi());
                    planner.graph.set_flaw_status(flaw_id, status);

                    if status == Some(true) {
                        planner.agenda.insert(flaw_id);
                    }
                }
            }

            if let Some(resolver_ids) = planner.graph.lit_to_resolver.get(&var_id).cloned() {
                for resolver_id in resolver_ids {
                    let (status, flaw_id) = {
                        let resolver = planner.graph.get_resolver(resolver_id);
                        (smt.get_lit_val(resolver.rho()), resolver.flaw())
                    };

                    trace!("Updating status for resolver {} to {:?} (flaw {})", resolver_id, status, flaw_id);
                    planner.graph.set_resolver_status(resolver_id, status);

                    if status == Some(true) {
                        planner.agenda.remove(&flaw_id);
                    }
                }
            }
        }

        planner.notified_len = current_trail_len;
    }

    fn cancel_until(&self, level: usize) {
        let vars_to_undo: Vec<usize> = {
            let smt = self.smt.borrow();
            let target_trail_len = smt.get_trail_len_at_level(level);
            let current_trail_len = smt.current_trail_len();

            smt.get_trail_slice(target_trail_len, current_trail_len).iter().map(|lit| lit.var()).collect()
        };
        self.smt.borrow_mut().cancel_until(level);

        let mut planner = self.planner_state.borrow_mut();
        let smt = self.smt.borrow();

        for var_id in vars_to_undo.into_iter().rev() {
            if let Some(flaw_ids) = planner.graph.lit_to_flaw.get(&var_id).cloned() {
                for flaw_id in flaw_ids {
                    let status = smt.get_lit_val(planner.graph.get_flaw(flaw_id).phi());
                    planner.graph.set_flaw_status(flaw_id, status);

                    if status != Some(true) {
                        planner.agenda.remove(&flaw_id);
                    }
                }
            }

            if let Some(resolver_ids) = planner.graph.lit_to_resolver.get(&var_id).cloned() {
                for resolver_id in resolver_ids {
                    let (status, flaw_id) = {
                        let resolver = planner.graph.get_resolver(resolver_id);
                        (smt.get_lit_val(resolver.rho()), resolver.flaw())
                    };

                    planner.graph.set_resolver_status(resolver_id, status);

                    if status != Some(true) && planner.graph.get_flaw(flaw_id).status() == Some(true) {
                        planner.agenda.insert(flaw_id);
                    }
                }
            }
        }

        planner.notified_len = smt.current_trail_len();
    }

    fn build_graph(&self) -> Result<(), SolverError> {
        info!("Building graph...");
        loop {
            {
                let planner = self.planner_state.borrow();
                if !planner.agenda.iter().any(|&flaw_id| planner.graph.get_flaw(flaw_id).estimated_cost() == f64::INFINITY) {
                    trace!("All flaws have finite estimated costs, graph building complete");
                    return Ok(());
                }
            }

            let next_flaw_id = self.planner_state.borrow_mut().graph.flaw_q.pop_front();
            if let Some(flaw_id) = next_flaw_id {
                let mut flaw = {
                    let mut planner = self.planner_state.borrow_mut();
                    planner.graph.set_current_flaw(Some(flaw_id));
                    let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flaw_id)));
                    planner.graph.take_flaw(flaw_id)
                };
                assert!(!flaw.is_expanded());
                let mut or_args = Vec::with_capacity(flaw.causes().len() + 1);
                for cause_id in flaw.causes() {
                    or_args.push(!self.planner_state.borrow().graph.get_resolver(*cause_id).rho());
                }
                or_args.push(flaw.phi());
                if self.smt.borrow_mut().add_clause(or_args).is_err() {
                    return Err(SolverError::Inconsistent);
                }

                let resolvers = flaw.expand(self)?;
                let mut or_args = Vec::with_capacity(resolvers.len() + 1);
                for resolver in &resolvers {
                    let rho = resolver.rho();
                    if self.smt.borrow().get_lit_val(rho) == Some(true) {
                        self.planner_state.borrow_mut().agenda.remove(&flaw_id);
                    }
                    or_args.push(rho);
                    if self.smt.borrow_mut().add_clause([!rho, flaw.phi()]).is_err() {
                        return Err(SolverError::Inconsistent);
                    }
                }
                or_args.push(!flaw.phi());
                if self.smt.borrow_mut().add_clause(or_args).is_err() {
                    return Err(SolverError::Inconsistent);
                }

                let flaw_id = flaw.id();
                for resolver in resolvers {
                    let mut resolver = {
                        let mut planner = self.planner_state.borrow_mut();
                        let resolver_id = planner.graph.add_resolver(resolver);
                        flaw.add_resolver(resolver_id);
                        planner.graph.set_current_resolver(Some(resolver_id));
                        let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(resolver_id)));
                        planner.graph.take_resolver(resolver_id)
                    };
                    resolver.apply(self)?;
                    {
                        let mut planner = self.planner_state.borrow_mut();
                        planner.graph.return_resolver(resolver.id(), resolver);
                        planner.graph.set_current_resolver(None);
                        let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
                    }
                }
                {
                    let mut planner = self.planner_state.borrow_mut();
                    planner.graph.return_flaw(flaw_id, flaw);
                    planner.graph.set_current_flaw(None);
                    let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
                }

                self.smt.borrow_mut().propagate().map_err(|_| SolverError::Inconsistent)?;
                self.sync_agenda();
                self.planner_state.borrow_mut().graph.propagate_costs(vec![flaw_id], |expr| self.smt.borrow().get_lit_val(expr) != Some(false));
            } else {
                return Err(SolverError::Inconsistent);
            }
        }
    }

    fn to_json(&self) -> Value {
        json!({"flaws": [], "resolvers": []})
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
        let var = self.smt.borrow_mut().new_bool();
        let (phi, c_res, status) = if let Some(c_res) = self.planner_state.borrow().graph.get_current_resolver() { (c_res.rho(), Some(c_res.id()), self.smt.borrow().get_lit_val(c_res.rho())) } else { (Lit::TRUE, None, Some(true)) };
        self.add_flaw(Box::new(BoolFlaw::new(phi, status, c_res, var.clone())));
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
        let (phi, c_res, status) = if let Some(c_res) = self.planner_state.borrow().graph.get_current_resolver() { (c_res.rho(), Some(c_res.id()), self.smt.borrow().get_lit_val(c_res.rho())) } else { (Lit::TRUE, None, Some(true)) };
        if !self.smt.borrow_mut().assert(&ast::BoolExpr::Or(vec![if phi.sign() { !ast::BoolExpr::Var(phi.var()) } else { ast::BoolExpr::Var(phi.var()) }, expr_to_bool(&term)])) {
            return false;
        }
        let cnf_expr = to_cnf(term.clone());
        if let BoolExpr::And { terms, .. } = cnf_expr.as_ref() {
            for clause in terms {
                if let BoolExpr::Or { terms, .. } = clause.as_ref()
                    && terms.len() > 1
                {
                    let terms = terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>();
                    self.add_flaw(Box::new(ClauseFlaw::new(phi, status, c_res, terms)));
                }
            }
        } else {
            if let BoolExpr::Or { terms, .. } = cnf_expr.as_ref()
                && terms.len() > 1
            {
                let terms = terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>();
                self.add_flaw(Box::new(ClauseFlaw::new(phi, status, c_res, terms)));
            }
        }
        true
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let domain = instances.iter().map(|id| **id as i32).collect::<Vec<_>>();
        let var = self.smt.borrow_mut().new_enum(domain.clone());
        let (phi, c_res, status) = if let Some(c_res) = self.planner_state.borrow().graph.get_current_resolver() { (c_res.rho(), Some(c_res.id()), self.smt.borrow().get_lit_val(c_res.rho())) } else { (Lit::TRUE, None, Some(true)) };
        self.add_flaw(Box::new(EnumFlaw::new(phi, status, c_res, var.clone(), domain)));
        Ok(Slot::Primitive(Rc::new(EnumVar::new(tp, var))))
    }
    fn new_disjunction(&self, _disjunction: Disjunction) {}

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        self.core.new_object(class)
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        self.core.get_object(id)
    }
    fn new_atom(&self, predicate: Rc<Predicate>, fact: bool, args: HashMap<String, Slot>) -> AtomId {
        let atm = self.core.new_atom(predicate, fact, args);
        let ast::BoolExpr::Var(sigma) = self.smt.borrow_mut().new_bool() else {
            unreachable!("Expected a BoolExpr::Var for atom sigma");
        };
        self.planner_state.borrow_mut().atom_sigma.push(sigma);
        let (phi, c_res) = if let Some(c_res) = self.planner_state.borrow().graph.get_current_resolver() { (c_res.rho(), Some(c_res.id())) } else { (Lit::TRUE, None) };
        let status = self.smt.borrow().get_lit_val(phi);
        self.add_flaw(Box::new(AtomFlaw::new(phi, status, c_res, self.get_atom(atm).expect("Atom should exist").clone())));
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
pub enum SolverEvent {
    NewFlaw { flaw_id: FlawId, phi: String, causes: Vec<ResolverId>, supports: Vec<ResolverId>, status: Option<bool>, cost: f64, data: Value },
    FlawCostUpdate { flaw_id: FlawId, cost: f64 },
    FlawStatusUpdate { flaw_id: FlawId, status: Option<bool> },
    CurrentFlaw(Option<FlawId>),
    NewResolver { resolver_id: ResolverId, rho: String, flaw_id: FlawId, sub_flaws: Vec<FlawId>, intrinsic_cost: f64, status: Option<bool>, data: Value },
    ResolverStatusUpdate { resolver_id: ResolverId, status: Option<bool> },
    CurrentResolver(Option<ResolverId>),
    NewCausalLink { flaw_id: FlawId, resolver_id: ResolverId },
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
                    SolverCommand::ReadRiDDle(riddle, responder) => match state.read(&riddle) {
                        Ok(_) => {
                            let _ = responder.send(Ok(()));
                        }
                        Err(e) => {
                            let _ = responder.send(Err(e));
                        }
                    },
                    SolverCommand::Solve(responder) => match state.solve() {
                        Ok(_) => {
                            let _ = responder.send(Ok(()));
                        }
                        Err(e) => {
                            let _ = responder.send(Err(e));
                        }
                    },
                    SolverCommand::ToJson(responder) => {
                        let json = state.to_json();
                        let _ = responder.send(Ok(json));
                    }
                }
            }
        });
        Self { tx_cmd, tx_event }
    }

    pub async fn read(&self, riddle: String) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ReadRiDDle(riddle, reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }

    pub async fn solve(&self) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::Solve(reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }

    pub async fn to_json(&self) -> Result<Value, SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ToJson(reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use semitone::ast;
    use tokio::sync::broadcast;

    fn setup_test_state() -> Rc<SolverState> {
        let (tx, _) = broadcast::channel(100);
        SolverState::new(tx)
    }

    #[test]
    fn test_solver_initialization() {
        let state = setup_test_state();

        assert!(state.planner_state.borrow().agenda.is_empty());
        assert_eq!(state.smt.borrow().current_trail_len(), 1); // The initial trail length should be 1 due to the initial true literal.
    }

    #[test]
    fn test_eq_to_bool_primitives() {
        let state = setup_test_state();

        let bool_true = state.new_bool(true);
        let bool_false = state.new_bool(false);

        let eq_expr = eq_to_bool(&bool_true, &bool_false);
        assert!(matches!(eq_expr, ast::BoolExpr::Eq(_, _)));
    }

    #[test]
    #[should_panic(expected = "Expected compatible types in equality")]
    fn test_eq_to_bool_incompatible_types_panic() {
        let state = setup_test_state();

        let bool_var = state.new_bool(true);
        let int_var = state.new_int("42");

        let _ = eq_to_bool(&bool_var, &int_var);
    }

    #[test]
    fn test_core_new_bool_var_generates_flaw() {
        let state = setup_test_state();

        let initial_q_len = state.planner_state.borrow().graph.flaw_q.len();
        assert_eq!(initial_q_len, 0, "Initial flaw queue should be empty");

        let bool_slot = state.new_bool_var();

        assert!(matches!(bool_slot, Slot::Primitive(_)));

        let final_q_len = state.planner_state.borrow().graph.flaw_q.len();
        assert_eq!(final_q_len, 1, "Flaw queue should have one flaw after creating a new bool var");
    }

    #[test]
    fn test_core_assert_disjunction_generates_clause_flaw() {
        let state = setup_test_state();

        let slot_a = state.new_bool_var();
        let slot_b = state.new_bool_var();

        let initial_q_len = state.planner_state.borrow().graph.flaw_q.len();
        assert_eq!(initial_q_len, 2);

        let expr_a = Rc::new(BoolExpr::Term { var_type: Rc::downgrade(&state.bool_type()), term: slot_a });
        let expr_b = Rc::new(BoolExpr::Term { var_type: Rc::downgrade(&state.bool_type()), term: slot_b });

        let disjunction = Rc::new(BoolExpr::Or { var_type: Rc::downgrade(&state.bool_type()), terms: vec![expr_a, expr_b] });

        let success = state.assert(disjunction);
        assert!(success, "Assertion of a disjunction should succeed");

        let final_q_len = state.planner_state.borrow().graph.flaw_q.len();
        assert_eq!(final_q_len, 3, "Assertion of a disjunction should generate a ClauseFlaw");
    }

    #[test]
    fn test_core_assert_conjunction_skips_clause_flaw() {
        let state = setup_test_state();
        let slot_a = state.new_bool_var();

        let initial_q_len = state.planner_state.borrow().graph.flaw_q.len();

        let expr_a = Rc::new(BoolExpr::Term { var_type: Rc::downgrade(&state.bool_type()), term: slot_a });

        let conjunction = Rc::new(BoolExpr::And { var_type: Rc::downgrade(&state.bool_type()), terms: vec![expr_a] });

        let success = state.assert(conjunction);
        assert!(success);

        let final_q_len = state.planner_state.borrow().graph.flaw_q.len();
        assert_eq!(final_q_len, initial_q_len, "Conjunctions should not generate ClauseFlaw");
    }
}
