use crate::{
    flaws::{Flaw, FlawId, Resolver, ResolverId},
    graph::Graph,
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    delegate_env, delegate_scope,
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot},
    language::{AtomKind, Disjunction, ResolutionConstraint},
    scope::{Class, Field, Function, Predicate, Scope, Type},
};
use semitone::{Lit, SeMiTONE, ast};
use serde_json::Value;
use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;
use tracing::trace;

mod flaws;
mod graph;

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    smt: RefCell<SeMiTONE>,
    notified_len: Cell<usize>,
    graph: RefCell<Graph>,
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
            tx_event,
        });
        slv
    }

    fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    pub fn add_flaw(&self, smt: &mut SeMiTONE, graph: &mut Graph, causes: Vec<ResolverId>, flw: Box<dyn Flaw>) -> Result<FlawId, SolverError> {
        let mut cause_lits: Vec<Lit> = graph.resolver_rhos(&causes);
        cause_lits.sort_unstable();
        cause_lits.dedup();

        unimplemented!()
    }

    pub fn add_resolver(&self, smt: &mut SeMiTONE, graph: &mut Graph, rho: Lit, res: Box<dyn Resolver>) -> Result<ResolverId, SolverError> {
        unimplemented!()
    }

    fn track_expr(&self, smt: &mut SeMiTONE, graph: &mut Graph, expr: ast::BoolExpr) -> Result<Lit, SolverError> {
        loop {
            match smt.track_expr(expr.as_ref()) {
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
        smt.add_clause(lemma).is_ok()
    }
}

delegate_scope!(SolverState, core);
delegate_env!(SolverState, core);

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Slot {
        unimplemented!()
    }
    fn new_bool_var(&self) -> Slot {
        unimplemented!()
    }
    fn new_int(&self, value: &str) -> Slot {
        unimplemented!()
    }
    fn new_int_var(&self) -> Slot {
        unimplemented!()
    }
    fn new_real(&self, num: &str, den: &str) -> Slot {
        unimplemented!()
    }
    fn new_real_var(&self) -> Slot {
        unimplemented!()
    }
    fn new_string(&self, value: &str) -> Slot {
        unimplemented!()
    }
    fn new_string_var(&self) -> Slot {
        unimplemented!()
    }

    fn sum(&self, sum: &[Slot]) -> Result<Slot, RiddleError> {
        unimplemented!()
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        unimplemented!()
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        unimplemented!()
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        unimplemented!()
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        unimplemented!()
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        unimplemented!()
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        unimplemented!()
    }

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        unimplemented!()
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        unimplemented!()
    }
    fn new_atom(&self, predicate: Rc<Predicate>, kind: AtomKind, args: HashMap<String, Slot>, resolution_constraint: ResolutionConstraint) -> Result<AtomId, RiddleError> {
        unimplemented!()
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        unimplemented!()
    }
}

#[derive(Debug)]
pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

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
