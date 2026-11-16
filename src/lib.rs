use crate::{
    flaws::{FlawId, ResolverId},
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
use semitone::SeMiTONE;
use serde_json::Value;
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;

mod flaws;
mod graph;

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    smt: RefCell<SeMiTONE>,
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
            graph: RefCell::new(Graph::new(tx_event.clone())),
            tx_event,
        });
        slv
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
