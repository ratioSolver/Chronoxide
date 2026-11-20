use crate::{
    SolverError, SolverState,
    graph::{Flaw, ResolverId},
    objects::ArithVar,
};
use riddle::{
    core::Core,
    env::{AtomId, Env, Slot},
    scope::Class,
};
use semitone::ast::ArithExpr;
use serde_json::Value;

pub(super) mod reusable_resource;
pub(super) mod state_variable;

type FlawWithCauses = (Box<dyn Flaw>, Vec<ResolverId>);

pub trait Timeline: Class {
    fn extract_flaws(&self, slv: &SolverState) -> Result<Vec<FlawWithCauses>, SolverError>;

    fn to_json(&self, slv: &SolverState) -> Value;
}

pub(super) fn get_tau(slv: &SolverState, atom_id: AtomId) -> Slot {
    let atom = slv.get_atom(atom_id).expect("Atom should exist");
    atom.get("tau").expect("Atom should have a 'tau' field")
}

pub(super) fn get_interval_vars(slv: &SolverState, atom_id: AtomId) -> (ArithExpr, ArithExpr) {
    let atom = slv.get_atom(atom_id).expect("Atom should exist");
    let start = match atom.get("start") {
        Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have a 'start' field"),
        _ => unreachable!("Atom should have a 'start' field"),
    };
    let end = match atom.get("end") {
        Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'end' field"),
        _ => unreachable!("Atom should have an 'end' field"),
    };
    (start, end)
}

pub(super) fn get_amount(slv: &SolverState, atom_id: AtomId) -> ArithExpr {
    let atom = slv.get_atom(atom_id).expect("Atom should exist");
    match atom.get("amount") {
        Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
        _ => unreachable!("Atom should have an 'amount' field"),
    }
}
