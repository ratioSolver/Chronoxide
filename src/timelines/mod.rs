pub(super) mod consumable_resource;
pub(super) mod reusable_resource;
pub(super) mod state_variable;

use crate::{SolverError, SolverState, graph::Flaw, objects::ArithVar};
use riddle::{
    core::Core,
    env::{AtomId, Env, Slot},
    scope::Class,
};
use semitone::ast::ArithExpr;
use serde_json::Value;

pub trait Timeline: Class {
    fn extract_flaws(&self, slv: &SolverState) -> Result<Vec<Box<dyn Flaw>>, SolverError>;

    fn to_json(&self, slv: &SolverState) -> Value;
}

pub(super) fn get_atom_vars(slv: &SolverState, atom_id: AtomId) -> (ArithExpr, ArithExpr) {
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

pub(super) fn get_atom_amount(slv: &SolverState, atom_id: AtomId) -> ArithExpr {
    let atom = slv.get_atom(atom_id).expect("Atom should exist");
    match atom.get("amount") {
        Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
        _ => unreachable!("Atom should have an 'amount' field"),
    }
}
