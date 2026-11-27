use crate::{
    SolverError, SolverState,
    graph::{Flaw, ResolverId},
    objects::{ArithVar, EnumVar},
};
use riddle::{
    core::Core,
    env::{AtomId, Env, Slot},
    scope::Class,
};
use semitone::ast::{ArithExpr, BoolExpr};
use serde_json::Value;
use std::rc::Rc;

pub(super) mod consumable_resource;
pub(super) mod reusable_resource;
pub(super) mod state_variable;

pub(super) type FlawWithCauses = (Rc<dyn Flaw>, Vec<ResolverId>);

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

/// Builds the displacement constraint (`a.tau != b.tau`) when at least one atom has a variable `tau`.
pub(super) fn displace_pair_expr(slv: &SolverState, a: AtomId, b: AtomId) -> Option<BoolExpr> {
    match (get_tau(slv, a), get_tau(slv, b)) {
        (Slot::Primitive(a_var), Slot::ObjectRef(b_obj)) => {
            let a_var = a_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
            Some(!a_var.eq(usize::from(b_obj)))
        }
        (Slot::ObjectRef(a_obj), Slot::Primitive(b_var)) => {
            let b_var = b_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
            Some(!b_var.eq(usize::from(a_obj)))
        }
        (Slot::Primitive(a_var), Slot::Primitive(b_var)) => {
            let a_var = a_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
            let b_var = b_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
            Some(!a_var.eq(b_var))
        }
        _ => None,
    }
}
