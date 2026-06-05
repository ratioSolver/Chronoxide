use crate::ToJson;
use std::{fmt, ops::Deref};
use watchsat::VarId;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FlawId(pub(crate) usize);

impl Deref for FlawId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for FlawId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ϕ{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ResolverId(pub(crate) usize);

impl Deref for ResolverId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for ResolverId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ρ{}", self.0)
    }
}

pub trait Flaw: ToJson {
    fn id(&self) -> FlawId;
    fn phi(&self) -> VarId;
}

pub trait Resolver: ToJson {
    fn id(&self) -> ResolverId;
    fn flaw(&self) -> FlawId;
    fn rho(&self) -> VarId;
    fn add_ac_constraint(&self, _constraint: ac3rm::ConstraintId) {
        unimplemented!()
    }
    fn lin_guard(&self) -> Option<linarith::GuardId> {
        None
    }
}
