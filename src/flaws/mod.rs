use crate::{SolverError, SolverState};
use serde_json::Value;
use std::{
    fmt,
    ops::{Index, IndexMut},
};

pub(super) mod bool_flaw;
pub(super) mod clause_flaw;
pub(super) mod disjunction_flaw;
pub(super) mod enum_flaw;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct FlawId(usize);

impl<T> Index<FlawId> for Vec<T> {
    type Output = T;
    fn index(&self, flw: FlawId) -> &Self::Output {
        &self[flw.0]
    }
}

impl<T> IndexMut<FlawId> for Vec<T> {
    fn index_mut(&mut self, flw: FlawId) -> &mut Self::Output {
        &mut self[flw.0]
    }
}

impl fmt::Display for FlawId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ϕ{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ResolverId(usize);

impl<T> Index<ResolverId> for Vec<T> {
    type Output = T;
    fn index(&self, res: ResolverId) -> &Self::Output {
        &self[res.0]
    }
}

impl<T> IndexMut<ResolverId> for Vec<T> {
    fn index_mut(&mut self, res: ResolverId) -> &mut Self::Output {
        &mut self[res.0]
    }
}

impl fmt::Display for ResolverId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ρ{}", self.0)
    }
}

pub trait Flaw {
    /// Expands this flaw by adding resolvers to the graph that can potentially solve it.
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError>;

    /// Serializes the domain-specific payload of this flaw to JSON.
    fn to_json(&self) -> Value;
}

pub trait Resolver {
    /// The intrinsic cost of selecting this resolver, independent from the current state of the graph.
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(1)
    }

    /// Applies this resolver, adding its constraints, sub-flaws, or causal links to the solver state.
    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    /// Serializes the domain-specific payload of this resolver to JSON.
    fn to_json(&self) -> Value {
        Value::Null
    }
}
