use riddle::{env::AtomId, language::Disjunction};
use serde_json::{Value, json};
use std::{fmt, ops::Deref, rc::Weak};
use z3::ast::Bool;

use crate::solver::SolverState;

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

pub trait Flaw {
    fn id(&self) -> FlawId;
    fn phi(&self) -> &Bool;
    fn causes(&self) -> Vec<ResolverId>;
    fn supports(&self) -> Vec<ResolverId>;
    fn to_json(&self) -> Value;
}

pub trait Resolver {
    fn id(&self) -> ResolverId;
    fn rho(&self) -> &Bool;
    fn flaw(&self) -> FlawId;
    fn requirements(&self) -> Vec<FlawId>;
    fn add_requirement(&mut self, flaw_id: FlawId);
    fn to_json(&self) -> Value;
}

pub(crate) struct AtomFlaw {
    slv: Weak<SolverState>,
    id: FlawId,
    phi: Bool,
    causes: Vec<ResolverId>,
    supports: Vec<ResolverId>,
    atom_id: AtomId,
    sigma: Bool,
}

impl AtomFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: Bool, cause: Option<ResolverId>, atom: AtomId, sigma: Bool) -> Box<Self> {
        Box::new(Self {
            slv,
            id,
            phi,
            causes: cause.into_iter().collect(),
            supports: Vec::new(),
            atom_id: atom,
            sigma,
        })
    }
}

impl Flaw for AtomFlaw {
    fn id(&self) -> FlawId {
        self.id
    }
    fn phi(&self) -> &Bool {
        &self.phi
    }
    fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }
    fn supports(&self) -> Vec<ResolverId> {
        self.supports.clone()
    }
    fn to_json(&self) -> Value {
        json!({
            "kind": "atom",
            "atom": format!("{}", self.atom_id),
        })
    }
}

pub(crate) struct DisjunctionFlaw {
    slv: Weak<SolverState>,
    id: FlawId,
    phi: Bool,
    causes: Vec<ResolverId>,
    supports: Vec<ResolverId>,
    disjunction: Disjunction,
}

impl DisjunctionFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: Bool, cause: Option<ResolverId>, disjunction: Disjunction) -> Box<Self> {
        Box::new(Self { slv, id, phi, causes: cause.into_iter().collect(), supports: Vec::new(), disjunction })
    }
}

impl Flaw for DisjunctionFlaw {
    fn id(&self) -> FlawId {
        self.id
    }
    fn phi(&self) -> &Bool {
        &self.phi
    }
    fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }
    fn supports(&self) -> Vec<ResolverId> {
        self.supports.clone()
    }
    fn to_json(&self) -> Value {
        json!({
            "kind": "disjunction",
        })
    }
}
