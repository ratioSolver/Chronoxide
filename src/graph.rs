use crate::solver::{SolverError, SolverState};
use riddle::{env::AtomId, language::Disjunction};
use serde::Serialize;
use serde_json::{Value, json};
use std::{fmt, ops::Deref, rc::Weak};
use z3::ast::Bool;

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

#[derive(Clone, Copy, Serialize)]
pub enum State {
    #[serde(rename = "active")]
    Active,
    #[serde(rename = "inactive")]
    Inactive,
    #[serde(rename = "forbidden")]
    Forbidden,
}

pub trait Flaw {
    fn id(&self) -> FlawId;
    fn phi(&self) -> &Bool;
    fn causes(&self) -> Vec<ResolverId>;
    fn supports(&self) -> Vec<ResolverId>;
    fn compute_resolvers(&mut self);
    fn get_state(&self) -> State;
    fn set_state(&mut self, state: State);
    fn get_cost(&self) -> f32;
    fn set_cost(&mut self, cost: f32);
    fn to_json(&self) -> Value;
}

pub trait Resolver {
    fn id(&self) -> ResolverId;
    fn rho(&self) -> &Bool;
    fn flaw(&self) -> FlawId;
    fn intrinsic_cost(&self) -> f32;
    fn apply(&mut self) -> Result<(), SolverError>;
    fn requirements(&self) -> Vec<FlawId>;
    fn add_requirement(&mut self, flaw_id: FlawId);
    fn get_state(&self) -> State;
    fn set_state(&mut self, state: State);
    fn to_json(&self) -> Value;
}

pub(crate) struct AtomFlaw {
    slv: Weak<SolverState>,
    id: FlawId,
    phi: Bool,
    causes: Vec<ResolverId>,
    supports: Vec<ResolverId>,
    state: State,
    cost: f32,
    atom_id: AtomId,
    sigma: Bool,
    resolvers: Vec<ResolverId>,
}

impl AtomFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: Bool, cause: Option<ResolverId>, atom: AtomId, sigma: Bool) -> Box<Self> {
        Box::new(Self {
            slv,
            id,
            phi,
            causes: cause.into_iter().collect(),
            supports: Vec::new(),
            state: cause.map_or(State::Active, |_| State::Inactive),
            cost: f32::INFINITY,
            atom_id: atom,
            sigma,
            resolvers: Vec::new(),
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
    fn compute_resolvers(&mut self) {
        unimplemented!()
    }
    fn get_cost(&self) -> f32 {
        self.cost
    }
    fn set_cost(&mut self, cost: f32) {
        self.cost = cost;
    }
    fn get_state(&self) -> State {
        self.state
    }
    fn set_state(&mut self, state: State) {
        self.state = state;
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
    state: State,
    cost: f32,
    disjunction: Disjunction,
    resolvers: Vec<ResolverId>,
}

impl DisjunctionFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: Bool, cause: Option<ResolverId>, disjunction: Disjunction) -> Box<Self> {
        Box::new(Self {
            slv,
            id,
            phi,
            causes: cause.into_iter().collect(),
            supports: Vec::new(),
            state: cause.map_or(State::Active, |_| State::Inactive),
            cost: f32::INFINITY,
            disjunction,
            resolvers: Vec::new(),
        })
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
    fn compute_resolvers(&mut self) {
        unimplemented!()
    }
    fn get_cost(&self) -> f32 {
        self.cost
    }
    fn set_cost(&mut self, cost: f32) {
        self.cost = cost;
    }
    fn get_state(&self) -> State {
        self.state
    }
    fn set_state(&mut self, state: State) {
        self.state = state;
    }
    fn to_json(&self) -> Value {
        json!({
            "kind": "disjunction",
        })
    }
}
