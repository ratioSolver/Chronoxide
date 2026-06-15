use crate::{ToJson, solver::SolverError, solver_state::SolverState};
use linarith::Rational;
use serde_json::{Value, json};
use std::{
    fmt,
    ops::Deref,
    rc::{Rc, Weak},
};
use watchsat::{LBool, VarId};

pub(crate) mod atom_flaw;
pub(crate) mod clause_flaw;
pub(crate) mod enum_flaw;

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
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> FlawId;
    fn phi(&self) -> VarId;
    fn causes(&self) -> Vec<ResolverId>;
    fn supports(&self) -> Vec<ResolverId>;
    fn resolvers(&self) -> Vec<ResolverId>;
    fn cost(&self) -> Rational;
    fn set_cost(&mut self, cost: Rational);
    fn is_expanded(&self) -> bool;
    fn compute_resolvers(&mut self);
    fn add_resolver(&mut self, resolver_id: ResolverId);
}

pub trait Resolver: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> ResolverId;
    fn flaw(&self) -> FlawId;
    fn rho(&self) -> VarId;
    fn intrinsic_cost(&self) -> Rational;
    fn apply(&self) -> Result<(), SolverError>;
    fn requirements(&self) -> Vec<FlawId> {
        unimplemented!()
    }
    fn ac_constraints(&self) -> Option<Vec<ac3rm::ConstraintId>> {
        unimplemented!()
    }
    fn add_ac_constraint(&mut self, _constraint: ac3rm::ConstraintId) {
        unimplemented!()
    }
    fn lin_guard(&self) -> linarith::GuardId {
        unimplemented!()
    }
}

pub struct FlawData {
    slv: Weak<SolverState>,
    id: FlawId,
    phi: VarId,
    causes: Vec<ResolverId>,
    supports: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,
    cost: Rational,
    expanded: bool,
}

impl FlawData {
    pub fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, causes: Vec<ResolverId>) -> Self {
        Self {
            slv,
            id,
            phi,
            causes: causes.clone(),
            supports: causes,
            resolvers: Vec::new(),
            cost: Rational::POSITIVE_INFINITY,
            expanded: false,
        }
    }

    pub fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    pub fn id(&self) -> FlawId {
        self.id
    }

    pub fn phi(&self) -> VarId {
        self.phi
    }

    pub fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }

    pub fn supports(&self) -> Vec<ResolverId> {
        self.supports.clone()
    }

    pub fn add_support(&mut self, support_id: ResolverId) {
        self.supports.push(support_id);
    }

    pub fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }

    pub fn add_resolver(&mut self, resolver_id: ResolverId) {
        self.resolvers.push(resolver_id);
    }

    pub fn cost(&self) -> Rational {
        self.cost
    }

    pub fn set_cost(&mut self, cost: Rational) {
        self.cost = cost;
    }

    pub fn is_expanded(&self) -> bool {
        self.expanded
    }

    pub fn set_expanded(&mut self) {
        assert!(!self.expanded, "Flaw {} is already expanded", self.id);
        self.expanded = true;
    }
}

pub struct ResolverData {
    slv: Weak<SolverState>,
    id: ResolverId,
    flaw: FlawId,
    rho: VarId,
    requirements: Vec<FlawId>,
    intrinsic_cost: Rational,
}

impl ResolverData {
    pub fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, intrinsic_cost: Rational) -> Self {
        Self { slv, id, flaw, rho, requirements: Vec::new(), intrinsic_cost }
    }

    pub fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    pub fn id(&self) -> ResolverId {
        self.id
    }

    pub fn flaw(&self) -> FlawId {
        self.flaw
    }

    pub fn rho(&self) -> VarId {
        self.rho
    }

    pub fn requirements(&self) -> Vec<FlawId> {
        self.requirements.clone()
    }

    pub fn add_requirement(&mut self, flaw_id: FlawId) {
        self.requirements.push(flaw_id);
    }

    pub fn intrinsic_cost(&self) -> Rational {
        self.intrinsic_cost
    }
}

impl ToJson for Rational {
    fn to_json(&self) -> Value {
        json!({
            "num": self.num,
            "den": self.den
        })
    }
}

impl ToJson for LBool {
    fn to_json(&self) -> Value {
        match self {
            LBool::True => true.into(),
            LBool::False => false.into(),
            LBool::Undef => Value::Null,
        }
    }
}
