use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::ast::BoolExpr;

pub(crate) struct BoolFlaw {
    id: FlawId,
    phi: BoolExpr,
    status: Option<bool>,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    target: BoolExpr,
}

impl BoolFlaw {
    pub(crate) fn new(phi: BoolExpr, status: Option<bool>, cause: Option<ResolverId>, target: BoolExpr) -> Self {
        Self {
            id: 0,
            phi,
            status,
            causes: cause.into_iter().collect(),
            resolvers: Vec::new(),
            estimated_cost: f64::INFINITY,
            is_expanded: false,
            target,
        }
    }
}

impl Flaw for BoolFlaw {
    fn id(&self) -> FlawId {
        self.id
    }
    fn set_id(&mut self, id: FlawId) {
        self.id = id;
    }

    fn phi(&self) -> &BoolExpr {
        &self.phi
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn causes(&self) -> &[ResolverId] {
        &self.causes
    }
    fn resolvers(&self) -> &[ResolverId] {
        &self.resolvers
    }
    fn add_resolver(&mut self, id: ResolverId) {
        self.resolvers.push(id);
    }

    fn estimated_cost(&self) -> f64 {
        self.estimated_cost
    }
    fn set_estimated_cost(&mut self, cost: f64) {
        self.estimated_cost = cost;
    }

    fn is_expanded(&self) -> bool {
        self.is_expanded
    }

    fn expand(&mut self, state: &SolverState) -> Result<Vec<Box<dyn Resolver>>, SolverError> {
        self.is_expanded = true;
        Ok(vec![Box::new(BoolResolver::new(self.id, self.target.clone(), state.smt.borrow().get_bool_val(&self.target))), Box::new(BoolResolver::new(self.id, !self.target.clone(), state.smt.borrow().get_bool_val(&!&self.target)))])
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "bool"
        })
    }
}

struct BoolResolver {
    id: ResolverId,
    flaw: FlawId,
    rho: BoolExpr,
    status: Option<bool>,
    sub_flaws: Vec<FlawId>,
}

impl BoolResolver {
    fn new(flaw: FlawId, rho: BoolExpr, status: Option<bool>) -> Self {
        Self { id: 0, flaw, rho, status, sub_flaws: Vec::new() }
    }
}

impl Resolver for BoolResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> &BoolExpr {
        &self.rho
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn intrinsic_cost(&self) -> f64 {
        1f64
    }

    fn sub_flaws(&self) -> &[FlawId] {
        &self.sub_flaws
    }

    fn apply(&mut self, _state: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "bool"
        })
    }
}
