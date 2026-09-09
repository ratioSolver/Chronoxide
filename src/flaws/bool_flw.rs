use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::{Lit, ast::BoolExpr};

pub(crate) struct BoolFlaw {
    id: FlawId,
    phi: Lit,
    status: Option<bool>,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    target: BoolExpr,
}

impl BoolFlaw {
    pub(crate) fn new(phi: Lit, status: Option<bool>, cause: Option<ResolverId>, target: BoolExpr) -> Self {
        assert!(status != Some(false), "Cannot create a BoolFlaw with status Some(false)");
        Self {
            id: FlawId::default(),
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

    fn phi(&self) -> Lit {
        self.phi
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
        let mut resolvers: Vec<Box<dyn Resolver>> = Vec::new();

        let rho = state.smt.borrow_mut().track_expr(&self.target);
        let smt = state.smt.borrow();

        let state_1 = smt.get_lit_val(rho);
        if state_1 != Some(false) {
            resolvers.push(Box::new(BoolResolver::new(self.id, rho, state_1)));
        }

        let state_2 = smt.get_lit_val(!rho);
        if state_2 != Some(false) {
            resolvers.push(Box::new(BoolResolver::new(self.id, !rho, state_2)));
        }
        Ok(resolvers)
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
    rho: Lit,
    status: Option<bool>,
    sub_flaws: Vec<FlawId>,
}

impl BoolResolver {
    fn new(flaw: FlawId, rho: Lit, status: Option<bool>) -> Self {
        assert!(status != Some(false), "Cannot create a BoolResolver with status Some(false)");
        Self { id: ResolverId::default(), flaw, rho, status, sub_flaws: Vec::new() }
    }
}

impl Resolver for BoolResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> Lit {
        self.rho
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
