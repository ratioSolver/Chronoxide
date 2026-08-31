use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::ast::BoolExpr;

pub(crate) struct ClauseFlaw {
    id: FlawId,
    phi: BoolExpr,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    literals: Vec<BoolExpr>,
}

impl ClauseFlaw {
    pub(crate) fn new(phi: BoolExpr, cause: Option<ResolverId>, literals: Vec<BoolExpr>) -> Self {
        Self {
            id: 0,
            phi,
            causes: cause.into_iter().collect(),
            resolvers: Vec::new(),
            estimated_cost: f64::INFINITY,
            is_expanded: false,
            literals,
        }
    }
}

impl Flaw for ClauseFlaw {
    fn id(&self) -> FlawId {
        self.id
    }
    fn set_id(&mut self, id: FlawId) {
        self.id = id;
    }

    fn phi(&self) -> &BoolExpr {
        &self.phi
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

    fn expand(&mut self, _state: &SolverState) -> Result<Vec<Box<dyn Resolver>>, SolverError> {
        self.is_expanded = true;

        let mut resolvers: Vec<Box<dyn Resolver>> = Vec::with_capacity(self.literals.len());
        for literal in &self.literals {
            resolvers.push(Box::new(ClauseResolver::new(self.id, literal.clone())));
        }

        Ok(resolvers)
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "clause",
            "lits": self.literals.iter().map(|lit| lit.to_string()).collect::<Vec<_>>(),
        })
    }
}

struct ClauseResolver {
    id: ResolverId,
    flaw: FlawId,
    rho: BoolExpr,
    sub_flaws: Vec<FlawId>,
}

impl ClauseResolver {
    fn new(flaw: FlawId, rho: BoolExpr) -> Self {
        Self { id: 0, flaw, rho, sub_flaws: Vec::new() }
    }
}

impl Resolver for ClauseResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> &BoolExpr {
        &self.rho
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
            "kind": "lit"
        })
    }
}
