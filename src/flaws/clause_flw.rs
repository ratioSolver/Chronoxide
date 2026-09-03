use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::{Lit, ast::BoolExpr};

pub(crate) struct ClauseFlaw {
    id: FlawId,
    phi: Lit,
    status: Option<bool>,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    literals: Vec<BoolExpr>,
}

impl ClauseFlaw {
    pub(crate) fn new(phi: Lit, status: Option<bool>, cause: Option<ResolverId>, literals: Vec<BoolExpr>) -> Self {
        assert!(status != Some(false), "Cannot create a ClauseFlaw with status Some(false)");
        Self {
            id: 0,
            phi,
            status,
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

        let rhos: Vec<Lit> = {
            let mut smt = state.smt.borrow_mut();
            self.literals.iter().map(|lit| smt.encode_bool(lit)).collect()
        };

        let mut resolvers: Vec<Box<dyn Resolver>> = Vec::with_capacity(rhos.len());

        let smt = state.smt.borrow();
        for rho in rhos {
            let status = smt.get_lit_val(rho);
            if status != Some(false) {
                resolvers.push(Box::new(ClauseResolver::new(self.id, rho, status)));
            }
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
    rho: Lit,
    status: Option<bool>,
    sub_flaws: Vec<FlawId>,
}

impl ClauseResolver {
    fn new(flaw: FlawId, rho: Lit, status: Option<bool>) -> Self {
        assert!(status != Some(false), "Cannot create a ClauseResolver with status Some(false)");
        Self { id: 0, flaw, rho, status, sub_flaws: Vec::new() }
    }
}

impl Resolver for ClauseResolver {
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
            "kind": "lit"
        })
    }
}
