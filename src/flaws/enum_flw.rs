use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::ast::{BoolExpr, EnumExpr};
use serde_json::{Value, json};

pub(crate) struct EnumFlaw {
    id: FlawId,
    phi: BoolExpr,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    target: EnumExpr,
    domain: Vec<i32>,
}

impl EnumFlaw {
    pub(crate) fn new(phi: BoolExpr, cause: Option<ResolverId>, target: EnumExpr, domain: Vec<i32>) -> Self {
        Self {
            id: 0,
            phi,
            causes: cause.into_iter().collect(),
            resolvers: Vec::new(),
            estimated_cost: f64::INFINITY,
            is_expanded: false,
            target,
            domain,
        }
    }
}

impl Flaw for EnumFlaw {
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

        let mut resolvers: Vec<Box<dyn Resolver>> = Vec::with_capacity(self.domain.len());

        for &val in &self.domain {
            resolvers.push(Box::new(EnumResolver::new(self.id, val, self.target.eq(val))));
        }

        Ok(resolvers)
    }

    fn to_json(&self) -> Value {
        let EnumExpr::Var(var) = &self.target else {
            panic!("Expected a EnumExpr::Var for flaw target");
        };
        json!({
            "kind": "enum",
            "var": var,
        })
    }
}

struct EnumResolver {
    id: ResolverId,
    flaw: FlawId,
    val: i32,
    rho: BoolExpr,
    sub_flaws: Vec<FlawId>,
}

impl EnumResolver {
    fn new(flaw: FlawId, val: i32, rho: BoolExpr) -> Self {
        Self { id: 0, flaw, val, rho, sub_flaws: Vec::new() }
    }
}

impl Resolver for EnumResolver {
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

    fn to_json(&self) -> Value {
        json!({
            "kind": "val",
            "val": self.val,
        })
    }
}
