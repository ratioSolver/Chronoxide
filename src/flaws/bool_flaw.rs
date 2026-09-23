use crate::{
    SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::ast::BoolExpr;

pub(crate) struct BoolFlaw {
    id: FlawId,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    expr: BoolExpr,
}

impl BoolFlaw {
    pub(crate) fn new(cause: Option<ResolverId>, expr: BoolExpr) -> Self {
        Self {
            id: FlawId::default(),
            causes: cause.into_iter().collect(),
            resolvers: Vec::with_capacity(2),
            expr,
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
    fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }

    fn expand(&mut self, slv: &SolverState) -> Result<(), crate::SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        match smt.get_bool_val(&self.expr) {
            Some(true) => {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(BoolResolver::new(self.id)), self.expr.clone())?);
            }
            Some(false) => {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(BoolResolver::new(self.id)), !self.expr.clone())?);
            }
            None => {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(BoolResolver::new(self.id)), self.expr.clone())?);
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(BoolResolver::new(self.id)), !self.expr.clone())?);
            }
        }
        Ok(())
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
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
}

impl BoolResolver {
    fn new(flaw: FlawId) -> Self {
        Self { id: ResolverId::default(), flaw }
    }
}

impl Resolver for BoolResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(1)
    }

    fn apply(&mut self, _slv: &SolverState) -> Result<(), crate::SolverError> {
        Ok(())
    }

    fn preconditions(&self) -> Vec<FlawId> {
        vec![]
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::Value::Null
    }
}
