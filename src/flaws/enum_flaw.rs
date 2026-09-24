use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::ast::EnumExpr;
use serde_json::{Value, json};
use tracing::trace;

pub(crate) struct EnumFlaw {
    id: FlawId,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    expr: EnumExpr,
    domain: Vec<i32>,
}

impl EnumFlaw {
    pub(crate) fn new(cause: Option<ResolverId>, expr: EnumExpr, domain: Vec<i32>) -> Self {
        Self {
            id: FlawId::default(),
            causes: cause.into_iter().collect(),
            resolvers: Vec::new(),
            expr,
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
    fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }

    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        trace!("Expanding EnumFlaw {} with expr: {} and domain: {:?}", self.id, self.expr, self.domain);
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();

        for &val in &self.domain {
            let expr = smt.track_expr(self.expr.eq(val));
            if smt.get_lit_val(expr) != Some(false) {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(EnumResolver::new(self.id)), expr)?);
            }
        }

        Ok(())
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "enum"
        })
    }
}

struct EnumResolver {
    id: ResolverId,
    flaw: FlawId,
}

impl EnumResolver {
    fn new(flaw: FlawId) -> Self {
        Self { id: ResolverId::default(), flaw }
    }
}

impl Resolver for EnumResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }
}
