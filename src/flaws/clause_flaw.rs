use crate::graph::{Flaw, FlawId, Resolver, ResolverId};
use semitone::ast::BoolExpr;
use serde_json::{Value, json};
use tracing::trace;

pub(crate) struct ClauseFlaw {
    id: FlawId,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    literals: Vec<BoolExpr>,
}

impl ClauseFlaw {
    pub(crate) fn new(cause: Option<ResolverId>, literals: Vec<BoolExpr>) -> Self {
        Self {
            id: FlawId::default(),
            causes: cause.into_iter().collect(),
            resolvers: Vec::with_capacity(2),
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
    fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }

    fn expand(&mut self, slv: &crate::SolverState) -> Result<(), crate::SolverError> {
        trace!("Expanding ClauseFlaw {} with literals: {}", self.id, self.literals.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(", "));
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        for literal in &self.literals {
            let expr = smt.track_expr(literal);
            if smt.get_lit_val(expr) != Some(false) {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(ClauseResolver::new(self.id)), expr)?);
            }
        }
        Ok(())
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "clause",
        })
    }
}

struct ClauseResolver {
    id: ResolverId,
    flaw: FlawId,
}

impl ClauseResolver {
    fn new(flaw: FlawId) -> Self {
        Self { id: ResolverId::default(), flaw }
    }
}

impl Resolver for ClauseResolver {
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
