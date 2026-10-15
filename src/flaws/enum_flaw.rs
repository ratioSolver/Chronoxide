use std::assert_matches;

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
        assert_matches!(expr, EnumExpr::Var(_), "EnumFlaw can only be created for EnumExpr::Var");
        assert!(!domain.is_empty(), "EnumFlaw domain cannot be empty");
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
    fn causes(&self) -> &Vec<ResolverId> {
        &self.causes
    }

    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        trace!("Expanding EnumFlaw {} with expr: {} and domain: {:?}", self.id, self.expr, self.domain);
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();

        let mut candidates = Vec::with_capacity(self.domain.len());
        for &val in &self.domain {
            let expr = slv.track_expr(&mut smt, &mut graph, self.expr.eq(val))?;
            match smt.get_lit_val_and_level(expr) {
                Some((true, 0)) => {
                    self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(EnumResolver::new(self.id, val)), expr)?);
                    return Ok(());
                }
                Some((false, 0)) => continue,
                _ => candidates.push((val, expr)),
            }
        }

        for (val, expr) in candidates {
            self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(EnumResolver::new(self.id, val)), expr)?);
        }

        Ok(())
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "enum",
            "var": self.expr.to_string(),
        })
    }
}

struct EnumResolver {
    id: ResolverId,
    flaw: FlawId,
    val: i32,
}

impl EnumResolver {
    fn new(flaw: FlawId, val: i32) -> Self {
        Self { id: ResolverId::default(), flaw, val }
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

    fn to_json(&self) -> Value {
        json!({
            "val": self.val,
        })
    }
}
