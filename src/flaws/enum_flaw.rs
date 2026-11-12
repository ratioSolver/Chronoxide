use std::assert_matches;

use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
};
use semitone::ast::EnumExpr;
use serde_json::{Value, json};
use tracing::trace;

pub(crate) struct EnumFlaw {
    expr: EnumExpr,
    domain: Vec<i32>,
}

impl EnumFlaw {
    pub(crate) fn new(expr: EnumExpr, domain: Vec<i32>) -> Self {
        assert_matches!(expr, EnumExpr::Var(_), "EnumFlaw can only be created for EnumExpr::Var");
        assert!(!domain.is_empty(), "EnumFlaw domain cannot be empty");
        Self { expr, domain }
    }
}

impl Flaw for EnumFlaw {
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, _) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding EnumFlaw {} with expr: {} and domain: {:?}", flw_id, self.expr, self.domain);

        let mut candidates = Vec::with_capacity(self.domain.len());
        for &val in &self.domain {
            let expr = slv.track_expr(&mut smt, &mut graph, self.expr.eq(val))?;
            match smt.get_lit_val_and_level(expr) {
                Some((true, 0)) => {
                    slv.add_resolver(&mut smt, &mut graph, Box::new(EnumResolver::new(val)), expr)?;
                    return Ok(());
                }
                Some((false, 0)) => continue,
                _ => candidates.push((val, expr)),
            }
        }

        for (val, expr) in candidates {
            slv.add_resolver(&mut smt, &mut graph, Box::new(EnumResolver::new(val)), expr)?;
        }

        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "enum",
            "var": self.expr.to_string(),
        })
    }
}

struct EnumResolver {
    val: i32,
}

impl EnumResolver {
    fn new(val: i32) -> Self {
        Self { val }
    }
}

impl Resolver for EnumResolver {
    fn to_json(&self) -> Value {
        json!({
            "val": self.val,
        })
    }
}
