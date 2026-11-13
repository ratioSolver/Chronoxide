use std::assert_matches;

use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
};
use semitone::{Lit, ast::EnumExpr};
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
        let (flw_id, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding EnumFlaw {} with expr: {} and domain: {:?}", flw_id, self.expr, self.domain);

        let mut candidates = Vec::with_capacity(self.domain.len());
        for &val in &self.domain {
            let val_lit = slv.track_expr(&mut smt, &mut graph, self.expr.eq(val))?;
            if smt.probe(&[phi, val_lit]).map_err(|_| SolverError::Inconsistent)? {
                candidates.push((val, val_lit));
            }
        }

        let single = candidates.len() == 1;
        for (val, val_lit) in candidates {
            let rho = if single { phi } else { smt.new_lit() };
            if rho != phi {
                // (ϕ ∧ (expr == val)) → ρ
                slv.add_clause(&mut smt, &mut graph, vec![!phi, !val_lit, rho])?;
            }
            slv.add_resolver(&mut smt, &mut graph, Box::new(EnumResolver::new(val, val_lit)), rho)?;
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
    lit: Lit,
}

impl EnumResolver {
    fn new(val: i32, lit: Lit) -> Self {
        Self { val, lit }
    }
}

impl Resolver for EnumResolver {
    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;
        // ρ → (expr == val)
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "val": self.val,
        })
    }
}
