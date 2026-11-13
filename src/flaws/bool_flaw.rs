use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
};
use semitone::{Lit, ast::BoolExpr};
use serde_json::{Value, json};
use tracing::trace;

pub(crate) struct BoolFlaw {
    expr: BoolExpr,
}

impl BoolFlaw {
    pub(crate) fn new(expr: BoolExpr) -> Self {
        Self { expr }
    }
}

impl Flaw for BoolFlaw {
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding BoolFlaw {} with expr: {}", flw_id, self.expr);

        let lit = slv.track_expr(&mut smt, &mut graph, &self.expr)?;
        let mut candidates = Vec::with_capacity(2);
        for (val, val_lit) in [(true, lit), (false, !lit)] {
            if smt.probe(&[phi, val_lit]).map_err(|_| SolverError::Inconsistent)? {
                candidates.push((val, val_lit));
            }
        }

        let single = candidates.len() == 1;
        for (val, val_lit) in candidates {
            let rho = if single { phi } else { smt.new_lit() };
            if rho != phi {
                // (ϕ ∧ val_lit) → ρ
                slv.add_clause(&mut smt, &mut graph, vec![!phi, !val_lit, rho])?;
            }
            slv.add_resolver(&mut smt, &mut graph, Box::new(BoolResolver::new(val, val_lit)), rho)?;
        }

        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "bool",
            "var": self.expr.to_string(),
        })
    }
}

struct BoolResolver {
    val: bool,
    lit: Lit,
}

impl BoolResolver {
    fn new(val: bool, lit: Lit) -> Self {
        Self { val, lit }
    }
}

impl Resolver for BoolResolver {
    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;
        // ρ → val_lit
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "val": self.val,
        })
    }
}
