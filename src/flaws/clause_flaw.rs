use crate::{
    SolverError, SolverState,
    flaws::{LitResolver, add_lit_candidates},
    graph::{Flaw, FlawId},
};
use semitone::ast::BoolExpr;
use serde_json::{Value, json};
use std::rc::Rc;
use tracing::trace;

pub(crate) struct ClauseFlaw {
    literals: Vec<BoolExpr>,
}

impl ClauseFlaw {
    pub(crate) fn new(literals: Vec<BoolExpr>) -> Self {
        Self { literals }
    }
}

impl Flaw for ClauseFlaw {
    fn expand(&self, slv: &SolverState, flw_id: FlawId) -> Result<(), SolverError> {
        let phi = slv.flaw_phi(flw_id);
        trace!("Expanding ClauseFlaw {} with literals: {}", flw_id, self.literals.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(", "));

        let mut candidates = Vec::with_capacity(self.literals.len());
        if slv.lit_val(phi) != Some(false) {
            for literal in &self.literals {
                let lit = slv.track_expr(literal)?;
                if slv.lit_val(phi) == Some(false) {
                    candidates.clear();
                    break;
                }
                if slv.lit_val(lit) == Some(false) {
                    continue;
                }
                candidates.push((lit, ()));
            }
        }

        add_lit_candidates(slv, flw_id, phi, candidates, |lit, ()| Rc::new(LitResolver::new(lit, json!({ "kind": "clause", "val": lit.to_string() }))))
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "clause",
        })
    }
}
