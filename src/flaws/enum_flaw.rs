use crate::{
    SolverError, SolverState,
    flaws::{LitResolver, add_lit_candidates},
    graph::{Flaw, FlawId},
};
use riddle::env::ObjectId;
use semitone::ast::EnumExpr;
use serde_json::{Value, json};
use std::rc::Rc;
use tracing::trace;

pub(crate) struct EnumFlaw {
    expr: EnumExpr,
    domain: Vec<ObjectId>,
}

impl EnumFlaw {
    pub(crate) fn new(expr: EnumExpr, domain: Vec<ObjectId>) -> Self {
        assert!(matches!(expr, EnumExpr::Var(_)), "EnumFlaw can only be created for EnumExpr::Var");
        assert!(!domain.is_empty(), "EnumFlaw domain cannot be empty");
        Self { expr, domain }
    }
}

impl Flaw for EnumFlaw {
    fn expand(&self, slv: &SolverState, flw_id: FlawId) -> Result<(), SolverError> {
        let phi = slv.flaw_phi(flw_id);
        trace!("Expanding EnumFlaw {} with expr: {} and domain: {:?}", flw_id, self.expr, self.domain.iter().map(|id| format!("{}", id)).collect::<Vec<_>>().join(", "));

        let mut candidates = Vec::with_capacity(self.domain.len());
        if slv.lit_val(phi) != Some(false) {
            for &val in &self.domain {
                let val_lit = slv.track_expr(self.expr.eq(usize::from(val)))?;
                if slv.lit_val(phi) == Some(false) {
                    candidates.clear();
                    break;
                }
                if slv.lit_val(val_lit) == Some(false) {
                    continue;
                }
                candidates.push((val_lit, val));
            }
        }

        add_lit_candidates(slv, flw_id, phi, candidates, |lit, val| Rc::new(LitResolver::new(lit, json!({ "kind": "enum", "val": val.to_string() }))))
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "enum",
            "var": self.expr.to_string(),
        })
    }
}
