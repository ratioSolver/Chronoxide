use crate::{
    SolverError, SolverState,
    flaws::{LitResolver, add_lit_candidates},
    graph::Flaw,
};
use riddle::env::ObjectId;
use semitone::ast::EnumExpr;
use serde_json::{Value, json};
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
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().expect("No current flaw found");
        trace!("Expanding EnumFlaw {} with expr: {} and domain: {:?}", flw_id, self.expr, self.domain.iter().map(|id| format!("{}", id)).collect::<Vec<_>>().join(", "));

        let mut candidates = Vec::with_capacity(self.domain.len());
        if smt.get_lit_val(phi) != Some(false) {
            for &val in &self.domain {
                let val_lit = slv.track_expr(&mut smt, &mut graph, self.expr.eq(usize::from(val)))?;
                if smt.get_lit_val(phi) == Some(false) {
                    candidates.clear();
                    break;
                }
                if smt.get_lit_val(val_lit) == Some(false) {
                    continue;
                }
                candidates.push((val_lit, val));
            }
        }

        add_lit_candidates(slv, &mut smt, &mut graph, phi, candidates, |lit, val| Box::new(LitResolver::new(lit, json!({ "kind": "enum", "val": val.to_string() }))))
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "enum",
            "var": self.expr.to_string(),
        })
    }
}
