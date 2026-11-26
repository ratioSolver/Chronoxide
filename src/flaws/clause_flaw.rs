use crate::{
    SolverError, SolverState,
    flaws::{LitResolver, add_lit_candidates},
    graph::Flaw,
};
use semitone::ast::BoolExpr;
use serde_json::{Value, json};
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
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().expect("No current flaw found");
        trace!("Expanding ClauseFlaw {} with literals: {}", flw_id, self.literals.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(", "));

        let mut candidates = Vec::with_capacity(self.literals.len());
        if smt.get_lit_val(phi) != Some(false) {
            for literal in &self.literals {
                let lit = slv.track_expr(&mut smt, &mut graph, literal)?;
                if smt.get_lit_val(phi) == Some(false) {
                    // ϕ is already false (as a consequence of `track_expr`), no need to continue checking candidates
                    candidates.clear();
                    break;
                }
                if smt.get_lit_val(lit) == Some(false) {
                    continue;
                }
                if smt.probe(&[phi, lit]).map_err(|_| SolverError::Inconsistent)? {
                    candidates.push((lit, ()));
                }
                if smt.get_lit_val(phi) == Some(false) {
                    // ϕ is already false (as a consequence of `probe`), no need to continue checking candidates
                    candidates.clear();
                    break;
                }
            }
        }

        add_lit_candidates(slv, &mut smt, &mut graph, phi, candidates, |lit, ()| Box::new(LitResolver::new(lit, json!({ "kind": "clause", "val": lit.to_string() }))))
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "clause",
        })
    }
}
