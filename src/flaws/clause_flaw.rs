use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
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
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, _) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding ClauseFlaw {} with literals: {}", flw_id, self.literals.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(", "));

        for literal in &self.literals {
            let expr = slv.track_expr(&mut smt, &mut graph, literal)?;
            if smt.get_lit_val_and_level(expr) != Some((false, 0)) {
                slv.add_resolver(&mut smt, &mut graph, Box::new(ClauseResolver), expr)?;
            }
        }
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "clause",
        })
    }
}

struct ClauseResolver;

impl Resolver for ClauseResolver {}
