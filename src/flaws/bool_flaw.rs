use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
};
use semitone::ast::BoolExpr;
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
        let (flw_id, _) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding BoolFlaw {} with expression: {}", flw_id, self.expr);

        let expr = slv.track_expr(&mut smt, &mut graph, &self.expr)?;
        match smt.get_lit_val_and_level(expr) {
            Some((true, 0)) => {
                slv.add_resolver(&mut smt, &mut graph, Box::new(BoolResolver), expr)?;
            }
            Some((false, 0)) => {
                slv.add_resolver(&mut smt, &mut graph, Box::new(BoolResolver), !expr)?;
            }
            _ => {
                slv.add_resolver(&mut smt, &mut graph, Box::new(BoolResolver), expr)?;
                slv.add_resolver(&mut smt, &mut graph, Box::new(BoolResolver), !expr)?;
            }
        }
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "bool"
        })
    }
}

struct BoolResolver;

impl Resolver for BoolResolver {}
