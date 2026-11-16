use crate::{
    SolverError, SolverState,
    flaws::{Flaw, Resolver},
};
use semitone::{Lit, ast::BoolExpr};
use serde_json::{Value, json};

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
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "val": self.val,
        })
    }
}
