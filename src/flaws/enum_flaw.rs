use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
};
use riddle::env::ObjectId;
use semitone::{Lit, ast::EnumExpr};
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
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().expect("No current flaw found");
        trace!("Expanding EnumFlaw {} with expr: {} and domain: {:?}", flw_id, self.expr, self.domain.iter().map(|id| format!("{}", id)).collect::<Vec<_>>().join(", "));

        let mut candidates = Vec::with_capacity(self.domain.len());
        for &val in &self.domain {
            let val_lit = slv.track_expr(&mut smt, &mut graph, self.expr.eq(*val))?;
            if smt.probe(&[phi, val_lit]).map_err(|_| SolverError::Inconsistent)? {
                candidates.push((val, val_lit));
            }
        }

        match candidates.len() {
            0 => return Err(SolverError::Inconsistent),
            1 => {
                let (val, val_lit) = candidates[0];
                slv.add_resolver(&mut smt, &mut graph, phi, Box::new(EnumResolver::new(val, val_lit)))?;
            }
            _ => {
                for (val, val_lit) in candidates {
                    let rho = smt.new_lit();
                    slv.add_resolver(&mut smt, &mut graph, rho, Box::new(EnumResolver::new(val, val_lit)))?;
                }
            }
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
    val: ObjectId,
    lit: Lit,
}

impl EnumResolver {
    fn new(val: ObjectId, lit: Lit) -> Self {
        Self { val, lit }
    }
}

impl Resolver for EnumResolver {
    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().expect("No current resolver found");
        // ρ → lit
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "val": self.val.to_string(),
        })
    }
}
