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
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().expect("No current flaw found");
        trace!("Expanding BoolFlaw {} with expr: {}", flw_id, self.expr);

        let mut candidates = Vec::with_capacity(2);
        if smt.get_lit_val(phi) != Some(false) {
            let lit = slv.track_expr(&mut smt, &mut graph, &self.expr)?;
            if smt.get_lit_val(phi) != Some(false) {
                for val_lit in [lit, !lit] {
                    if smt.get_lit_val(val_lit) == Some(false) {
                        continue;
                    }
                    if smt.probe(&[phi, val_lit]).map_err(|_| SolverError::Inconsistent)? {
                        candidates.push(val_lit);
                    }
                    if smt.get_lit_val(phi) == Some(false) {
                        // ϕ is already false (as a consequence of `probe`), no need to continue checking candidates
                        candidates.clear();
                        break;
                    }
                }
            }
        }

        match candidates.len() {
            0 => {
                if phi == Lit::TRUE {
                    return Err(SolverError::Inconsistent);
                }
            }
            1 => {
                slv.add_resolver(&mut smt, &mut graph, phi, Box::new(BoolResolver::new(candidates[0])))?;
            }
            2 => {
                for val_lit in candidates {
                    let rho = smt.new_lit();
                    slv.add_resolver(&mut smt, &mut graph, rho, Box::new(BoolResolver::new(val_lit)))?;
                }
            }
            _ => unreachable!("BoolFlaw should have at most 2 candidates"),
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
    lit: Lit,
}

impl BoolResolver {
    fn new(lit: Lit) -> Self {
        Self { lit }
    }
}

impl Resolver for BoolResolver {
    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().expect("No current resolver found");
        // ρ → val_lit
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "val": self.lit.to_string(),
        })
    }
}
