use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
};
use semitone::{Lit, ast::BoolExpr};
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
                    candidates.push(lit);
                }
                if smt.get_lit_val(phi) == Some(false) {
                    // ϕ is already false (as a consequence of `probe`), no need to continue checking candidates
                    candidates.clear();
                    break;
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
                slv.add_resolver(&mut smt, &mut graph, phi, Box::new(ClauseResolver::new(candidates[0])))?;
            }
            _ => {
                for val_lit in candidates {
                    let rho = smt.new_lit();
                    slv.add_resolver(&mut smt, &mut graph, rho, Box::new(ClauseResolver::new(val_lit)))?;
                }
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

struct ClauseResolver {
    lit: Lit,
}

impl ClauseResolver {
    pub(crate) fn new(lit: Lit) -> Self {
        Self { lit }
    }
}

impl Resolver for ClauseResolver {
    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().expect("No current resolver found");
        // ρ → lit
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "val": self.lit.to_string(),
        })
    }
}
