use crate::{
    SolverError, SolverState,
    graph::{Graph, Resolver},
};
use semitone::{Lit, SeMiTONE};
use serde_json::Value;

pub(super) mod atom_flaw;
pub(super) mod clause_flaw;
pub(super) mod disjunction_flaw;
pub(super) mod enum_flaw;

/// Adds one resolver per candidate. With 0 candidates and ϕ = ⊤ the problem is inconsistent;
/// with a single candidate the resolver reuses ϕ as its literal.
pub(super) fn add_lit_candidates<T>(slv: &SolverState, smt: &mut SeMiTONE, graph: &mut Graph, phi: Lit, candidates: Vec<(Lit, T)>, mk: impl Fn(Lit, T) -> Box<dyn Resolver>) -> Result<(), SolverError> {
    match candidates.len() {
        0 if phi == Lit::TRUE => Err(SolverError::Inconsistent),
        0 => Ok(()),
        1 => {
            let (lit, payload) = candidates.into_iter().next().expect("length checked");
            slv.add_resolver(smt, graph, phi, mk(lit, payload)).map(|_| ())
        }
        _ => {
            for (lit, payload) in candidates {
                let rho = smt.new_lit();
                slv.add_resolver(smt, graph, rho, mk(lit, payload))?;
            }
            Ok(())
        }
    }
}

/// ρ → lit. Replaces BoolResolver, ClauseResolver, EnumResolver, Order and Displace.
pub(super) struct LitResolver {
    lit: Lit,
    json: Value,
}

impl LitResolver {
    pub(super) fn new(lit: Lit, json: Value) -> Self {
        Self { lit, json }
    }
}

impl Resolver for LitResolver {
    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or_else(|| SolverError::RuntimeError(String::from("No current resolver found")))?;
        // ρ → lit
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        self.json.clone()
    }
}
