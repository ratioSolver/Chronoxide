use crate::{
    SolverError, SolverState,
    graph::{FlawId, Resolver, ResolverId},
};
use semitone::Lit;
use serde_json::Value;
use std::rc::Rc;

pub(super) mod atom_flaw;
pub(super) mod clause_flaw;
pub(super) mod disjunction_flaw;
pub(super) mod enum_flaw;

/// Adds one resolver per candidate. With 0 candidates and ϕ = ⊤ the problem is inconsistent;
/// with a single candidate the resolver reuses ϕ as its literal.
pub(super) fn add_lit_candidates<T>(slv: &SolverState, flw_id: FlawId, phi: Lit, candidates: Vec<(Lit, T)>, mk: impl Fn(Lit, T) -> Rc<dyn Resolver>) -> Result<(), SolverError> {
    match candidates.len() {
        0 if phi == Lit::TRUE => Err(SolverError::Inconsistent),
        0 => Ok(()),
        1 => {
            let (lit, payload) = candidates.into_iter().next().expect("length checked");
            slv.add_resolver(flw_id, phi, mk(lit, payload)).map(|_| ())
        }
        _ => {
            for (lit, payload) in candidates {
                let rho = slv.new_lit();
                slv.add_resolver(flw_id, rho, mk(lit, payload))?;
            }
            Ok(())
        }
    }
}

/// Generic literal resolver (`ρ → lit`). Used by clauses, enums, and timeline peaks/levels.
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
    fn apply(&self, slv: &SolverState, res_id: ResolverId) -> Result<(), SolverError> {
        let rho = slv.resolver_rho(res_id);
        if self.lit == Lit::TRUE || self.lit == rho {
            return Ok(());
        }
        // ρ → lit
        slv.add_clause(vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        self.json.clone()
    }
}
