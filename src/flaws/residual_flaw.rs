use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::Lit;
use serde_json::{Value, json};
use tracing::trace;

/// A flaw representing `target_flaw` deprived of `excluded_resolver` due to a mutex conflict.
pub(crate) struct ResidualFlaw {
    target_flaw: FlawId,
    excluded_resolver: ResolverId,
    allowed_resolvers: Vec<ResolverId>,
}

impl ResidualFlaw {
    pub(crate) fn new(target_flaw: FlawId, excluded_resolver: ResolverId, allowed_resolvers: Vec<ResolverId>) -> Self {
        Self { target_flaw, excluded_resolver, allowed_resolvers }
    }
}

impl Flaw for ResidualFlaw {
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().ok_or_else(|| SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding ResidualFlaw {} (target {}, excluding {})", flw_id, self.target_flaw, self.excluded_resolver);

        let candidates: Vec<(ResolverId, Lit, Vec<FlawId>)> = self.allowed_resolvers.iter().copied().filter(|&r| graph.resolver_status(r) != Some(false)).map(|r| (r, graph.rho(r), graph.resolver_preconditions(r).to_vec())).collect();

        let single = candidates.len() == 1;
        for (orig_res_id, orig_rho, orig_preconditions) in candidates {
            let rho = if single { phi } else { smt.new_lit() };
            if rho != phi {
                // (ϕ ∧ orig_rho) → ρ
                slv.add_clause(&mut smt, &mut graph, vec![!phi, !orig_rho, rho])?;
            }
            let proxy = Box::new(ResidualResolver::new(orig_res_id, orig_rho, orig_preconditions));
            slv.add_resolver(&mut smt, &mut graph, rho, proxy)?;
        }

        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "residual",
            "target_flaw": self.target_flaw.to_string(),
            "excluded_resolver": self.excluded_resolver.to_string()
        })
    }
}

/// A proxy resolver that delegates to an existing resolver's literal and preconditions.
struct ResidualResolver {
    original_resolver: ResolverId,
    orig_rho: Lit,
    target_preconditions: Vec<FlawId>,
}

impl ResidualResolver {
    fn new(original_resolver: ResolverId, orig_rho: Lit, target_preconditions: Vec<FlawId>) -> Self {
        Self { original_resolver, orig_rho, target_preconditions }
    }
}

impl Resolver for ResidualResolver {
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(0)
    }

    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or_else(|| SolverError::RuntimeError(String::from("No current resolver found")))?;
        // ρ → orig_rho
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.orig_rho])?;
        for &pre_flaw in &self.target_preconditions {
            slv.add_causal_link(&mut smt, &mut graph, pre_flaw)?;
        }
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "residual",
            "original_resolver": self.original_resolver.to_string()
        })
    }
}
