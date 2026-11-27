#[cfg(any(all(feature = "h_max", feature = "h_add"), all(feature = "h_max", feature = "h2"), all(feature = "h_add", feature = "h2"),))]
compile_error!("Features 'h_max', 'h_add', and 'h2' are mutually exclusive. Please enable only one of them.");

#[cfg(not(any(feature = "h_max", feature = "h_add", feature = "h2")))]
compile_error!("Please enable one of the heuristic features: 'h_max', 'h_add', or 'h2'.");

#[cfg(any(feature = "h_max", feature = "h_add"))]
mod h1;
#[cfg(feature = "h2")]
mod h2;

#[cfg(feature = "h_max")]
pub(crate) type ActiveHeuristic = h1::HMax;
#[cfg(feature = "h_add")]
pub(crate) type ActiveHeuristic = h1::HAdd;
#[cfg(feature = "h2")]
pub(crate) type ActiveHeuristic = h2::H2;

use crate::{
    graph::{CausalGraph, FlawId, ResolverId},
    mutex::MutexTable,
    search::SearchState,
};
use semitone::Lit;
use std::collections::HashSet;

pub(crate) trait Heuristic {
    /// Creates a new heuristic instance.
    fn new() -> Self;

    /// Marks cached heuristic estimates as stale.
    fn invalidate(&mut self);

    /// Recomputes heuristic estimates if invalidated.
    /// When the `server` feature is enabled, returns `(flaw_id, new_cost)` pairs whose single-flaw cost changed.
    fn ensure_fresh(&mut self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> Vec<(FlawId, f64)>;

    /// Returns the estimated cost of solving `flw`. Requires `ensure_fresh` to have been called.
    fn flaw_cost(&self, flw: FlawId) -> f64;

    /// Returns `true` if `res` currently has a finite estimated cost. Requires `ensure_fresh` to have been called.
    fn is_resolver_finite(&self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState, res: ResolverId) -> bool;

    /// Graph construction termination criterion: returns `true` if the current agenda has a finite estimated solution.
    fn has_estimated_solution(&self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> bool;

    /// Selects the next frontier `phi` literal to expand at decision level 0.
    fn pick_phi_to_expand(&self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> Option<Lit>;

    /// Selects the next `(flaw, resolver)` branching pair from the active agenda.
    fn pick_branch(&self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> Option<(FlawId, ResolverId)>;
}

#[inline]
pub(crate) fn norm_flaw_pair(f1: FlawId, f2: FlawId) -> (FlawId, FlawId) {
    if f1 <= f2 { (f1, f2) } else { (f2, f1) }
}

#[inline]
pub(crate) fn norm_res_pair(r1: ResolverId, r2: ResolverId) -> (ResolverId, ResolverId) {
    if r1 <= r2 { (r1, r2) } else { (r2, r1) }
}

/// Collects unassigned, alive, finite-cost resolvers whose parent `phi`-group is fully expanded.
/// Used as unary probe candidates.
pub(crate) fn finite_probe_resolvers<H: Heuristic>(h: &H, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> Vec<ResolverId> {
    let mut out = Vec::new();
    for r in graph.resolver_ids() {
        let data = graph.resolver(r);
        if search.res_val(r).is_some() || !search.is_resolver_alive(graph, r) {
            continue;
        }
        if !graph.is_phi_fully_expanded(graph.flaw(data.flaw).phi) {
            continue;
        }
        if h.is_resolver_finite(graph, mutex, search, r) {
            out.push(r);
        }
    }
    out
}

/// Collects non-mutex, alive, finite-cost resolver pairs across:
/// 1) distinct flaws currently in the agenda, and
/// 2) sibling preconditions of any alive, finite-cost, non-linked resolver.
///
/// Only includes resolvers whose parent `phi`-group is fully expanded.
pub(crate) fn finite_probe_pairs<H: Heuristic>(h: &H, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> Vec<(ResolverId, ResolverId)> {
    let mut flaw_pairs: HashSet<(FlawId, FlawId)> = HashSet::new();

    let agenda: Vec<FlawId> = search.agenda().iter().copied().collect();
    for (i, &f1) in agenda.iter().enumerate() {
        for &f2 in &agenda[(i + 1)..] {
            flaw_pairs.insert(norm_flaw_pair(f1, f2));
        }
    }

    for r in graph.resolver_ids() {
        let data = graph.resolver(r);
        if data.causal_link.is_some() || data.preconditions.len() < 2 || !search.is_resolver_alive(graph, r) {
            continue;
        }
        if !h.is_resolver_finite(graph, mutex, search, r) {
            continue;
        }
        for (i, &p1) in data.preconditions.iter().enumerate() {
            for &p2 in &data.preconditions[(i + 1)..] {
                flaw_pairs.insert(norm_flaw_pair(p1, p2));
            }
        }
    }

    let mut pairs = Vec::new();
    let mut seen = HashSet::new();

    for (f1, f2) in flaw_pairs {
        if !graph.is_phi_fully_expanded(graph.flaw(f1).phi) || !graph.is_phi_fully_expanded(graph.flaw(f2).phi) {
            continue;
        }
        for &r1 in &graph.flaw(f1).resolvers {
            if !search.is_resolver_alive(graph, r1) || !h.is_resolver_finite(graph, mutex, search, r1) {
                continue;
            }
            for &r2 in &graph.flaw(f2).resolvers {
                if !search.is_resolver_alive(graph, r2) || mutex.is_res_mutex(r1, r2) || !h.is_resolver_finite(graph, mutex, search, r2) {
                    continue;
                }
                if graph.resolver(r1).rho == graph.resolver(r2).rho {
                    continue;
                }
                if search.res_val(r1) == Some(true) && search.res_val(r2) == Some(true) {
                    continue;
                }
                let key = norm_res_pair(r1, r2);
                if seen.insert(key) {
                    pairs.push(key);
                }
            }
        }
    }

    pairs
}
