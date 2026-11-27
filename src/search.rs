use crate::{
    SolverEvent,
    graph::{CausalGraph, FlawId, ResolverId},
};
use semitone::Lit;
use std::collections::HashSet;
use tokio::sync::broadcast;
use tracing::trace;

/// Mirrors the current SAT assignment of flaws and resolvers and maintains the active agenda.
pub(crate) struct SearchState {
    flaw_val: Vec<Option<bool>>,
    res_val: Vec<Option<bool>>,
    /// Active flaws (`flaw_val == Some(true)`) that do not yet have an active resolver.
    agenda: HashSet<FlawId>,
}

impl SearchState {
    pub(crate) fn new() -> Self {
        Self { flaw_val: Vec::new(), res_val: Vec::new(), agenda: HashSet::new() }
    }

    /// Registers a newly added flaw. Returns `true` if it entered the agenda.
    pub(crate) fn on_new_flaw(&mut self, id: FlawId, val: Option<bool>) -> bool {
        debug_assert_eq!(id.index(), self.flaw_val.len(), "SearchState flaws out of sync with CausalGraph");
        self.flaw_val.push(val);
        if val == Some(true) {
            self.agenda.insert(id);
            self.trace_agenda();
            true
        } else {
            false
        }
    }

    /// Registers a newly added resolver. Returns `true` if it immediately solved its parent flaw in the agenda.
    pub(crate) fn on_new_resolver(&mut self, id: ResolverId, flaw: FlawId, val: Option<bool>) -> bool {
        debug_assert_eq!(id.index(), self.res_val.len(), "SearchState resolvers out of sync with CausalGraph");
        self.res_val.push(val);
        if val == Some(true) && self.agenda.remove(&flaw) {
            self.trace_agenda();
            true
        } else {
            false
        }
    }

    /// Applies newly propagated SAT literals. Returns `true` if `H2` must be invalidated.
    #[cfg_attr(not(feature = "server"), allow(unused_variables))]
    pub(crate) fn propagate(&mut self, graph: &CausalGraph, lits: &[Lit], tx_event: &broadcast::Sender<SolverEvent>) -> bool {
        let mut h2_dirty = false;

        // 1. Update resolvers first so newly activated flaws with an already-active resolver are not added to the agenda.
        for &lit in lits {
            for &res_id in graph.resolvers_by_lit(lit) {
                self.res_val[res_id] = Some(true);
                h2_dirty = true;
                let flaw_id = graph.resolver(res_id).flaw;
                #[cfg(feature = "server")]
                let _ = tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: Some(true) });
                if self.agenda.remove(&flaw_id) {
                    self.trace_agenda();
                    #[cfg(feature = "server")]
                    let _ = tx_event.send(SolverEvent::SolvedFlaw { flaw_id });
                }
            }
            for &res_id in graph.resolvers_by_lit(!lit) {
                self.res_val[res_id] = Some(false);
                h2_dirty = true;
                #[cfg(feature = "server")]
                let _ = tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: Some(false) });
            }
        }

        // 2. Update flaws and synchronize the agenda.
        for &lit in lits {
            for &flw_id in graph.flaws_by_lit(lit) {
                self.flaw_val[flw_id] = Some(true);
                #[cfg(feature = "server")]
                let _ = tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: Some(true) });
                let has_active_res = graph.flaw(flw_id).resolvers.iter().any(|&r| self.res_val[r] == Some(true));
                if !has_active_res && self.agenda.insert(flw_id) {
                    self.trace_agenda();
                    #[cfg(feature = "server")]
                    let _ = tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                }
            }
            for &flw_id in graph.flaws_by_lit(!lit) {
                self.flaw_val[flw_id] = Some(false);
                h2_dirty = true;
                #[cfg(feature = "server")]
                let _ = tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: Some(false) });
                if self.agenda.remove(&flw_id) {
                    self.trace_agenda();
                    #[cfg(feature = "server")]
                    let _ = tx_event.send(SolverEvent::SolvedFlaw { flaw_id: flw_id });
                }
            }
        }

        h2_dirty
    }

    /// Undoes SAT literals on backtrack. Returns `true` if `H2` must be invalidated.
    #[cfg_attr(not(feature = "server"), allow(unused_variables))]
    pub(crate) fn cancel_until(&mut self, graph: &CausalGraph, lits: &[Lit], tx_event: &broadcast::Sender<SolverEvent>) -> bool {
        if lits.is_empty() {
            return false;
        }
        let mut h2_dirty = false;

        // 1. Undo flaws first so resolvers undone in step 2 do not spuriously re-add deactivated flaws to the agenda.
        for &lit in lits {
            for &flw_id in graph.flaws_by_lit(lit) {
                self.flaw_val[flw_id] = None;
                #[cfg(feature = "server")]
                let _ = tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: None });
                if self.agenda.remove(&flw_id) {
                    self.trace_agenda();
                    #[cfg(feature = "server")]
                    let _ = tx_event.send(SolverEvent::SolvedFlaw { flaw_id: flw_id });
                }
            }
            for &flw_id in graph.flaws_by_lit(!lit) {
                self.flaw_val[flw_id] = None;
                h2_dirty = true;
                #[cfg(feature = "server")]
                let _ = tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: None });
            }
        }

        // 2. Undo resolvers and re-open active flaws that lost their active resolver.
        for &lit in lits {
            for &res_id in graph.resolvers_by_lit(lit) {
                self.res_val[res_id] = None;
                h2_dirty = true;
                #[cfg(feature = "server")]
                let _ = tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: None });
                let flw_id = graph.resolver(res_id).flaw;
                if self.flaw_val[flw_id] == Some(true) && !graph.flaw(flw_id).resolvers.iter().any(|&r| self.res_val[r] == Some(true)) && self.agenda.insert(flw_id) {
                    self.trace_agenda();
                    #[cfg(feature = "server")]
                    let _ = tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                }
            }
            for &res_id in graph.resolvers_by_lit(!lit) {
                self.res_val[res_id] = None;
                h2_dirty = true;
                #[cfg(feature = "server")]
                let _ = tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: None });
            }
        }

        h2_dirty
    }

    #[inline]
    pub(crate) fn flaw_val(&self, id: FlawId) -> Option<bool> {
        self.flaw_val[id]
    }

    #[inline]
    pub(crate) fn res_val(&self, id: ResolverId) -> Option<bool> {
        self.res_val[id]
    }

    #[inline]
    pub(crate) fn agenda(&self) -> &HashSet<FlawId> {
        &self.agenda
    }

    /// Returns `true` if `r`, its parent flaw, and its optional causal-link target are all not `false`.
    #[inline]
    pub(crate) fn is_resolver_alive(&self, graph: &CausalGraph, r: ResolverId) -> bool {
        let data = graph.resolver(r);
        if self.res_val[r] == Some(false) || self.flaw_val[data.flaw] == Some(false) {
            return false;
        }
        if let Some(target) = data.causal_link {
            let target_data = graph.resolver(target);
            if self.res_val[target] == Some(false) || self.flaw_val[target_data.flaw] == Some(false) {
                return false;
            }
        }
        true
    }

    /// Returns `true` if any queued frontier flaw has been forced to `true`.
    pub(crate) fn has_active_frontier(&self, graph: &CausalGraph) -> bool {
        graph.frontier().iter().any(|&f| self.flaw_val[f] == Some(true))
    }

    /// Returns the first unassigned frontier flaw and its `phi` literal (to branch on `!phi`).
    pub(crate) fn next_unassigned_frontier_phi(&self, graph: &CausalGraph) -> Option<(FlawId, Lit)> {
        graph.frontier().iter().copied().find(|&f| self.flaw_val[f].is_none()).map(|f| (f, graph.flaw(f).phi))
    }

    /// Returns distinct `phi` literals (in BFS order) of all queued frontier flaws touched by the current search.
    pub(crate) fn conflict_frontier_phis(&self, graph: &CausalGraph) -> Vec<Lit> {
        let mut seen = HashSet::new();
        let mut phis = Vec::new();
        for &f in graph.frontier() {
            if self.flaw_val[f].is_some() {
                let phi = graph.flaw(f).phi;
                if seen.insert(phi) {
                    phis.push(phi);
                }
            }
        }
        phis
    }

    fn trace_agenda(&self) {
        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
    }
}
