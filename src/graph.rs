use std::collections::HashMap;

use crate::{
    SolverEvent,
    flaws::{Flaw, FlawId, Resolver, ResolverId},
};
use semitone::Lit;
use tokio::sync::broadcast;

pub struct Graph {
    flaws: Vec<Option<Box<dyn Flaw>>>,
    resolvers: Vec<Option<Box<dyn Resolver>>>,
    c_flaw: Option<(FlawId, Lit)>,
    c_res: Option<(ResolverId, Lit)>,

    lit_to_flaws: HashMap<Lit, Vec<FlawId>>,
    flaw_status: Vec<Option<bool>>,
    flaw_phi: Vec<Lit>,

    lit_to_resolvers: HashMap<Lit, Vec<ResolverId>>,
    resolver_status: Vec<Option<bool>>,
    resolver_rho: Vec<Lit>,

    tx_event: broadcast::Sender<SolverEvent>,
}

impl Graph {
    pub(super) fn new(tx_event: broadcast::Sender<SolverEvent>) -> Self {
        Self {
            flaws: Vec::new(),
            resolvers: Vec::new(),
            c_flaw: None,
            c_res: None,

            lit_to_flaws: HashMap::new(),
            flaw_status: Vec::new(),
            flaw_phi: Vec::new(),

            lit_to_resolvers: HashMap::new(),
            resolver_status: Vec::new(),
            resolver_rho: Vec::new(),

            tx_event,
        }
    }

    pub(super) fn current_flaw(&self) -> Option<(FlawId, Lit)> {
        self.c_flaw
    }

    pub(super) fn current_resolver(&self) -> Option<(ResolverId, Lit)> {
        self.c_res
    }

    /// Returns the currently active resolver as a cause vector (empty if at root level).
    pub(super) fn current_causes(&self) -> Vec<ResolverId> {
        self.c_res.map(|(r_id, _)| vec![r_id]).unwrap_or_default()
    }

    /// Returns the ϕ literal of the given flaw.
    pub(super) fn phi(&self, flw_id: FlawId) -> Lit {
        self.flaw_phi[flw_id]
    }

    pub(super) fn take_flaw(&mut self, flw_id: FlawId) -> Option<Box<dyn Flaw>> {
        self.c_flaw.replace((flw_id, self.flaw_phi[flw_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));
        self.flaws[flw_id].take()
    }

    pub(super) fn return_flaw(&mut self, flw: Box<dyn Flaw>) {
        let (flw_id, _) = self.c_flaw.take().expect("A flaw must be checked out when calling return_flaw");
        self.flaws[flw_id] = Some(flw);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
    }

    /// Returns the ρ literal of the given resolver.
    pub(super) fn rho(&self, res_id: ResolverId) -> Lit {
        self.resolver_rho[res_id]
    }

    /// Returns the ρ literals of the given resolvers.
    pub(super) fn rhos(&self, res_ids: &[ResolverId]) -> Vec<Lit> {
        res_ids.iter().map(|&r_id| self.resolver_rho[r_id]).collect()
    }

    pub(super) fn take_resolver(&mut self, res_id: ResolverId) -> Option<Box<dyn Resolver>> {
        self.c_res.replace((res_id, self.resolver_rho[res_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(res_id)));
        self.resolvers[res_id].take()
    }

    pub(super) fn return_resolver(&mut self, res: Box<dyn Resolver>) {
        let (res_id, _) = self.c_res.take().expect("A resolver must be checked out when calling return_resolver");
        self.resolvers[res_id] = Some(res);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
    }
}
