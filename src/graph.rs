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

            lit_to_flaws: HashMap::new(),
            flaw_status: Vec::new(),
            flaw_phi: Vec::new(),

            lit_to_resolvers: HashMap::new(),
            resolver_status: Vec::new(),
            resolver_rho: Vec::new(),

            tx_event,
        }
    }

    /// Returns the ρ literals of the given resolvers, used by the caller to build a flaw's causes clause.
    pub(super) fn resolver_rhos(&self, res_ids: &[ResolverId]) -> Vec<Lit> {
        res_ids.iter().map(|&r_id| self.resolver_rho[*r_id]).collect()
    }
}
