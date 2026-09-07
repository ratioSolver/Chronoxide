use crate::{SolverError, SolverEvent, SolverState};
use riddle::env::AtomId;
use semitone::Lit;
use serde_json::Value;
use std::collections::{HashMap, HashSet, VecDeque};
use tokio::sync::broadcast;
use tracing::trace;

pub type FlawId = usize;
pub type ResolverId = usize;

pub(super) struct Graph {
    flaws: Vec<Option<Box<dyn Flaw>>>,
    resolvers: Vec<Option<Box<dyn Resolver>>>,
    pub(super) lit_to_flaw: HashMap<usize, Vec<FlawId>>,
    pub(super) lit_to_resolver: HashMap<usize, Vec<ResolverId>>,
    pub(super) flaw_q: VecDeque<FlawId>,
    pub(super) atom_to_flaw: HashMap<AtomId, FlawId>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl Graph {
    pub(super) fn new(tx_event: broadcast::Sender<SolverEvent>) -> Self {
        Graph {
            flaws: Vec::new(),
            resolvers: Vec::new(),
            lit_to_flaw: HashMap::new(),
            lit_to_resolver: HashMap::new(),
            flaw_q: VecDeque::new(),
            atom_to_flaw: HashMap::new(),
            tx_event,
        }
    }

    pub(super) fn get_flaw(&self, id: FlawId) -> &dyn Flaw {
        self.flaws[id].as_ref().unwrap().as_ref()
    }

    pub(super) fn get_flaw_mut(&mut self, id: FlawId) -> &mut dyn Flaw {
        self.flaws[id].as_mut().unwrap().as_mut()
    }

    pub(super) fn add_flaw(&mut self, mut flaw: Box<dyn Flaw>) -> FlawId {
        let id = self.flaws.len();
        flaw.set_id(id);

        trace!("Adding flaw: f{} ({})", flaw.id(), flaw.phi());
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id: id,
            phi: flaw.phi().to_string(),
            causes: flaw.causes().to_vec(),
            supports: flaw.supports().to_vec(),
            status: flaw.status(),
            cost: flaw.estimated_cost(),
            data: flaw.to_json(),
        });

        self.lit_to_flaw.entry(flaw.phi().var()).or_default().push(id);
        self.flaws.push(Some(flaw));
        self.flaw_q.push_back(id);
        id
    }

    pub(super) fn set_flaw_status(&mut self, flaw_id: FlawId, status: Option<bool>) {
        trace!(
            "Flaw f{} is {}",
            flaw_id,
            match status {
                Some(true) => "active",
                Some(false) => "inactive",
                None => "unknown",
            }
        );
        let flaw = self.get_flaw_mut(flaw_id);
        flaw.set_status(status);
        let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id, status });
    }

    pub(super) fn set_flaw_estimated_cost(&mut self, flaw_id: FlawId, cost: f64) {
        let flaw = self.get_flaw_mut(flaw_id);
        trace!("Flaw f{} cost {} -> {}", flaw_id, flaw.estimated_cost(), cost);
        flaw.set_estimated_cost(cost);
        let _ = self.tx_event.send(SolverEvent::FlawCostUpdate { flaw_id, cost });
    }

    pub(super) fn take_flaw(&mut self, id: FlawId) -> Box<dyn Flaw> {
        self.flaws[id].take().expect("Flaw already taken or missing!")
    }

    pub(super) fn return_flaw(&mut self, id: FlawId, flaw: Box<dyn Flaw>) {
        self.flaws[id] = Some(flaw);
    }

    pub(super) fn get_resolver(&self, id: ResolverId) -> &dyn Resolver {
        self.resolvers[id].as_ref().unwrap().as_ref()
    }

    pub(super) fn get_resolver_mut(&mut self, id: ResolverId) -> &mut dyn Resolver {
        self.resolvers[id].as_mut().unwrap().as_mut()
    }

    pub(super) fn add_resolver(&mut self, mut resolver: Box<dyn Resolver>) -> ResolverId {
        let id = self.resolvers.len();
        resolver.set_id(id);

        trace!("Adding resolver: r{} ({}) for flaw f{}", resolver.id(), resolver.rho(), resolver.flaw());
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: id,
            flaw_id: resolver.flaw(),
            rho: resolver.rho().to_string(),
            status: resolver.status(),
            intrinsic_cost: resolver.intrinsic_cost(),
            sub_flaws: resolver.sub_flaws().to_vec(),
            data: resolver.to_json(),
        });

        self.lit_to_resolver.entry(resolver.rho().var()).or_default().push(id);
        self.resolvers.push(Some(resolver));
        id
    }

    pub(super) fn set_resolver_status(&mut self, resolver_id: ResolverId, status: Option<bool>) {
        trace!(
            "Resolver r{} is {}",
            resolver_id,
            match status {
                Some(true) => "active",
                Some(false) => "inactive",
                None => "unknown",
            }
        );
        let resolver = self.get_resolver_mut(resolver_id);
        resolver.set_status(status);
        let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id, status });
    }

    pub(super) fn take_resolver(&mut self, id: ResolverId) -> Box<dyn Resolver> {
        self.resolvers[id].take().expect("Resolver already taken or missing!")
    }

    pub(super) fn return_resolver(&mut self, id: ResolverId, resolver: Box<dyn Resolver>) {
        self.resolvers[id] = Some(resolver);
    }

    pub(super) fn propagate_costs<F>(&mut self, start_flaws: Vec<FlawId>, is_valid: F)
    where
        F: Fn(Lit) -> bool,
    {
        let mut queue: VecDeque<FlawId> = start_flaws.into_iter().collect();
        let mut in_queue: HashSet<FlawId> = queue.iter().copied().collect();
        while let Some(flaw_id) = queue.pop_front() {
            in_queue.remove(&flaw_id);

            let (phi, resolver_ids, old_cost, supports) = {
                let flaw = self.get_flaw(flaw_id);
                (flaw.phi(), flaw.resolvers().to_vec(), flaw.estimated_cost(), flaw.supports().to_vec())
            };

            let mut current_cost = f64::INFINITY;

            if is_valid(phi) {
                for res_id in resolver_ids {
                    let resolver = self.get_resolver(res_id);
                    if is_valid(resolver.rho()) {
                        let resolver_cost = self.get_resolver_estimated_cost(res_id);
                        if resolver_cost < current_cost {
                            current_cost = resolver_cost;
                        }
                    }
                }
            }

            if (current_cost - old_cost).abs() > f64::EPSILON {
                self.set_flaw_estimated_cost(flaw_id, current_cost);

                for support_id in supports {
                    let parent_flaw_id = self.get_resolver(support_id).flaw();
                    if in_queue.insert(parent_flaw_id) {
                        queue.push_back(parent_flaw_id);
                    }
                }
            }
        }
    }

    pub(super) fn get_resolver_estimated_cost(&self, id: ResolverId) -> f64 {
        let resolver = self.get_resolver(id);
        let max_sub_flaws_cost = resolver.sub_flaws().iter().map(|&sub_id| self.get_flaw(sub_id).estimated_cost()).fold(0.0_f64, f64::max);
        resolver.intrinsic_cost() + max_sub_flaws_cost
    }

    pub(crate) fn get_causal_ancestor_atoms(&self, start_resolver_id: ResolverId) -> HashSet<riddle::env::AtomId> {
        let mut ancestor_atoms = HashSet::new();
        let mut current_resolver = Some(start_resolver_id);

        while let Some(res_id) = current_resolver {
            let resolver = self.get_resolver(res_id);
            let parent_flaw_id = resolver.flaw();
            let flaw = self.get_flaw(parent_flaw_id);

            if let Some(atom_id) = flaw.atom_id() {
                ancestor_atoms.insert(atom_id);
            }

            current_resolver = flaw.causes().first().copied();
        }

        ancestor_atoms
    }
}

pub trait Flaw {
    fn id(&self) -> FlawId;
    fn set_id(&mut self, id: FlawId);

    fn phi(&self) -> Lit;
    fn status(&self) -> Option<bool>;
    fn set_status(&mut self, status: Option<bool>);

    fn causes(&self) -> &[ResolverId];
    fn supports(&self) -> &[ResolverId] {
        self.causes()
    }
    fn add_support(&mut self, _id: ResolverId) {
        unreachable!("This flaw type does not support adding supports.");
    }

    fn atom_id(&self) -> Option<AtomId> {
        None
    }

    fn is_expanded(&self) -> bool;
    fn expand(&mut self, core: &SolverState) -> Result<Vec<Box<dyn Resolver>>, SolverError>;

    fn resolvers(&self) -> &[ResolverId];
    fn add_resolver(&mut self, id: ResolverId);

    fn estimated_cost(&self) -> f64;
    fn set_estimated_cost(&mut self, cost: f64);

    fn to_json(&self) -> Value;
}

pub trait Resolver {
    fn id(&self) -> ResolverId;
    fn set_id(&mut self, id: ResolverId);

    fn rho(&self) -> Lit;
    fn status(&self) -> Option<bool>;
    fn set_status(&mut self, status: Option<bool>);

    fn flaw(&self) -> FlawId;

    fn intrinsic_cost(&self) -> f64;

    fn apply(&mut self, core: &SolverState) -> Result<(), SolverError>;

    fn sub_flaws(&self) -> &[FlawId];
    fn add_sub_flaw(&mut self, id: FlawId) {
        unreachable!("This resolver type does not support adding sub-flaws.");
    }

    fn to_json(&self) -> Value;
}
