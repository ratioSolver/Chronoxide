use crate::{SolverError, SolverEvent, SolverState};
use semitone::{DlVar, Lit};
use serde_json::Value;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    ops::{Index, IndexMut},
};
use tokio::sync::broadcast;
use tracing::trace;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct FlawId(usize);

impl<T> Index<FlawId> for Vec<T> {
    type Output = T;
    fn index(&self, flw: FlawId) -> &Self::Output {
        &self[flw.0]
    }
}

impl<T> IndexMut<FlawId> for Vec<T> {
    fn index_mut(&mut self, flw: FlawId) -> &mut Self::Output {
        &mut self[flw.0]
    }
}

impl fmt::Display for FlawId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ϕ{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ResolverId(usize);

impl<T> Index<ResolverId> for Vec<T> {
    type Output = T;
    fn index(&self, res: ResolverId) -> &Self::Output {
        &self[res.0]
    }
}

impl<T> IndexMut<ResolverId> for Vec<T> {
    fn index_mut(&mut self, res: ResolverId) -> &mut Self::Output {
        &mut self[res.0]
    }
}

impl fmt::Display for ResolverId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ρ{}", self.0)
    }
}

pub trait Flaw {
    /// Expands this flaw by adding resolvers to the graph that can potentially solve it.
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError>;

    /// Serializes the domain-specific payload of this flaw to JSON.
    fn to_json(&self) -> Value;
}

pub trait Resolver {
    /// The intrinsic cost of selecting this resolver, independent from the current state of the graph.
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(1)
    }

    /// Applies this resolver, adding its constraints, sub-flaws, or causal links to the solver state.
    fn apply(&self, _slv: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    /// Serializes the domain-specific payload of this resolver to JSON.
    fn to_json(&self) -> Value {
        Value::Null
    }
}

pub struct Graph {
    flaws: Vec<Option<Box<dyn Flaw>>>,
    resolvers: Vec<Option<Box<dyn Resolver>>>,
    c_flaw: Option<(FlawId, Lit)>,
    c_res: Option<(ResolverId, Lit)>,

    lit_to_flaws: HashMap<Lit, Vec<FlawId>>,
    flaw_status: Vec<Option<bool>>,
    flaw_phi: Vec<Lit>,
    flaw_cost_var: Vec<DlVar>,
    flaw_causes: Vec<Vec<ResolverId>>,
    flaw_required_by: Vec<Vec<ResolverId>>,
    flaw_resolvers: Vec<Vec<ResolverId>>,
    flaw_cost: Vec<f64>,

    lit_to_resolvers: HashMap<Lit, Vec<ResolverId>>,
    resolver_status: Vec<Option<bool>>,
    resolver_rho: Vec<Lit>,
    resolver_cost_var: Vec<DlVar>,
    resolver_flaw: Vec<FlawId>,
    resolver_preconditions: Vec<Vec<FlawId>>,

    trail: Vec<(FlawId, f64)>,

    flaw_q: VecDeque<FlawId>,
    trail_lim: Vec<usize>,
    agenda: HashSet<FlawId>,

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
            flaw_cost_var: Vec::new(),
            flaw_causes: Vec::new(),
            flaw_required_by: Vec::new(),
            flaw_resolvers: Vec::new(),
            flaw_cost: Vec::new(),

            lit_to_resolvers: HashMap::new(),
            resolver_status: Vec::new(),
            resolver_rho: Vec::new(),
            resolver_cost_var: Vec::new(),
            resolver_flaw: Vec::new(),
            resolver_preconditions: Vec::new(),

            trail: Vec::new(),

            flaw_q: VecDeque::new(),
            trail_lim: Vec::new(),
            agenda: HashSet::new(),

            tx_event,
        }
    }

    /// Returns the currently processing flaw and its ϕ literal, if any.
    pub(super) fn current_flaw(&self) -> Option<(FlawId, Lit)> {
        self.c_flaw
    }

    /// Returns the currently processing resolver and its ρ literal, if any.
    pub(super) fn current_resolver(&self) -> Option<(ResolverId, Lit)> {
        self.c_res
    }

    /// Returns the currently active resolver as a cause vector (empty if at root level).
    pub(super) fn current_causes(&self) -> Vec<ResolverId> {
        self.c_res.map(|(r_id, _)| vec![r_id]).unwrap_or_default()
    }

    /// Adds a new flaw to the graph, returning its FlawId.
    pub fn add_flaw(&mut self, causes: Vec<ResolverId>, phi: Lit, status: Option<bool>, cost_var: DlVar, flw: Box<dyn Flaw>) -> FlawId {
        let flw_id = FlawId(self.flaws.len());
        trace!("Adding flaw: {} ({})", flw_id, phi);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id: flw_id,
            phi: phi.to_string(),
            causes: causes.clone(),
            required_by: causes.clone(),
            status,
            cost: f64::INFINITY,
            data: flw.to_json(),
        });

        self.flaws.push(Some(flw));
        self.flaw_phi.push(phi);
        self.flaw_status.push(status);
        if status == Some(true) {
            self.agenda.insert(flw_id);
            trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
        }
        self.flaw_cost_var.push(cost_var);
        for &cause in &causes {
            self.resolver_preconditions[cause].push(flw_id);
        }
        self.flaw_causes.push(causes.clone());
        self.flaw_required_by.push(causes);
        self.flaw_resolvers.push(Vec::new());
        self.flaw_cost.push(f64::INFINITY);

        self.lit_to_flaws.entry(phi).or_default().push(flw_id);

        self.flaw_q.push_back(flw_id);

        flw_id
    }

    /// Returns the status of the given flaw, if known.
    pub(super) fn flaw_status(&self, flw_id: FlawId) -> Option<bool> {
        self.flaw_status[flw_id]
    }

    /// Returns the ϕ literal of the given flaw.
    pub(super) fn phi(&self, flw_id: FlawId) -> Lit {
        self.flaw_phi[flw_id]
    }

    /// Returns the ϕ literals of the given flaws.
    pub(super) fn phis(&self, flw_ids: &[FlawId]) -> Vec<Lit> {
        flw_ids.iter().map(|&f_id| self.flaw_phi[f_id]).collect()
    }

    /// Returns the cost variable of the given flaw.
    pub(super) fn flaw_cost_var(&self, flw_id: FlawId) -> DlVar {
        self.flaw_cost_var[flw_id]
    }

    /// Returns the causes of the given flaw.
    pub(super) fn flaw_causes(&self, flw_id: FlawId) -> &[ResolverId] {
        &self.flaw_causes[flw_id]
    }

    /// Returns the resolvers that require the given flaw.
    pub(super) fn flaw_required_by(&self, flw_id: FlawId) -> &[ResolverId] {
        &self.flaw_required_by[flw_id]
    }

    /// Returns the resolvers that can solve the given flaw.
    pub(super) fn flaw_resolvers(&self, flw_id: FlawId) -> &[ResolverId] {
        &self.flaw_resolvers[flw_id]
    }

    /// Returns the estimated cost of the given flaw.
    pub(super) fn flaw_cost(&self, flw_id: FlawId) -> f64 {
        self.flaw_cost[flw_id]
    }

    /// Returns whether the given flaw has been expanded (i.e., its resolvers have been added to the graph).
    pub(super) fn flaw_expanded(&self, flw_id: FlawId) -> bool {
        !self.flaw_q.contains(&flw_id)
    }

    /// Computes the estimated cost of the given flaw based on its resolvers and their preconditions.
    fn compute_flaw_cost(&self, flw_id: FlawId) -> f64 {
        if self.flaw_status[flw_id] == Some(false) {
            f64::INFINITY
        } else {
            let mut min_cost = f64::INFINITY;

            for &resolver_id in &self.flaw_resolvers[flw_id] {
                let resolver_cost = self.compute_resolver_cost(resolver_id);
                if resolver_cost < min_cost {
                    min_cost = resolver_cost;
                }
            }

            min_cost
        }
    }

    /// Takes the flaw out of the graph for processing.
    pub(super) fn take_flaw(&mut self, flw_id: FlawId) -> Option<Box<dyn Flaw>> {
        self.c_flaw.replace((flw_id, self.flaw_phi[flw_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));
        self.flaws[flw_id].take()
    }

    /// Returns the flaw to the graph after processing it.
    pub(super) fn return_flaw(&mut self, flw: Box<dyn Flaw>) {
        let (flw_id, _) = self.c_flaw.take().expect("A flaw must be currently being processed to return it");
        self.flaws[flw_id] = Some(flw);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
    }

    /// Adds a new resolver to the graph, returning its ResolverId.
    pub fn add_resolver(&mut self, rho: Lit, status: Option<bool>, cost: DlVar, res: Box<dyn Resolver>) -> ResolverId {
        let (flaw_id, _) = self.c_flaw.expect("Cannot add a resolver when no flaw is currently being processed");
        let res_id = ResolverId(self.resolvers.len());
        trace!("Adding resolver: {} ({}) for flaw {}", res_id, rho, flaw_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: res_id,
            flaw_id,
            rho: rho.to_string(),
            status,
            intrinsic_cost: res.intrinsic_cost().to_f64(),
            preconditions: Vec::new(),
            data: res.to_json(),
        });

        self.resolvers.push(Some(res));
        self.resolver_rho.push(rho);
        self.resolver_status.push(status);
        if status == Some(true) {
            self.agenda.remove(&flaw_id);
            trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id });
        }
        self.resolver_cost_var.push(cost);
        self.resolver_flaw.push(flaw_id);
        self.resolver_preconditions.push(Vec::new());
        self.flaw_resolvers[flaw_id].push(res_id);

        self.lit_to_resolvers.entry(rho).or_default().push(res_id);

        res_id
    }

    /// Returns the status of the given resolver, if known.
    pub(super) fn resolver_status(&self, res_id: ResolverId) -> Option<bool> {
        self.resolver_status[res_id]
    }

    /// Returns the ρ literal of the given resolver.
    pub(super) fn rho(&self, res_id: ResolverId) -> Lit {
        self.resolver_rho[res_id]
    }

    /// Returns the ρ literals of the given resolvers.
    pub(super) fn rhos(&self, res_ids: &[ResolverId]) -> Vec<Lit> {
        res_ids.iter().map(|&r_id| self.resolver_rho[r_id]).collect()
    }

    /// Returns the cost variable of the given resolver.
    pub(super) fn resolver_cost_var(&self, res_id: ResolverId) -> DlVar {
        self.resolver_cost_var[res_id]
    }

    /// Returns the flaw that the given resolver can solve.
    pub(super) fn resolver_flaw(&self, res_id: ResolverId) -> FlawId {
        self.resolver_flaw[res_id]
    }

    /// Returns the preconditions of the given resolver.
    pub(super) fn resolver_preconditions(&self, res_id: ResolverId) -> &[FlawId] {
        &self.resolver_preconditions[res_id]
    }

    /// Computes the estimated cost of the given resolver based on its intrinsic cost and the costs of its preconditions.
    fn compute_resolver_cost(&self, res_id: ResolverId) -> f64 {
        if self.resolver_status[res_id] == Some(false) {
            f64::INFINITY
        } else {
            #[cfg(feature = "h_add")]
            let precondition_cost: f64 = self.resolver_preconditions[res_id].iter().map(|&f_id| self.flaw_cost[f_id]).sum();
            #[cfg(feature = "h_max")]
            let precondition_cost: f64 = self.resolver_preconditions[res_id].iter().fold(0.0_f64, |acc, &f_id| acc.max(self.flaw_cost[f_id]));

            self.resolvers[res_id].as_ref().expect("Resolver should exist").intrinsic_cost().to_f64() + precondition_cost
        }
    }

    /// Takes the resolver out of the graph for processing.
    pub(super) fn take_resolver(&mut self, res_id: ResolverId) -> Option<Box<dyn Resolver>> {
        self.c_res.replace((res_id, self.resolver_rho[res_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(res_id)));
        self.resolvers[res_id].take()
    }

    /// Adds a causal link from the given flaw to the current resolver.
    pub(super) fn add_causal_link(&mut self, flw_id: FlawId) -> Result<(Lit, Lit), SolverError> {
        let phi = self.flaw_phi[flw_id];
        let (res_id, rho) = self.c_res.ok_or(SolverError::RuntimeError(String::from("No current resolver to add causal link from")))?;
        assert!(!self.flaw_required_by[flw_id].contains(&res_id), "Duplicate causal link between {} and {}", res_id, flw_id);
        self.flaw_required_by[flw_id].push(res_id);
        self.resolver_preconditions[res_id].push(flw_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewCausalLink { flaw_id: flw_id, resolver_id: res_id });

        Ok((rho, phi))
    }

    /// Returns the resolver to the graph after processing it.
    pub(super) fn return_resolver(&mut self, res: Box<dyn Resolver>) {
        let (res_id, _) = self.c_res.take().expect("A resolver must be currently being processed to return it");
        self.resolvers[res_id] = Some(res);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
    }

    pub(super) fn propagate(&mut self, lits: &[Lit]) {
        let mut affected_flaws = Vec::new();
        // 1. Update resolver status first so newly activated flaws with an already-active resolver are not spuriously added to the agenda.
        for &lit in lits {
            if let Some(res_ids) = self.lit_to_resolvers.get(&lit) {
                for &res_id in res_ids {
                    self.resolver_status[res_id] = Some(true);
                    let flaw_id = self.resolver_flaw[res_id];
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: Some(true) });
                    if self.agenda.remove(&flaw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id });
                    }
                }
            }
            if let Some(res_ids) = self.lit_to_resolvers.get(&!lit) {
                for &res_id in res_ids {
                    self.resolver_status[res_id] = Some(false);
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: Some(false) });
                    affected_flaws.push(self.resolver_flaw[res_id]);
                }
            }
        }
        // 2. Update flaw status and synchronize the agenda.
        for &lit in lits {
            if let Some(flw_ids) = self.lit_to_flaws.get(&lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[flw_id] = Some(true);
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: Some(true) });
                    if !self.flaw_resolvers[flw_id].iter().any(|&r| self.resolver_status[r] == Some(true)) && self.agenda.insert(flw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                    }
                }
            }
            if let Some(flw_ids) = self.lit_to_flaws.get(&!lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[flw_id] = Some(false);
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: Some(false) });
                    if self.agenda.remove(&flw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id: flw_id });
                    }
                    affected_flaws.push(flw_id);
                }
            }
        }

        self.propagate_costs(affected_flaws.as_slice());
    }

    pub(super) fn propagate_costs(&mut self, initial_flaws: &[FlawId]) {
        assert!(self.c_flaw.is_none(), "Cannot propagate while a flaw is being processed");
        assert!(self.c_res.is_none(), "Cannot propagate while a resolver is being processed");

        let n_flaws = self.flaws.len();
        let mut queue = VecDeque::new();
        let mut in_queue = vec![false; n_flaws];
        let mut updates = vec![0usize; n_flaws];

        for &f_id in initial_flaws {
            if !in_queue[f_id] {
                queue.push_back(f_id);
                in_queue[f_id] = true;
            }
        }

        while let Some(f_id) = queue.pop_front() {
            in_queue[f_id] = false;

            let old_cost = self.flaw_cost[f_id];
            let mut c_cost = self.compute_flaw_cost(f_id);

            if c_cost != old_cost {
                updates[f_id] += 1;
                if updates[f_id] > n_flaws {
                    c_cost = f64::INFINITY;
                }
            }

            if c_cost != old_cost {
                self.trail.push((f_id, old_cost));
                self.flaw_cost[f_id] = c_cost;
                #[cfg(feature = "server")]
                let _ = self.tx_event.send(SolverEvent::FlawCostUpdate { flaw_id: f_id, cost: c_cost });

                for &r_id in &self.flaw_required_by[f_id] {
                    let parent_flaw_id = self.resolver_flaw[r_id];
                    if !in_queue[parent_flaw_id] {
                        queue.push_back(parent_flaw_id);
                        in_queue[parent_flaw_id] = true;
                    }
                }
            }
        }
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    pub(super) fn cancel_until(&mut self, level: usize, lits: &[Lit]) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];
        while self.trail.len() > target_len {
            let (f, old_cost) = self.trail.pop().unwrap();
            self.flaw_cost[f] = old_cost;
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::FlawCostUpdate { flaw_id: f, cost: old_cost });
        }
        self.trail_lim.truncate(level);

        for &lit in lits {
            if let Some(flw_ids) = self.lit_to_flaws.get(&lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[flw_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: None });
                    if self.agenda.remove(&flw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id: flw_id });
                    }
                }
            }
            if let Some(flw_ids) = self.lit_to_flaws.get(&!lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[flw_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: None });
                }
            }
        }
        for &lit in lits {
            if let Some(res_ids) = self.lit_to_resolvers.get(&lit) {
                for &res_id in res_ids {
                    self.resolver_status[res_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: None });
                    let flw_id = self.resolver_flaw[res_id];
                    if self.flaw_status[flw_id] == Some(true) && !self.flaw_resolvers[flw_id].iter().any(|&r| self.resolver_status[r] == Some(true)) && self.agenda.insert(flw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                    }
                }
            }
            if let Some(res_ids) = self.lit_to_resolvers.get(&!lit) {
                for &res_id in res_ids {
                    self.resolver_status[res_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: None });
                }
            }
        }
    }

    pub(super) fn has_estimated_solution(&self) -> bool {
        for &f_id in &self.agenda {
            if self.flaw_status[f_id] == Some(true) && self.flaw_cost[f_id] == f64::INFINITY {
                return false;
            }
        }
        true
    }

    pub(super) fn pop_flaw(&mut self) -> Option<FlawId> {
        let mut best_idx = None;
        let mut best_priority = -1;

        for (idx, &f_id) in self.flaw_q.iter().enumerate() {
            if self.flaw_status[f_id] == Some(false) {
                continue;
            }
            let priority = if self.flaw_status[f_id] == Some(true) {
                2
            } else if self.has_finite_cost_ancestor(f_id) {
                0
            } else {
                1
            };

            if priority > best_priority {
                best_priority = priority;
                best_idx = Some(idx);

                if best_priority == 2 {
                    break;
                }
            }
        }

        best_idx.and_then(|idx| self.flaw_q.remove(idx))
    }

    /// Returns true if `anc` is a causal ancestor of `flw` along `flaw_causes`.
    pub(super) fn is_ancestor(&self, anc: ResolverId, flw: FlawId) -> bool {
        let mut queue = VecDeque::from([flw]);
        let mut visited = HashSet::new();

        while let Some(f_id) = queue.pop_front() {
            if !visited.insert(f_id) {
                continue;
            }
            for &c_res in &self.flaw_causes[f_id] {
                if c_res == anc {
                    return true;
                }
                queue.push_back(self.resolver_flaw[c_res]);
            }
        }

        false
    }

    fn has_finite_cost_ancestor(&self, target: FlawId) -> bool {
        let mut queue = Vec::new();
        let mut visited = HashSet::new();

        for &res_id in &self.flaw_causes[target] {
            queue.push(self.resolver_flaw[res_id]);
        }

        while let Some(f_id) = queue.pop() {
            if !visited.insert(f_id) {
                continue;
            }

            if self.flaw_cost[f_id] < f64::INFINITY {
                return true;
            }

            for &res_id in &self.flaw_causes[f_id] {
                queue.push(self.resolver_flaw[res_id]);
            }
        }

        false
    }

    pub(super) fn pick_branching_literal(&self) -> Option<Lit> {
        for &f_id in &self.flaw_q {
            if self.flaw_status[f_id].is_none() {
                #[cfg(feature = "server")]
                let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(f_id)));
                return Some(!self.flaw_phi[f_id]);
            }
        }

        if self.agenda.is_empty() {
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
            return None;
        }

        debug_assert!(self.agenda.iter().all(|&f_id| self.flaw_status[f_id] == Some(true)), "Agenda contains flaws that are not active: {}", self.agenda.iter().filter(|&&f_id| self.flaw_status[f_id] != Some(true)).map(|&f_id| f_id.to_string()).collect::<Vec<_>>().join(", "));

        let best_flaw_id = self.agenda.iter().max_by(|&f1, &f2| self.flaw_cost[*f1].partial_cmp(&self.flaw_cost[*f2]).unwrap()).unwrap();
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(*best_flaw_id)));
        let mut best_res_id = None;
        let mut best_res_cost = f64::INFINITY;

        for &r_id in &self.flaw_resolvers[*best_flaw_id] {
            if self.resolver_status[r_id] == Some(false) {
                continue;
            }

            let cost = self.compute_resolver_cost(r_id);
            if best_res_id.is_none() || cost < best_res_cost {
                best_res_cost = cost;
                best_res_id = Some(r_id);
            }
        }

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(best_res_id));
        Some(self.resolver_rho[best_res_id.expect("There should be at least one resolver for the flaw")])
    }
}
