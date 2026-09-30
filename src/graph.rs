#[cfg(all(feature = "h_add", feature = "h_max"))]
compile_error!("Features 'h_add' and 'h_max' are mutually exclusive. Please enable only one of them.");
#[cfg(not(any(feature = "h_add", feature = "h_max")))]
compile_error!("Please enable one of the features 'h_add' or 'h_max'.");

use crate::{SolverError, SolverEvent, SolverState};
use semitone::{Lit, ast::DlVar};
use serde_json::Value;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    ops::Deref,
};
use tokio::sync::broadcast;
use tracing::trace;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct FlawId(usize);

impl Deref for FlawId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for FlawId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ϕ{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ResolverId(usize);

impl Deref for ResolverId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for ResolverId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ρ{}", self.0)
    }
}

pub trait Flaw {
    /// Unique identifier of this flaw in the graph.
    fn id(&self) -> FlawId;
    /// Sets the unique identifier of this flaw in the graph.
    fn set_id(&mut self, id: FlawId);
    /// Causes for this flaw to exist in the graph.
    fn causes(&self) -> Vec<ResolverId>;

    fn required_by(&self) -> Vec<ResolverId> {
        self.causes()
    }
    fn add_required_by(&mut self, _res_id: ResolverId) {
        unimplemented!("add_required_by is not implemented for this flaw");
    }

    /// Expands this flaw by adding resolvers to the graph that can potentially solve it.
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError>;

    /// Resolvers that can potentially solve this flaw.
    fn resolvers(&self) -> Vec<ResolverId>;

    fn to_json(&self) -> serde_json::Value;
}

pub trait Resolver {
    /// Unique identifier of this resolver in the graph.
    fn id(&self) -> ResolverId;
    /// Sets the unique identifier of this resolver in the graph.
    fn set_id(&mut self, id: ResolverId);
    /// Flaw that this resolver is attempting to solve.
    fn flaw(&self) -> FlawId;

    /// The intrinsic cost of selecting this resolver, independent from the current state of the graph.
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(1)
    }

    /// Applies this resolver.
    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    /// Preconditions that must be satisfied for this resolver to be applicable.
    fn preconditions(&self) -> Vec<FlawId> {
        vec![]
    }

    /// Adds a precondition to this resolver.
    fn add_precondition(&mut self, _flaw_id: FlawId) {
        unimplemented!("add_precondition is not implemented for this resolver");
    }

    fn to_json(&self) -> Value {
        Value::Null
    }
}

pub struct Graph {
    flaws: Vec<Option<Box<dyn Flaw>>>,
    resolvers: Vec<Option<Box<dyn Resolver>>>,
    c_flaw: Option<(FlawId, Lit)>,
    c_res: Option<(ResolverId, Lit)>,
    c_preconditions: Vec<FlawId>,

    h_flaw: Vec<f64>,

    lit_to_flaw: HashMap<Lit, Vec<FlawId>>,
    flaw_status: Vec<Option<bool>>,
    flaw_phi: Vec<Lit>,
    flaw_cost: Vec<DlVar>,
    lit_to_resolver: HashMap<Lit, Vec<ResolverId>>,
    resolver_status: Vec<Option<bool>>,
    resolver_rho: Vec<Lit>,
    resolver_cost: Vec<DlVar>,

    agenda: HashSet<FlawId>,

    trail: Vec<(FlawId, f64)>,
    trail_lim: Vec<usize>,

    flaw_q: VecDeque<FlawId>,

    tx_event: broadcast::Sender<SolverEvent>,
}

impl Graph {
    pub(super) fn new(tx_event: broadcast::Sender<SolverEvent>) -> Self {
        Self {
            flaws: Vec::new(),
            resolvers: Vec::new(),
            c_flaw: None,
            c_res: None,
            c_preconditions: Vec::new(),

            h_flaw: Vec::new(),

            lit_to_flaw: HashMap::new(),
            flaw_status: Vec::new(),
            flaw_phi: Vec::new(),
            flaw_cost: Vec::new(),
            lit_to_resolver: HashMap::new(),
            resolver_status: Vec::new(),
            resolver_rho: Vec::new(),
            resolver_cost: Vec::new(),

            agenda: HashSet::new(),

            trail: Vec::new(),
            trail_lim: Vec::new(),

            flaw_q: VecDeque::new(),

            tx_event,
        }
    }

    /// Returns the ρ literals of the given resolvers, used by the caller to build a flaw's causes clause.
    pub(super) fn resolver_rhos(&self, res_ids: &[ResolverId]) -> Vec<Lit> {
        res_ids.iter().map(|&r_id| self.resolver_rho[r_id.0]).collect()
    }

    /// Returns the DL cost variable associated with a flaw.
    pub(super) fn flaw_cost(&self, flw_id: FlawId) -> DlVar {
        self.flaw_cost[*flw_id]
    }

    /// Registers a new flaw in the graph. `phi`, `status` and `cost` must already be set up in the SAT/theory solver by the caller.
    pub fn add_flaw(&mut self, mut flw: Box<dyn Flaw>, phi: Lit, status: Option<bool>, cost: DlVar) -> FlawId {
        let flw_id = FlawId(self.flaws.len());
        flw.set_id(flw_id);
        if self.c_res.is_some() {
            self.c_preconditions.push(flw_id);
        }
        trace!("Adding flaw: {} ({})", flw.id(), phi);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id: flw_id,
            phi: phi.to_string(),
            causes: flw.causes().to_vec(),
            required_by: flw.required_by().to_vec(),
            status,
            cost: f64::INFINITY,
            data: flw.to_json(),
        });

        self.flaws.push(Some(flw));
        self.lit_to_flaw.entry(phi).or_default().push(flw_id);
        self.flaw_status.push(status);
        if status == Some(true) {
            self.agenda.insert(flw_id);
            trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
        }
        self.flaw_phi.push(phi);
        self.flaw_cost.push(cost);
        self.h_flaw.push(f64::INFINITY);

        self.flaw_q.push_back(flw_id);

        flw_id
    }

    pub(super) fn phi(&self, flw_id: FlawId) -> Lit {
        self.flaw_phi[*flw_id]
    }

    pub(super) fn current_flaw(&self) -> Option<(FlawId, Lit)> {
        self.c_flaw
    }

    pub(super) fn flaw(&self, flw_id: FlawId) -> Option<&Box<dyn Flaw>> {
        self.flaws[*flw_id].as_ref()
    }

    pub(super) fn take_flaw(&mut self, flw_id: FlawId) -> Option<Box<dyn Flaw>> {
        self.c_flaw.replace((flw_id, self.flaw_phi[*flw_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));
        self.flaws[*flw_id].take()
    }

    pub(super) fn return_flaw(&mut self, flw: Box<dyn Flaw>) {
        let id = flw.id();
        self.flaws[*id] = Some(flw);
        self.c_flaw.take();
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
    }

    fn compute_flaw_cost(&self, flw_id: FlawId) -> f64 {
        if self.flaw_status[*flw_id] == Some(false) {
            f64::INFINITY
        } else {
            let mut min_cost = f64::INFINITY;

            for &resolver_id in self.flaws[*flw_id].as_ref().expect("Flaw should exist").resolvers().iter() {
                let resolver_cost = self.compute_resolver_cost(resolver_id);
                if resolver_cost < min_cost {
                    min_cost = resolver_cost;
                }
            }

            min_cost
        }
    }

    /// Registers a new resolver in the graph. `rho`, `status` and `cost` must already be set up in the SAT/theory solver by the caller.
    pub fn add_resolver(&mut self, mut res: Box<dyn Resolver>, rho: Lit, status: Option<bool>, cost: DlVar) -> ResolverId {
        let r_id = ResolverId(self.resolvers.len());
        trace!("Adding resolver: {} ({}) for flaw {}", res.id(), rho, res.flaw());
        res.set_id(r_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: r_id,
            flaw_id: res.flaw(),
            rho: rho.to_string(),
            status,
            intrinsic_cost: res.intrinsic_cost().to_f64(),
            preconditions: res.preconditions().to_vec(),
            data: res.to_json(),
        });

        let flaw_id = res.flaw();
        self.resolvers.push(Some(res));
        self.lit_to_resolver.entry(rho).or_default().push(r_id);
        self.resolver_status.push(status);
        if status == Some(true) {
            self.agenda.remove(&flaw_id);
            trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id });
        }
        self.resolver_rho.push(rho);
        self.resolver_cost.push(cost);

        r_id
    }

    pub(super) fn rho(&self, res_id: ResolverId) -> Lit {
        self.resolver_rho[*res_id]
    }

    pub(super) fn current_resolver(&self) -> Option<(ResolverId, Lit)> {
        self.c_res
    }

    /// Whether a flaw or resolver is currently checked out (between `take_*` and `return_*`).
    /// `propagate`/`propagate_costs` must not run while this is true.
    pub(super) fn is_busy(&self) -> bool {
        self.c_flaw.is_some() || self.c_res.is_some()
    }

    pub(super) fn take_resolver(&mut self, res_id: ResolverId) -> Option<Box<dyn Resolver>> {
        self.c_res.replace((res_id, self.resolver_rho[*res_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(res_id)));
        self.resolvers[*res_id].take()
    }

    pub(super) fn return_resolver(&mut self, mut res: Box<dyn Resolver>) {
        for pre in self.c_preconditions.drain(..) {
            res.add_precondition(pre);
        }
        let id = res.id();
        self.resolvers[*id] = Some(res);
        self.c_res.take();
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
    }

    /// Registers a causal link from the current resolver to `flw_id`, returning `(rho, phi)` so the
    /// caller can add the ρ → ϕ implication clause to the SAT/theory solver.
    pub(super) fn add_causal_link(&mut self, flw_id: FlawId) -> Result<(Lit, Lit), SolverError> {
        let phi = self.flaw_phi[*flw_id];
        let (res_id, rho) = self.c_res.ok_or(SolverError::RuntimeError("No current resolver to add causal link from".to_string()))?;
        self.flaws[*flw_id].as_mut().ok_or(SolverError::RuntimeError(format!("Flaw {} not found", flw_id)))?.add_required_by(res_id);
        self.c_preconditions.push(flw_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewCausalLink { flaw_id: flw_id, resolver_id: res_id });

        Ok((rho, phi))
    }

    fn compute_resolver_cost(&self, res_id: ResolverId) -> f64 {
        if self.resolver_status[*res_id] == Some(false) {
            f64::INFINITY
        } else {
            #[cfg(feature = "h_add")]
            let precondition_cost: f64 = self.resolvers[*res_id].as_ref().expect("Resolver should exist").preconditions().iter().map(|&f_id| self.h_flaw[*f_id]).sum();
            #[cfg(feature = "h_max")]
            let precondition_cost: f64 = self.resolvers[*res_id].as_ref().expect("Resolver should exist").preconditions().iter().fold(0.0_f64, |acc, &f_id| acc.max(self.h_flaw[*f_id]));

            self.resolvers[*res_id].as_ref().expect("Resolver should exist").intrinsic_cost().to_f64() + precondition_cost
        }
    }

    pub(super) fn has_estimated_solution(&self) -> bool {
        for &f_id in &self.agenda {
            if self.flaw_status[*f_id] == Some(true) && self.h_flaw[*f_id] == f64::INFINITY {
                return false;
            }
        }
        true
    }

    pub(super) fn pick_branching_literal(&self) -> Option<Lit> {
        for &f_id in &self.flaw_q {
            if self.flaw_status[*f_id].is_none() {
                #[cfg(feature = "server")]
                let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(f_id)));
                return Some(!self.flaw_phi[*f_id]);
            }
        }

        if self.agenda.is_empty() {
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
            return None;
        }

        let best_flaw_id = self.agenda.iter().max_by(|&f1, &f2| self.h_flaw[**f1].partial_cmp(&self.h_flaw[**f2]).unwrap()).unwrap();
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(*best_flaw_id)));
        let mut best_res_id = None;
        let mut best_res_cost = f64::INFINITY;

        let flaw = self.flaws[**best_flaw_id].as_ref().unwrap();
        for &r_id in flaw.resolvers().iter() {
            if self.resolver_status[*r_id] == Some(false) {
                continue;
            }

            let cost = self.compute_resolver_cost(r_id);
            if cost < best_res_cost {
                best_res_cost = cost;
                best_res_id = Some(r_id);
            }
        }

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(best_res_id));
        Some(self.resolver_rho[*best_res_id.expect("There should be at least one resolver for the flaw")])
    }

    pub(super) fn pop_flaw(&mut self) -> Option<FlawId> {
        self.flaw_q.pop_front()
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    pub(super) fn propagate(&mut self, lits: &[Lit]) {
        let mut affected_flaws = Vec::new();
        for &lit in lits {
            if let Some(flw_ids) = self.lit_to_flaw.get(&lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[*flw_id] = Some(true);
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: Some(true) });
                    self.agenda.insert(flw_id);
                    trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                }
            }
            if let Some(flw_ids) = self.lit_to_flaw.get(&!lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[*flw_id] = Some(false);
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: Some(false) });
                    affected_flaws.push(flw_id);
                }
            }
        }
        for &lit in lits {
            if let Some(res_ids) = self.lit_to_resolver.get(&lit) {
                for &res_id in res_ids {
                    self.resolver_status[*res_id] = Some(true);
                    let flaw_id = self.resolvers[*res_id].as_ref().expect("Resolver should exist").flaw();
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: Some(true) });
                    self.agenda.remove(&flaw_id);
                    trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id });
                }
            }
            if let Some(res_ids) = self.lit_to_resolver.get(&!lit) {
                for &res_id in res_ids {
                    self.resolver_status[*res_id] = Some(false);
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: Some(false) });
                    affected_flaws.push(self.resolvers[*res_id].as_ref().expect("Resolver should exist").flaw());
                }
            }
        }

        self.propagate_costs(affected_flaws.as_slice());
    }

    pub(super) fn cancel_until(&mut self, level: usize, lits: &[Lit]) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];
        while self.trail.len() > target_len {
            let (f, old_cost) = self.trail.pop().unwrap();
            self.h_flaw[*f] = old_cost;
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::FlawCostUpdate { flaw_id: f, cost: old_cost });
        }
        self.trail_lim.truncate(level);

        for &lit in lits {
            if let Some(flw_ids) = self.lit_to_flaw.get(&lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[*flw_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: None });
                    self.agenda.remove(&flw_id);
                    trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id: flw_id });
                }
            }
            if let Some(flw_ids) = self.lit_to_flaw.get(&!lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[*flw_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: None });
                }
            }
        }
        for &lit in lits {
            if let Some(res_ids) = self.lit_to_resolver.get(&lit) {
                for &res_id in res_ids {
                    self.resolver_status[*res_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: None });
                    let flw_id = self.resolvers[*res_id].as_ref().expect("Resolver should exist").flaw();
                    if self.flaw_status[*flw_id] == Some(true) {
                        self.agenda.insert(flw_id);
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                    }
                }
            }
            if let Some(res_ids) = self.lit_to_resolver.get(&!lit) {
                for &res_id in res_ids {
                    self.resolver_status[*res_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: None });
                }
            }
        }
    }

    pub(super) fn propagate_costs(&mut self, initial_flaws: &[FlawId]) {
        assert!(self.c_flaw.is_none(), "Cannot propagate while a flaw is being processed");
        assert!(self.c_res.is_none(), "Cannot propagate while a resolver is being processed");

        let mut queue = VecDeque::new();
        let mut in_queue = vec![false; self.flaws.len()];
        for &f_id in initial_flaws {
            queue.push_back(f_id);
            in_queue[*f_id] = true;
        }

        while let Some(f_id) = queue.pop_front() {
            in_queue[*f_id] = false;

            let old_cost = self.h_flaw[*f_id];
            let c_cost = self.compute_flaw_cost(f_id);

            if c_cost != old_cost {
                self.trail.push((f_id, old_cost));
                self.h_flaw[*f_id] = c_cost;
                #[cfg(feature = "server")]
                let _ = self.tx_event.send(SolverEvent::FlawCostUpdate { flaw_id: f_id, cost: c_cost });

                for &r_id in self.flaws[*f_id].as_ref().expect("Flaw should exist").required_by().iter() {
                    let parent_flaw_id = self.resolvers[*r_id].as_ref().expect("Resolver should exist").flaw();
                    if !in_queue[*parent_flaw_id] {
                        queue.push_back(parent_flaw_id);
                        in_queue[*parent_flaw_id] = true;
                    }
                }
            }
        }
    }

    pub(super) fn can_unify(&self, target: FlawId) -> bool {
        if self.flaw_q.contains(&target) {
            return false;
        }

        let mut queue = vec![target];
        let mut visited = std::collections::HashSet::new();

        while let Some(f_id) = queue.pop() {
            if !visited.insert(f_id) {
                continue;
            }

            if self.flaws[*f_id].is_none() {
                return false;
            }

            if let Some(flaw) = self.flaws[*f_id].as_ref() {
                for r_id in flaw.causes() {
                    if let Some(resolver) = self.resolvers[*r_id].as_ref() {
                        queue.push(resolver.flaw());
                    }
                }
            }
        }

        true
    }
}
