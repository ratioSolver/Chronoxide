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
    /// Expands this flaw by adding resolvers to the graph that can potentially solve it.
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError>;

    /// Serializes the domain-specific payload of this flaw to JSON.
    fn to_json(&self) -> Value;
}

pub trait Resolver {
    /// The intrinsic cost of selecting this resolver, independent from the current state of the graph.
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(1)
    }

    /// Applies this resolver, adding its constraints, sub-flaws, or causal links to the solver state.
    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
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
    c_preconditions: Vec<FlawId>,

    h_flaw: Vec<f64>,

    lit_to_flaw: HashMap<Lit, Vec<FlawId>>,
    flaw_status: Vec<Option<bool>>,
    flaw_phi: Vec<Lit>,
    flaw_cost: Vec<DlVar>,
    flaw_causes: Vec<Vec<ResolverId>>,
    flaw_required_by: Vec<Vec<ResolverId>>,
    flaw_resolvers: Vec<Vec<ResolverId>>,

    lit_to_resolver: HashMap<Lit, Vec<ResolverId>>,
    resolver_status: Vec<Option<bool>>,
    resolver_rho: Vec<Lit>,
    resolver_cost: Vec<DlVar>,
    resolver_flaw: Vec<FlawId>,
    resolver_preconditions: Vec<Vec<FlawId>>,

    created_residuals: HashSet<(ResolverId, FlawId, ResolverId)>,

    agenda: HashSet<FlawId>,

    trail: Vec<(FlawId, f64)>,
    trail_lim: Vec<usize>,
    costs_dirty: bool,

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
            flaw_causes: Vec::new(),
            flaw_required_by: Vec::new(),
            flaw_resolvers: Vec::new(),

            lit_to_resolver: HashMap::new(),
            resolver_status: Vec::new(),
            resolver_rho: Vec::new(),
            resolver_cost: Vec::new(),
            resolver_flaw: Vec::new(),
            resolver_preconditions: Vec::new(),

            created_residuals: HashSet::new(),

            agenda: HashSet::new(),

            trail: Vec::new(),
            trail_lim: Vec::new(),
            costs_dirty: false,

            flaw_q: VecDeque::new(),

            tx_event,
        }
    }

    /// Returns the currently active resolver as a cause vector (empty if at root level).
    pub(super) fn current_cause(&self) -> Vec<ResolverId> {
        self.c_res.map(|(r_id, _)| vec![r_id]).unwrap_or_default()
    }

    /// Returns the ρ literals of the given resolvers, used by the caller to build a flaw's causes clause.
    pub(super) fn resolver_rhos(&self, res_ids: &[ResolverId]) -> Vec<Lit> {
        res_ids.iter().map(|&r_id| self.resolver_rho[*r_id]).collect()
    }

    /// Returns the DL cost variable associated with a flaw.
    pub(super) fn flaw_cost(&self, flw_id: FlawId) -> DlVar {
        self.flaw_cost[*flw_id]
    }

    /// Returns the DL cost variable associated with a resolver.
    pub(super) fn resolver_cost(&self, res_id: ResolverId) -> DlVar {
        self.resolver_cost[*res_id]
    }

    /// Registers a new flaw in the graph. `phi`, `status`, and `cost` must already be set up in the SAT/theory solver by the caller.
    pub fn add_flaw(&mut self, flw: Box<dyn Flaw>, causes: Vec<ResolverId>, phi: Lit, status: Option<bool>, cost: DlVar) -> FlawId {
        let flw_id = FlawId(self.flaws.len());
        if self.c_res.is_some() {
            self.c_preconditions.push(flw_id);
        }
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
        self.flaw_causes.push(causes.clone());
        self.flaw_required_by.push(causes);
        self.flaw_resolvers.push(Vec::new());
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

    pub(super) fn flaw_causes(&self, flw_id: FlawId) -> &[ResolverId] {
        &self.flaw_causes[*flw_id]
    }

    pub(super) fn flaw_resolvers(&self, flw_id: FlawId) -> &[ResolverId] {
        &self.flaw_resolvers[*flw_id]
    }

    pub(super) fn take_flaw(&mut self, flw_id: FlawId) -> Option<Box<dyn Flaw>> {
        self.c_flaw.replace((flw_id, self.flaw_phi[*flw_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));
        self.flaws[*flw_id].take()
    }

    pub(super) fn return_flaw(&mut self, flw: Box<dyn Flaw>) {
        let (id, _) = self.c_flaw.take().expect("A flaw must be checked out when calling return_flaw");
        self.flaws[*id] = Some(flw);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
    }

    fn compute_flaw_cost(&self, flw_id: FlawId) -> f64 {
        if self.flaw_status[*flw_id] == Some(false) {
            f64::INFINITY
        } else {
            let mut min_cost = f64::INFINITY;

            for &resolver_id in &self.flaw_resolvers[*flw_id] {
                let resolver_cost = self.compute_resolver_cost(resolver_id);
                if resolver_cost < min_cost {
                    min_cost = resolver_cost;
                }
            }

            min_cost
        }
    }

    /// Registers a new resolver for the currently checked-out flaw (`c_flaw`).
    /// `rho`, `status`, and `cost` must already be set up in the SAT/theory solver by the caller.
    pub fn add_resolver(&mut self, res: Box<dyn Resolver>, rho: Lit, status: Option<bool>, cost: DlVar) -> ResolverId {
        let (flaw_id, _) = self.c_flaw.expect("Cannot add a resolver when no flaw is checked out");
        let r_id = ResolverId(self.resolvers.len());
        trace!("Adding resolver: {} ({}) for flaw {}", r_id, rho, flaw_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: r_id,
            flaw_id,
            rho: rho.to_string(),
            status,
            intrinsic_cost: res.intrinsic_cost().to_f64(),
            preconditions: Vec::new(),
            data: res.to_json(),
        });

        self.resolvers.push(Some(res));
        self.flaw_resolvers[*flaw_id].push(r_id);
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
        self.resolver_flaw.push(flaw_id);
        self.resolver_preconditions.push(Vec::new());

        r_id
    }

    pub(super) fn rho(&self, res_id: ResolverId) -> Lit {
        self.resolver_rho[*res_id]
    }

    pub(super) fn resolver(&self, res_id: ResolverId) -> Option<&dyn Resolver> {
        self.resolvers[*res_id].as_deref()
    }

    pub(super) fn resolver_flaw(&self, res_id: ResolverId) -> FlawId {
        self.resolver_flaw[*res_id]
    }

    pub(super) fn resolver_preconditions(&self, res_id: ResolverId) -> &[FlawId] {
        &self.resolver_preconditions[*res_id]
    }

    pub(super) fn resolvers_for_lit(&self, lit: Lit) -> Option<&[ResolverId]> {
        self.lit_to_resolver.get(&lit).map(|v| v.as_slice())
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

    pub(super) fn return_resolver(&mut self, res: Box<dyn Resolver>) {
        let (id, _) = self.c_res.take().expect("A resolver must be checked out when calling return_resolver");
        for pre in self.c_preconditions.drain(..) {
            if !self.resolver_preconditions[*id].contains(&pre) {
                self.resolver_preconditions[*id].push(pre);
            }
        }
        self.resolvers[*id] = Some(res);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
    }

    /// Registers a causal link from the current resolver to `flw_id`, returning `(rho, phi)` so the
    /// caller can add the ρ → ϕ implication clause to the SAT/theory solver.
    pub(super) fn add_causal_link(&mut self, flw_id: FlawId) -> Result<(Lit, Lit), SolverError> {
        let phi = self.flaw_phi[*flw_id];
        let (res_id, rho) = self.c_res.ok_or(SolverError::RuntimeError(String::from("No current resolver to add causal link from")))?;
        if !self.flaw_required_by[*flw_id].contains(&res_id) {
            self.flaw_required_by[*flw_id].push(res_id);
        }
        self.c_preconditions.push(flw_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewCausalLink { flaw_id: flw_id, resolver_id: res_id });

        Ok((rho, phi))
    }

    /// Links `flw_id` as a precondition of `res_id` directly (used when attaching a `ResidualFlaw`).
    pub(super) fn add_precondition_to_resolver(&mut self, res_id: ResolverId, flw_id: FlawId) {
        if !self.resolver_preconditions[*res_id].contains(&flw_id) {
            self.resolver_preconditions[*res_id].push(flw_id);
        }
        if !self.flaw_required_by[*flw_id].contains(&res_id) {
            self.flaw_required_by[*flw_id].push(res_id);
        }
    }

    /// Removes `flw_id` from the unexpanded flaw queue (used when expanding a `ResidualFlaw` immediately).
    pub(super) fn remove_from_flaw_q(&mut self, flw_id: FlawId) {
        self.flaw_q.retain(|&id| id != flw_id);
    }

    /// Records a `(cause_res, target_flaw, excluded_res)` tuple to avoid creating duplicate residual flaws.
    pub(super) fn register_residual(&mut self, cause_res: ResolverId, target_flaw: FlawId, excluded_res: ResolverId) -> bool {
        self.created_residuals.insert((cause_res, target_flaw, excluded_res))
    }

    fn compute_resolver_cost(&self, res_id: ResolverId) -> f64 {
        if self.resolver_status[*res_id] == Some(false) {
            f64::INFINITY
        } else {
            #[cfg(feature = "h_add")]
            let precondition_cost: f64 = self.resolver_preconditions[*res_id].iter().map(|&f_id| self.h_flaw[*f_id]).sum();
            #[cfg(feature = "h_max")]
            let precondition_cost: f64 = self.resolver_preconditions[*res_id].iter().fold(0.0_f64, |acc, &f_id| acc.max(self.h_flaw[*f_id]));

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

        for &r_id in &self.flaw_resolvers[**best_flaw_id] {
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
        let mut to_keep = Vec::new();
        for &f_id in &self.flaw_q {
            if !self.is_unreachable(f_id) {
                to_keep.push(f_id);
            }
        }
        self.flaw_q = VecDeque::from(to_keep);

        if self.flaw_q.is_empty() {
            return None;
        }

        let mut best_idx = 0;
        let mut best_priority = -1;

        for (idx, &f_id) in self.flaw_q.iter().enumerate() {
            let priority = if self.flaw_status[*f_id] == Some(true) {
                2
            } else if self.has_finite_cost_ancestor(f_id) {
                0
            } else {
                1
            };

            if priority > best_priority {
                best_priority = priority;
                best_idx = idx;

                if best_priority == 2 {
                    break;
                }
            }
        }

        self.flaw_q.remove(best_idx)
    }

    /// Returns true if the flaw is already false or all resolvers requiring it are false.
    fn is_unreachable(&self, flw_id: FlawId) -> bool {
        if self.flaw_status[*flw_id] == Some(false) {
            return true;
        }
        let req = &self.flaw_required_by[*flw_id];
        !req.is_empty() && req.iter().all(|&r_id| self.resolver_status[*r_id] == Some(false))
    }

    fn has_finite_cost_ancestor(&self, target: FlawId) -> bool {
        let mut queue = Vec::new();
        let mut visited = HashSet::new();

        for &res_id in &self.flaw_causes[*target] {
            queue.push(self.resolver_flaw[*res_id]);
        }

        while let Some(f_id) = queue.pop() {
            if !visited.insert(f_id) {
                continue;
            }

            if self.h_flaw[*f_id] < f64::INFINITY {
                return true;
            }

            for &res_id in &self.flaw_causes[*f_id] {
                queue.push(self.resolver_flaw[*res_id]);
            }
        }

        false
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
                    if !self.flaw_resolvers[*flw_id].iter().any(|&r| self.resolver_status[*r] == Some(true)) {
                        self.agenda.insert(flw_id);
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                    }
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
                    let flaw_id = self.resolver_flaw[*res_id];
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
                    affected_flaws.push(self.resolver_flaw[*res_id]);
                }
            }
        }

        self.propagate_costs(affected_flaws.as_slice());
    }

    /// Recomputes the cost of every flaw after a backtrack.
    /// Flaws and resolvers are never removed on backtrack, but costs computed after a flaw was expanded
    /// at a deeper level are rolled back by the trail, leaving expanded flaws with a stale infinite cost.
    pub(super) fn refresh_costs(&mut self) {
        if !self.costs_dirty || self.is_busy() {
            return;
        }
        self.costs_dirty = false;
        let all: Vec<FlawId> = (0..self.flaws.len()).filter(|&i| self.flaws[i].is_some()).map(FlawId).collect();
        self.propagate_costs(&all);
    }

    pub(super) fn cancel_until(&mut self, level: usize, lits: &[Lit]) {
        if level >= self.trail_lim.len() {
            return;
        }
        self.costs_dirty = true;

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
                    let flw_id = self.resolver_flaw[*res_id];
                    if self.flaw_status[*flw_id] == Some(true) && !self.flaw_resolvers[*flw_id].iter().any(|&r| self.resolver_status[*r] == Some(true)) {
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

                for &r_id in &self.flaw_required_by[*f_id] {
                    let parent_flaw_id = self.resolver_flaw[*r_id];
                    if !in_queue[*parent_flaw_id] {
                        queue.push_back(parent_flaw_id);
                        in_queue[*parent_flaw_id] = true;
                    }
                }
            }
        }
    }

    pub(super) fn is_expanded(&self, flw_id: FlawId) -> bool {
        !self.flaw_q.contains(&flw_id)
    }

    /// Checks whether `source_flaw` can unify with `target` without creating a causal cycle.
    pub(super) fn can_unify(&self, source_flaw: FlawId, target: FlawId) -> bool {
        let mut queue = vec![source_flaw];
        let mut visited = HashSet::new();

        while let Some(f_id) = queue.pop() {
            if f_id == target {
                return false;
            }
            if !visited.insert(f_id) {
                continue;
            }

            for &r_id in &self.flaw_causes[*f_id] {
                let parent_flaw = self.resolver_flaw[*r_id];
                if parent_flaw == target {
                    return false;
                }
                queue.push(parent_flaw);
            }
        }

        true
    }

    /// Checks whether `source_flaw` can depend on `targets` (via `flaw_required_by`) without creating a cycle.
    pub(super) fn can_depend_on(&self, source_flaw: FlawId, targets: &[FlawId]) -> bool {
        let mut queue = vec![source_flaw];
        let mut visited = HashSet::new();

        while let Some(f_id) = queue.pop() {
            if targets.contains(&f_id) {
                return false;
            }
            if !visited.insert(f_id) {
                continue;
            }

            for &r_id in &self.flaw_required_by[*f_id] {
                queue.push(self.resolver_flaw[*r_id]);
            }
        }

        true
    }
}
