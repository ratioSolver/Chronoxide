#[cfg(all(feature = "h_add", feature = "h_max"))]
compile_error!("Features 'h_add' and 'h_max' are mutually exclusive. Please enable only one of them.");
#[cfg(not(any(feature = "h_add", feature = "h_max")))]
compile_error!("Please enable one of the features 'h_add' or 'h_max'.");

use crate::{SolverError, SolverEvent, SolverState};
use semitone::{
    SeMiTONE,
    ast::{BoolExpr, DlVar},
};
use std::{collections::VecDeque, fmt, ops::Deref};
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
    fn intrinsic_cost(&self) -> rug::Rational;

    /// Applies this resolver.
    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError>;

    /// Preconditions that must be satisfied for this resolver to be applicable.
    fn preconditions(&self) -> Vec<FlawId>;

    /// Adds a precondition to this resolver.
    fn add_precondition(&mut self, _flaw_id: FlawId) {
        unimplemented!("add_precondition is not implemented for this resolver");
    }

    fn to_json(&self) -> serde_json::Value;
}

pub struct Graph {
    flaws: Vec<Option<Box<dyn Flaw>>>,
    resolvers: Vec<Option<Box<dyn Resolver>>>,

    h_flaw: Vec<f64>,

    flaw_phi: Vec<BoolExpr>,
    flaw_cost: Vec<DlVar>,
    resolver_rho: Vec<BoolExpr>,
    resolver_cost: Vec<DlVar>,

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

            h_flaw: Vec::new(),

            flaw_phi: Vec::new(),
            flaw_cost: Vec::new(),
            resolver_rho: Vec::new(),
            resolver_cost: Vec::new(),

            trail: Vec::new(),
            trail_lim: Vec::new(),

            flaw_q: VecDeque::new(),

            tx_event,
        }
    }

    pub fn add_flaw(&mut self, smt: &mut SeMiTONE, mut flaw: Box<dyn Flaw>) -> Result<FlawId, SolverError> {
        let f_id = FlawId(self.flaws.len());
        flaw.set_id(f_id);

        let causes = flaw.causes();
        let phi = match causes.len() {
            0 => BoolExpr::True,
            _ => {
                let phi = smt.new_bool();
                // (ρ₁ ∧ ρ₂ ∧ ... ∧ ρₙ) → ϕ (the flaw is active if all its causes are active)
                let mut clause = Vec::with_capacity(causes.len() + 1);
                for &r_id in causes.iter() {
                    clause.push(!self.resolver_rho[r_id.0].clone());
                }
                clause.push(phi.clone());
                if !smt.assert(BoolExpr::Or(clause)) {
                    return Err(SolverError::Inconsistent);
                }
                phi
            }
        };
        trace!("Adding flaw: {} ({})", flaw.id(), phi);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id: f_id,
            phi: phi.to_string(),
            causes: flaw.causes().to_vec(),
            required_by: flaw.required_by().to_vec(),
            status: smt.get_bool_val(&phi),
            cost: f64::INFINITY,
            data: flaw.to_json(),
        });

        let cost = smt.new_dl_var();

        self.flaws.push(Some(flaw));
        self.flaw_phi.push(phi);
        self.flaw_cost.push(cost);
        self.h_flaw.push(f64::INFINITY);

        self.flaw_q.push_back(f_id);

        Ok(f_id)
    }

    pub(super) fn take_flaw(&mut self, id: FlawId) -> Option<Box<dyn Flaw>> {
        self.flaws[*id].take()
    }

    pub(super) fn return_flaw(&mut self, flaw: Box<dyn Flaw>) {
        let id = flaw.id();
        self.flaws[*id] = Some(flaw);
    }

    fn compute_flaw_cost(&self, smt: &SeMiTONE, flaw_id: FlawId) -> f64 {
        if smt.get_bool_val(&self.flaw_phi[*flaw_id]) == Some(false) {
            f64::INFINITY
        } else {
            let mut min_cost = f64::INFINITY;

            for &resolver_id in self.flaws[*flaw_id].as_ref().expect("Flaw should exist").resolvers().iter() {
                let resolver_cost = self.compute_resolver_cost(smt, resolver_id);
                if resolver_cost < min_cost {
                    min_cost = resolver_cost;
                }
            }

            min_cost
        }
    }

    pub fn flaw_phi(&self, flaw_id: FlawId) -> BoolExpr {
        self.flaw_phi[*flaw_id].clone()
    }

    pub fn flaw_cost(&self, flaw_id: FlawId) -> f64 {
        self.h_flaw[*flaw_id]
    }

    pub fn add_resolver(&mut self, smt: &mut SeMiTONE, mut resolver: Box<dyn Resolver>, rho: BoolExpr) -> Result<ResolverId, SolverError> {
        let r_id = ResolverId(self.resolvers.len());
        trace!("Adding resolver: {} ({}) for flaw {}", resolver.id(), rho, resolver.flaw());
        resolver.set_id(r_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: r_id,
            flaw_id: resolver.flaw(),
            rho: rho.to_string(),
            status: smt.get_bool_val(&rho),
            intrinsic_cost: resolver.intrinsic_cost().to_f64(),
            preconditions: resolver.preconditions().to_vec(),
            data: resolver.to_json(),
        });

        let flaw_id = resolver.flaw();
        // ρ → ϕ (applying the resolver implies solving the flaw)
        if !smt.assert(BoolExpr::Or(vec![!rho.clone(), self.flaw_phi[*flaw_id].clone()])) {
            return Err(SolverError::Inconsistent);
        }

        let cost = smt.new_dl_var();
        let parent_cost_var = self.flaw_cost[*flaw_id];
        if !smt.assert(BoolExpr::Or(vec![!rho.clone(), BoolExpr::DlGe(parent_cost_var, cost, resolver.intrinsic_cost())])) {
            return Err(SolverError::Inconsistent);
        }

        self.resolvers.push(Some(resolver));
        self.resolver_rho.push(rho);
        self.resolver_cost.push(cost);

        Ok(r_id)
    }

    pub(super) fn take_resolver(&mut self, id: ResolverId) -> Option<Box<dyn Resolver>> {
        self.resolvers[*id].take()
    }

    pub(super) fn return_resolver(&mut self, resolver: Box<dyn Resolver>) {
        let id = resolver.id();
        self.resolvers[*id] = Some(resolver);
    }

    pub fn resolver_rho(&self, resolver_id: ResolverId) -> BoolExpr {
        self.resolver_rho[*resolver_id].clone()
    }

    fn compute_resolver_cost(&self, smt: &SeMiTONE, resolver_id: ResolverId) -> f64 {
        if smt.get_bool_val(&self.resolver_rho[*resolver_id]) == Some(false) {
            f64::INFINITY
        } else {
            #[cfg(feature = "h_add")]
            let precondition_cost: f64 = self.resolvers[*resolver_id].as_ref().expect("Resolver should exist").preconditions().iter().map(|&f_id| self.h_flaw[*f_id]).sum();
            #[cfg(feature = "h_max")]
            let precondition_cost: f64 = self.resolvers[*resolver_id].as_ref().expect("Resolver should exist").preconditions().iter().fold(0.0_f64, |acc, &f_id| acc.max(self.h_flaw[*f_id]));

            self.resolvers[*resolver_id].as_ref().expect("Resolver should exist").intrinsic_cost().to_f64() + precondition_cost
        }
    }

    pub(super) fn has_estimated_solution(&self, smt: &SeMiTONE) -> bool {
        for flaw in self.flaws.iter().filter_map(|f| f.as_ref()) {
            if smt.get_bool_val(&self.flaw_phi[*flaw.id()]) == Some(true) && self.h_flaw[*flaw.id()] == f64::INFINITY {
                return false;
            }
        }
        true
    }

    pub(super) fn pop_flaw(&mut self) -> Option<FlawId> {
        self.flaw_q.pop_front()
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];
        while self.trail.len() > target_len {
            let (f, old_cost) = self.trail.pop().unwrap();
            self.h_flaw[*f] = old_cost;
        }
        self.trail_lim.truncate(level);
    }

    pub(super) fn propagate(&mut self, smt: &SeMiTONE, initial_flaw_id: FlawId) {
        let mut queue = VecDeque::new();
        queue.push_back(initial_flaw_id);

        let mut in_queue = vec![false; self.flaws.len()];
        in_queue[*initial_flaw_id] = true;

        while let Some(f_id) = queue.pop_front() {
            in_queue[*f_id] = false;

            let old_cost = self.h_flaw[*f_id];
            let c_cost = self.compute_flaw_cost(smt, f_id);

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
}
