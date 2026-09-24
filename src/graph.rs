#[cfg(all(feature = "h_add", feature = "h_max"))]
compile_error!("Features 'h_add' and 'h_max' are mutually exclusive. Please enable only one of them.");
#[cfg(not(any(feature = "h_add", feature = "h_max")))]
compile_error!("Please enable one of the features 'h_add' or 'h_max'.");

use crate::{SolverError, SolverEvent, SolverState};
use semitone::{
    Lit, SeMiTONE,
    ast::{BoolExpr, DlVar},
};
use serde_json::Value;
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

    flaw_status: Vec<Option<bool>>,
    flaw_phi: Vec<Lit>,
    flaw_cost: Vec<DlVar>,
    resolver_status: Vec<Option<bool>>,
    resolver_rho: Vec<Lit>,
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
            c_flaw: None,
            c_res: None,
            c_preconditions: Vec::new(),

            h_flaw: Vec::new(),

            flaw_status: Vec::new(),
            flaw_phi: Vec::new(),
            flaw_cost: Vec::new(),
            resolver_status: Vec::new(),
            resolver_rho: Vec::new(),
            resolver_cost: Vec::new(),

            trail: Vec::new(),
            trail_lim: Vec::new(),

            flaw_q: VecDeque::new(),

            tx_event,
        }
    }

    pub fn add_flaw(&mut self, smt: &mut SeMiTONE, mut flw: Box<dyn Flaw>) -> Result<FlawId, SolverError> {
        let flw_id = FlawId(self.flaws.len());
        flw.set_id(flw_id);
        if self.c_res.is_some() {
            self.c_preconditions.push(flw_id);
        }

        let causes = flw.causes();
        let phi = match causes.len() {
            0 => Lit::TRUE,
            _ => {
                let phi = smt.new_lit();
                // (ρ₁ ∧ ρ₂ ∧ ... ∧ ρₙ) → ϕ (the flaw is active if all its causes are active)
                let mut clause = Vec::with_capacity(causes.len() + 1);
                for &r_id in causes.iter() {
                    clause.push(!self.resolver_rho[r_id.0]);
                }
                clause.push(phi);
                smt.add_clause(clause).expect("Failed to add clause for flaw causes");
                phi
            }
        };
        trace!("Adding flaw: {} ({})", flw.id(), phi);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id: flw_id,
            phi: phi.to_string(),
            causes: flw.causes().to_vec(),
            required_by: flw.required_by().to_vec(),
            status: smt.get_lit_val(phi),
            cost: f64::INFINITY,
            data: flw.to_json(),
        });

        let cost = smt.new_dl_var();

        self.flaws.push(Some(flw));
        self.flaw_status.push(smt.get_lit_val(phi));
        self.flaw_phi.push(phi);
        self.flaw_cost.push(cost);
        self.h_flaw.push(f64::INFINITY);

        self.flaw_q.push_back(flw_id);

        Ok(flw_id)
    }

    pub(super) fn current_flaw(&self) -> Option<(FlawId, Lit)> {
        self.c_flaw
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

    fn compute_flaw_cost(&self, smt: &SeMiTONE, flw_id: FlawId) -> f64 {
        if smt.get_lit_val(self.flaw_phi[*flw_id]) == Some(false) {
            f64::INFINITY
        } else {
            let mut min_cost = f64::INFINITY;

            for &resolver_id in self.flaws[*flw_id].as_ref().expect("Flaw should exist").resolvers().iter() {
                let resolver_cost = self.compute_resolver_cost(smt, resolver_id);
                if resolver_cost < min_cost {
                    min_cost = resolver_cost;
                }
            }

            min_cost
        }
    }

    pub fn add_resolver(&mut self, smt: &mut SeMiTONE, mut res: Box<dyn Resolver>, rho: Lit) -> Result<ResolverId, SolverError> {
        assert!(smt.get_lit_val(rho) != Some(false), "Cannot add resolver with a false ρ");
        let r_id = ResolverId(self.resolvers.len());
        trace!("Adding resolver: {} ({}) for flaw {}", res.id(), rho, res.flaw());
        res.set_id(r_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: r_id,
            flaw_id: res.flaw(),
            rho: rho.to_string(),
            status: smt.get_lit_val(rho),
            intrinsic_cost: res.intrinsic_cost().to_f64(),
            preconditions: res.preconditions().to_vec(),
            data: res.to_json(),
        });

        let flaw_id = res.flaw();
        // ρ → ϕ (applying the resolver implies solving the flaw)
        smt.add_clause(vec![!rho, self.flaw_phi[*flaw_id]]).expect("Failed to add clause for resolver implication");

        let cost = smt.new_dl_var();
        let parent_cost_var = self.flaw_cost[*flaw_id];
        let dl_cnstr = smt.track_expr(BoolExpr::DlGe(parent_cost_var, cost, res.intrinsic_cost()));
        smt.add_clause(vec![!rho, dl_cnstr]).expect("Failed to add clause for resolver cost implication");

        self.resolvers.push(Some(res));
        self.resolver_status.push(smt.get_lit_val(rho));
        self.resolver_rho.push(rho);
        self.resolver_cost.push(cost);

        Ok(r_id)
    }

    pub(super) fn current_resolver(&self) -> Option<(ResolverId, Lit)> {
        self.c_res
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

    pub(super) fn add_causal_link(&mut self, smt: &mut SeMiTONE, flw_id: FlawId) -> Result<(), SolverError> {
        let phi = self.flaw_phi[*flw_id];
        let (res_id, rho) = self.c_res.ok_or(SolverError::RuntimeError("No current resolver to add causal link from".to_string()))?;
        self.flaws[*flw_id].as_mut().ok_or(SolverError::RuntimeError(format!("Flaw {} not found", flw_id)))?.add_required_by(res_id);
        self.c_preconditions.push(flw_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewCausalLink { flaw_id: flw_id, resolver_id: res_id });

        // ρ → ϕ (applying the resolver implies solving the flaw)
        smt.add_clause(vec![!rho, phi]).map_err(|_e| SolverError::RuntimeError(format!("Failed to add causal link from resolver {} to flaw {}", res_id, flw_id)))?;

        Ok(())
    }

    fn compute_resolver_cost(&self, smt: &SeMiTONE, res_id: ResolverId) -> f64 {
        if smt.get_lit_val(self.resolver_rho[*res_id]) == Some(false) {
            f64::INFINITY
        } else {
            #[cfg(feature = "h_add")]
            let precondition_cost: f64 = self.resolvers[*res_id].as_ref().expect("Resolver should exist").preconditions().iter().map(|&f_id| self.h_flaw[*f_id]).sum();
            #[cfg(feature = "h_max")]
            let precondition_cost: f64 = self.resolvers[*res_id].as_ref().expect("Resolver should exist").preconditions().iter().fold(0.0_f64, |acc, &f_id| acc.max(self.h_flaw[*f_id]));

            self.resolvers[*res_id].as_ref().expect("Resolver should exist").intrinsic_cost().to_f64() + precondition_cost
        }
    }

    pub(super) fn has_estimated_solution(&self, smt: &SeMiTONE) -> bool {
        for flaw in self.flaws.iter().filter_map(|f| f.as_ref()) {
            if smt.get_lit_val(self.flaw_phi[*flaw.id()]) == Some(true) && self.h_flaw[*flaw.id()] == f64::INFINITY {
                return false;
            }
        }
        true
    }

    pub(super) fn get_agenda(&self, smt: &SeMiTONE) -> Vec<FlawId> {
        assert!(self.c_flaw.is_none(), "Cannot get agenda while a flaw is being processed");
        assert!(self.c_res.is_none(), "Cannot get agenda while a resolver is being processed");

        let mut agenda = Vec::new();
        for flaw in &self.flaws {
            if let Some(flaw) = flaw.as_ref() {
                let f_id = flaw.id();
                if smt.get_lit_val(self.flaw_phi[*f_id]) == Some(true) {
                    let mut is_resolved = false;
                    for r_id in flaw.resolvers() {
                        if smt.get_lit_val(self.resolver_rho[*r_id]) == Some(true) {
                            is_resolved = true;
                            break;
                        }
                    }
                    if !is_resolved {
                        agenda.push(f_id);
                    }
                }
            }
        }
        agenda
    }

    pub(super) fn pick_branching_literal(&self, smt: &mut SeMiTONE) -> Option<Lit> {
        for &f_id in &self.flaw_q {
            if smt.get_lit_val(self.flaw_phi[*f_id]).is_none() {
                return Some(!self.flaw_phi[*f_id]);
            }
        }

        let agenda = self.get_agenda(smt);

        if agenda.is_empty() {
            return None;
        }

        let best_flaw_id = agenda.into_iter().max_by(|&f1, &f2| self.h_flaw[*f1].partial_cmp(&self.h_flaw[*f2]).unwrap()).unwrap();
        let mut best_res_id = None;
        let mut best_res_cost = f64::INFINITY;

        let flaw = self.flaws[*best_flaw_id].as_ref().unwrap();
        for &r_id in flaw.resolvers().iter() {
            if smt.get_lit_val(self.resolver_rho[*r_id]) == Some(false) {
                continue;
            }

            let cost = self.compute_resolver_cost(smt, r_id);
            if cost < best_res_cost {
                best_res_cost = cost;
                best_res_id = Some(r_id);
            }
        }

        Some(self.resolver_rho[*best_res_id.expect("There should be at least one resolver for the flaw")])
    }

    pub(super) fn pop_flaw(&mut self) -> Option<FlawId> {
        self.flaw_q.pop_front()
    }

    pub(super) fn sync(&mut self, smt: &SeMiTONE) {
        let mut affected_flaws = Vec::new();

        for i in 0..self.flaws.len() {
            let current = smt.get_lit_val(self.flaw_phi[i]);
            if current != self.flaw_status[i] {
                #[cfg(feature = "server")]
                let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: FlawId(i), status: current });

                if current == Some(false) {
                    affected_flaws.push(FlawId(i));
                }

                self.flaw_status[i] = current;
            }
        }

        for i in 0..self.resolvers.len() {
            let current = smt.get_lit_val(self.resolver_rho[i]);
            if current != self.resolver_status[i] {
                #[cfg(feature = "server")]
                let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: ResolverId(i), status: current });

                if current == Some(false) {
                    if let Some(res) = self.resolvers[i].as_ref() {
                        affected_flaws.push(res.flaw());
                    }
                }

                self.resolver_status[i] = current;
            }
        }

        if !affected_flaws.is_empty() {
            self.propagate_costs(smt, affected_flaws.as_slice());
        }
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

    pub(super) fn propagate_costs(&mut self, smt: &SeMiTONE, initial_flaws: &[FlawId]) {
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
