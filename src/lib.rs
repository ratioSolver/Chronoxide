use crate::{
    flaws::{atom_flaw::AtomFlaw, clause_flaw::ClauseFlaw, disjunction_flaw::DisjunctionFlaw, enum_flaw::EnumFlaw},
    graph::{CausalGraph, Flaw, FlawId, FlawState, Resolver, ResolverId},
    heuristics::{ActiveHeuristic, Heuristic, finite_probe_pairs, finite_probe_resolvers},
    mutex::MutexTable,
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
    search::SearchState,
    timelines::{Timeline, consumable_resource::ConsumableResource, reusable_resource::ReusableResource, state_variable::StateVariable},
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    delegate_env, delegate_scope,
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, Var, to_cnf},
    language::{AtomKind, Disjunction, ResolutionConstraint},
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use semitone::{
    Lit, SeMiTONE, ast,
    rational::{InfRational, Rational},
};
use serde_json::{Value, json};
use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    error, fmt,
    rc::{Rc, Weak},
    str::FromStr,
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};

mod flaws;
mod graph;
mod heuristics;
mod mutex;
mod objects;
mod search;
mod timelines;

#[derive(Default)]
struct ProbeCache {
    unary: HashSet<Lit>,
    binary: HashSet<(Lit, Lit)>,
}

impl ProbeCache {
    #[inline]
    fn norm_lits(a: Lit, b: Lit) -> (Lit, Lit) {
        if a <= b { (a, b) } else { (b, a) }
    }

    fn mark_unary(&mut self, lit: Lit) -> bool {
        self.unary.insert(lit)
    }

    fn mark_binary(&mut self, a: Lit, b: Lit) -> bool {
        self.binary.insert(Self::norm_lits(a, b))
    }
}

enum Decision {
    Frontier(Lit),
    Agenda(Lit),
}

struct Planner {
    graph: CausalGraph,
    mutex: MutexTable,
    search: SearchState,
    heuristic: ActiveHeuristic,
    probes: ProbeCache,
}

impl Planner {
    fn new() -> Self {
        Self {
            graph: CausalGraph::new(),
            mutex: MutexTable::new(),
            search: SearchState::new(),
            heuristic: ActiveHeuristic::new(),
            probes: ProbeCache::default(),
        }
    }
}

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    pub(crate) smt: RefCell<SeMiTONE>,
    notified_len: Cell<usize>,
    planner: RefCell<Planner>,
    /// Currently executing resolver during `Resolver::apply`, used by `riddle::Core` callbacks.
    active_resolver: Cell<Option<ResolverId>>,
    pub(crate) atom_sigma: RefCell<Vec<Option<ResolverId>>>,
    pub(crate) atom_flaw: RefCell<Vec<FlawId>>,
    timelines: RefCell<Vec<Rc<dyn Timeline>>>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl SolverState {
    fn new(tx_event: broadcast::Sender<SolverEvent>) -> Rc<Self> {
        let slv = Rc::new_cyclic(|core| SolverState {
            core: {
                let core: Weak<SolverState> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            smt: RefCell::new(SeMiTONE::new()),
            notified_len: Cell::new(0),
            planner: RefCell::new(Planner::new()),
            active_resolver: Cell::new(None),
            atom_sigma: RefCell::new(Vec::new()),
            atom_flaw: RefCell::new(Vec::new()),
            timelines: RefCell::new(Vec::new()),
            tx_event,
        });
        if slv.read(include_str!("init.rddl")).is_err() {
            panic!("Failed to initialize solver");
        }
        slv.add_timeline(StateVariable::new(Rc::downgrade(&slv) as _));
        slv.add_timeline(ReusableResource::new(Rc::downgrade(&slv) as _));
        slv.add_timeline(ConsumableResource::new(Rc::downgrade(&slv) as _));
        slv
    }

    pub fn add_timeline(&self, timeline: Rc<dyn Timeline>) {
        self.core.add_type(timeline.clone());
        self.timelines.borrow_mut().push(timeline);
    }

    fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::runtime(format!("Failed to read RiDDle script: {:?}", e)))
    }

    fn solve(&self) -> Result<(), SolverError> {
        info!("Solving problem...");
        loop {
            // 1. Propagate SAT/theory constraints and sync search state.
            let prop_result = self.smt.borrow_mut().propagate();
            if let Err((bt_level, lemma)) = prop_result {
                let mut smt = self.smt.borrow_mut();
                let mut planner = self.planner.borrow_mut();
                if !self.backtrack_and_learn(&mut smt, &mut planner, bt_level, lemma) {
                    return Err(SolverError::Inconsistent);
                }
                continue;
            }

            self.sync_trail();
            self.refresh_heuristic();

            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::StateUpdate { json: self.to_json() });

            let lvl = self.smt.borrow().decision_level();
            let active_frontier = {
                let p = self.planner.borrow();
                p.search.has_active_frontier(&p.graph)
            };

            // 2. Graph expansion (always executed at decision level 0).
            if active_frontier && lvl > 0 {
                trace!("Bounded search hit frontier, expanding conflict frontier...");
                let phis = {
                    let p = self.planner.borrow();
                    p.search.conflict_frontier_phis(&p.graph)
                };
                self.cancel_until(0);
                for phi in phis {
                    self.expand_phi_group(phi)?;
                }
                continue;
            }

            let needs_level0_expansion = lvl == 0
                && (active_frontier || {
                    let p = self.planner.borrow();
                    !p.heuristic.has_estimated_solution(&p.graph, &p.mutex, &p.search)
                });
            if needs_level0_expansion {
                trace!("Expanding graph...");
                let phi = {
                    let p = self.planner.borrow();
                    p.heuristic.pick_phi_to_expand(&p.graph, &p.mutex, &p.search)
                }
                .ok_or(SolverError::Inconsistent)?;
                self.expand_phi_group(phi)?;
                continue;
            }

            // 3. Level-0 theory mutex probing.
            if lvl == 0 && self.probe_level0_mutexes()? {
                continue;
            }

            // 4. Branch on an unassigned frontier literal or an active agenda flaw.
            trace!("Picking branching literal...");
            match self.pick_branching_literal() {
                Some(Decision::Frontier(phi)) => {
                    let new_lvl = {
                        let mut smt = self.smt.borrow_mut();
                        smt.decide(!phi);
                        smt.decision_level()
                    };
                    self.planner.borrow_mut().search.on_frontier_decision(new_lvl, phi);
                    continue;
                }
                Some(Decision::Agenda(rho)) => {
                    self.smt.borrow_mut().decide(rho);
                    continue;
                }
                None => {}
            }

            // 5. No open flaws left: check timelines for resource/state-variable conflicts.
            trace!("No more decisions to make, checking timelines for new flaws...");
            let mut extracted_flaws = Vec::new();
            for timeline in self.timelines.borrow().iter() {
                extracted_flaws.extend(timeline.extract_flaws(self)?);
            }
            if !extracted_flaws.is_empty() {
                trace!("Extracted {} new flaws from timelines", extracted_flaws.len());
                self.cancel_until(0);
                let mut new_flaws = Vec::with_capacity(extracted_flaws.len());
                for (flaw, causes) in extracted_flaws {
                    new_flaws.push(self.add_flaw(causes, flaw)?);
                }
                self.sync_trail();
                for flw_id in new_flaws {
                    self.expand_flaw(flw_id)?;
                }
                continue;
            }

            trace!("No more decisions to make, solution found");
            break;
        }
        Ok(())
    }

    /// Probes unprobed finite-cost resolvers (unary) and agenda/sibling pairs (binary) at decision level 0.
    /// Returns `true` if any new theory mutex or level-0 propagation occurred.
    fn probe_level0_mutexes(&self) -> Result<bool, SolverError> {
        let mut learned = false;

        let unary_candidates = {
            let p = self.planner.borrow();
            finite_probe_resolvers(&p.heuristic, &p.graph, &p.mutex, &p.search)
        };

        {
            let mut smt = self.smt.borrow_mut();
            let mut planner = self.planner.borrow_mut();
            trace!("Running unary level-0 probes ({} candidates)...", unary_candidates.len());
            for r in unary_candidates {
                let rho = planner.graph.resolver(r).rho;
                if smt.get_lit_val(rho).is_some() || !planner.probes.mark_unary(rho) {
                    continue;
                }
                match smt.probe(&[rho]) {
                    Ok(true) => {}
                    Ok(false) => {
                        trace!("Inconsistent resolver detected via level-0 probe: {} ({})", r, rho);
                        self.add_clause_with(&mut smt, &mut planner, vec![!rho])?;
                        learned = true;
                    }
                    Err(_) => return Err(SolverError::Inconsistent),
                }
            }
            learned |= self.sync_trail_with(&smt, &mut planner);
        }

        if learned {
            return Ok(true);
        }

        let binary_candidates = {
            let p = self.planner.borrow();
            finite_probe_pairs(&p.heuristic, &p.graph, &p.mutex, &p.search)
        };

        {
            let mut smt = self.smt.borrow_mut();
            let mut planner = self.planner.borrow_mut();
            trace!("Running binary level-0 probes ({} candidates)...", binary_candidates.len());
            for (r1, r2) in binary_candidates {
                let rho1 = planner.graph.resolver(r1).rho;
                let rho2 = planner.graph.resolver(r2).rho;
                if rho1 == rho2 || planner.mutex.is_res_mutex(r1, r2) || smt.get_lit_val(rho1) == Some(false) || smt.get_lit_val(rho2) == Some(false) || !planner.probes.mark_binary(rho1, rho2) {
                    continue;
                }
                match smt.probe(&[rho1, rho2]) {
                    Ok(true) => {}
                    Ok(false) => {
                        trace!("Theory mutex detected via level-0 probe: {} and {}", r1, r2);
                        let p = &mut *planner;
                        if p.mutex.learn_binary_clause(&p.graph, !rho1, !rho2) {
                            p.heuristic.invalidate();
                        }
                        self.add_clause_with(&mut smt, &mut planner, vec![!rho1, !rho2])?;
                        learned = true;
                    }
                    Err(_) => return Err(SolverError::Inconsistent),
                }
            }
            learned |= self.sync_trail_with(&smt, &mut planner);
        }

        Ok(learned)
    }

    fn pick_branching_literal(&self) -> Option<Decision> {
        let p = self.planner.borrow();

        if let Some((flw_id, phi)) = p.search.next_unassigned_frontier_phi(&p.graph) {
            trace!("Branching on unexpanded flaw {}: {}", flw_id, !phi);
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));
            return Some(Decision::Frontier(phi));
        }

        if let Some((flw_id, res_id)) = p.heuristic.pick_branch(&p.graph, &p.mutex, &p.search) {
            let lit = p.graph.resolver(res_id).rho;
            trace!("Branching on flaw {} (cost={}) with resolver {} ({})", flw_id, p.heuristic.flaw_cost(flw_id), res_id, lit);
            #[cfg(feature = "server")]
            {
                let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));
                let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(res_id)));
            }
            return Some(Decision::Agenda(lit));
        }

        #[cfg(feature = "server")]
        {
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
        }
        None
    }

    fn expand_phi_group(&self, phi: Lit) -> Result<(), SolverError> {
        let flaws = self.planner.borrow().graph.queued_flaws_for_phi(phi);
        for flw_id in flaws {
            self.expand_flaw(flw_id)?;
        }
        Ok(())
    }

    /// Expands a single queued flaw, applies its resolvers, and emits closure and pairwise AMO clauses.
    fn expand_flaw(&self, flw_id: FlawId) -> Result<(), SolverError> {
        let (flaw_payload, phi) = {
            let mut p = self.planner.borrow_mut();
            if p.graph.flaw(flw_id).state != FlawState::Queued || p.search.flaw_val(flw_id) == Some(false) {
                return Ok(());
            }
            let payload = p.graph.begin_expand(flw_id);
            let phi = p.graph.flaw(flw_id).phi;
            (payload, phi)
        };

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));

        flaw_payload.expand(self, flw_id)?;

        let resolvers: Vec<(ResolverId, Lit, Rc<dyn Resolver>)> = {
            let p = self.planner.borrow();
            p.graph
                .flaw(flw_id)
                .resolvers
                .iter()
                .map(|&r| {
                    let data = p.graph.resolver(r);
                    (r, data.rho, Rc::clone(&data.payload))
                })
                .collect()
        };

        for &(res_id, _, ref res_payload) in &resolvers {
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(res_id)));

            let prev = self.active_resolver.replace(Some(res_id));
            let apply_res = res_payload.apply(self, res_id);
            self.active_resolver.set(prev);

            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));

            apply_res?;
        }

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));

        let mut smt = self.smt.borrow_mut();
        let mut planner = self.planner.borrow_mut();
        planner.graph.finish_expand(flw_id);
        planner.heuristic.invalidate();

        // Closure clause: ϕ → (ρ₁ ∨ ... ∨ ρₙ). Skip tautological single-resolver `¬ϕ ∨ ϕ`.
        if !(resolvers.len() == 1 && resolvers[0].1 == phi) {
            let mut clause = Vec::with_capacity(resolvers.len() + 1);
            clause.push(!phi);
            clause.extend(resolvers.iter().map(|&(_, rho, _)| rho));
            self.add_clause_with(&mut smt, &mut planner, clause)?;
        }

        // Pairwise AMO between sibling resolvers: ¬ρᵢ ∨ ¬ρⱼ.
        for i in 0..resolvers.len() {
            for j in (i + 1)..resolvers.len() {
                self.add_clause_with(&mut smt, &mut planner, vec![!resolvers[i].1, !resolvers[j].1])?;
            }
        }

        self.sync_trail_with(&smt, &mut planner);

        // If a binary multi-cause flaw (e.g., a state-variable peak) becomes false at level 0,
        // record the direct mutual exclusion between its two causes.
        if smt.decision_level() == 0 && planner.search.flaw_val(flw_id) == Some(false) {
            let causes = planner.graph.flaw(flw_id).causes.clone();
            if let &[c1, c2] = causes.as_slice()
                && planner.mutex.add_mutex(c1, c2)
            {
                planner.heuristic.invalidate();
            }
        }

        Ok(())
    }

    pub(crate) fn add_flaw(&self, mut causes: Vec<ResolverId>, payload: Rc<dyn Flaw>) -> Result<FlawId, SolverError> {
        causes.sort_unstable();
        causes.dedup();

        let mut smt = self.smt.borrow_mut();
        let mut planner = self.planner.borrow_mut();

        let mut cause_lits = planner.graph.rhos(&causes);
        cause_lits.sort_unstable();
        cause_lits.dedup();

        let phi = match cause_lits.as_slice() {
            [] => Lit::TRUE,
            &[lit] => lit,
            _ => {
                let phi = smt.new_lit();
                // (ρ₁ ∧ ... ∧ ρₙ) → ϕ
                let mut clause: Vec<Lit> = cause_lits.iter().map(|&r| !r).collect();
                clause.push(phi);
                self.add_clause_with(&mut smt, &mut planner, clause)?;
                // ϕ → ρᵢ
                for &rho in &cause_lits {
                    self.add_clause_with(&mut smt, &mut planner, vec![!phi, rho])?;
                }
                phi
            }
        };

        let cost_var = smt.new_dl_var();
        self.wire_flaw_acyclicity(&mut smt, &mut planner, &causes, cost_var)?;

        let status = smt.get_lit_val(phi);
        #[cfg(feature = "server")]
        let (causes_for_evt, data_for_evt) = (causes.clone(), payload.to_json());

        let flw_id = planner.graph.add_flaw(causes, phi, cost_var, payload);
        trace!("Adding flaw: {} ({})", flw_id, phi);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id: flw_id,
            phi: phi.to_string(),
            causes: causes_for_evt.clone(),
            required_by: causes_for_evt,
            status,
            cost: f64::INFINITY,
            data: data_for_evt,
        });

        let entered_agenda = planner.search.on_new_flaw(flw_id, status);
        #[cfg(feature = "server")]
        if entered_agenda {
            let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
        }
        #[cfg(not(feature = "server"))]
        let _ = entered_agenda;

        planner.heuristic.invalidate();
        Ok(flw_id)
    }

    pub(crate) fn add_resolver(&self, flw_id: FlawId, rho: Lit, payload: Rc<dyn Resolver>) -> Result<ResolverId, SolverError> {
        let mut smt = self.smt.borrow_mut();
        let mut planner = self.planner.borrow_mut();

        let (phi, parent_cost_var, causes, siblings) = {
            let f = planner.graph.flaw(flw_id);
            (f.phi, f.cost_var, f.causes.clone(), f.resolvers.clone())
        };

        // ρ → ϕ
        if rho != phi {
            self.add_clause_with(&mut smt, &mut planner, vec![!rho, phi])?;
        }

        let cost_var = smt.new_dl_var();
        let intrinsic = payload.intrinsic_cost();
        self.wire_resolver_acyclicity(&mut smt, &mut planner, rho, parent_cost_var, cost_var, intrinsic)?;

        let status = smt.get_lit_val(rho);
        #[cfg(feature = "server")]
        let (intrinsic_f64, data_for_evt) = (payload.intrinsic_cost().to_f64(), payload.to_json());

        let res_id = planner.graph.add_resolver(flw_id, rho, cost_var, payload);
        trace!("Adding resolver: {} ({}) for flaw {}", res_id, rho, flw_id);

        planner.mutex.on_new_resolver(res_id, &causes, &siblings);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: res_id,
            flaw_id: flw_id,
            rho: rho.to_string(),
            status,
            intrinsic_cost: intrinsic_f64,
            preconditions: Vec::new(),
            data: data_for_evt,
        });

        let solved = planner.search.on_new_resolver(res_id, flw_id, status);
        #[cfg(feature = "server")]
        if solved {
            let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id: flw_id });
        }
        #[cfg(not(feature = "server"))]
        let _ = solved;

        planner.heuristic.invalidate();
        Ok(res_id)
    }

    /// Adds a causal link `res_id → target_res`, wiring `ρ → ρ_target`, unidirectional mutex inheritance,
    /// and the DL acyclicity guard.
    pub(crate) fn add_causal_link(&self, res_id: ResolverId, target_res: ResolverId) -> Result<(), SolverError> {
        let mut smt = self.smt.borrow_mut();
        let mut planner = self.planner.borrow_mut();

        let (rho, res_cost) = {
            let r = planner.graph.resolver(res_id);
            (r.rho, r.cost_var)
        };
        let (target_rho, target_cost, target_intrinsic, target_flaw) = {
            let t = planner.graph.resolver(target_res);
            (t.rho, t.cost_var, t.payload.intrinsic_cost(), t.flaw)
        };

        planner.graph.add_causal_link(res_id, target_res);
        planner.mutex.on_causal_link(res_id, target_res);
        planner.heuristic.invalidate();

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewCausalLink { flaw_id: target_flaw, resolver_id: res_id });
        #[cfg(not(feature = "server"))]
        let _ = target_flaw;

        // ρ → ρ_target
        self.add_clause_with(&mut smt, &mut planner, vec![!rho, target_rho])?;
        // ρ → (cost(ρ) >= cost(ρ_target) + intrinsic_cost(ρ_target))
        self.wire_resolver_acyclicity(&mut smt, &mut planner, rho, res_cost, target_cost, target_intrinsic)
    }

    /// DL acyclicity guard: for every cause `r`, `ρ(r) → (cost(r) >= cost(ϕ))`.
    fn wire_flaw_acyclicity(&self, smt: &mut SeMiTONE, planner: &mut Planner, causes: &[ResolverId], flw_cost: semitone::DlVar) -> Result<(), SolverError> {
        for &res_id in causes {
            let (rho, res_cost) = {
                let r = planner.graph.resolver(res_id);
                (r.rho, r.cost_var)
            };
            let dl_cnstr = self.track_expr_with(smt, planner, ast::BoolExpr::DlGe(res_cost, flw_cost, rug::Rational::from(0)))?;
            self.add_clause_with(smt, planner, vec![!rho, dl_cnstr])?;
        }
        Ok(())
    }

    /// DL acyclicity guard: `rho → (upper >= lower + delta)`.
    fn wire_resolver_acyclicity(&self, smt: &mut SeMiTONE, planner: &mut Planner, rho: Lit, upper: semitone::DlVar, lower: semitone::DlVar, delta: rug::Rational) -> Result<(), SolverError> {
        let dl_cnstr = self.track_expr_with(smt, planner, ast::BoolExpr::DlGe(upper, lower, delta))?;
        self.add_clause_with(smt, planner, vec![!rho, dl_cnstr])
    }

    // --- Convenience accessors for flaws, timelines, and objects ---

    pub(crate) fn new_lit(&self) -> Lit {
        self.smt.borrow_mut().new_lit()
    }

    pub(crate) fn lit_val(&self, lit: Lit) -> Option<bool> {
        self.smt.borrow().get_lit_val(lit)
    }

    pub(crate) fn flaw_phi(&self, flw_id: FlawId) -> Lit {
        self.planner.borrow().graph.flaw(flw_id).phi
    }

    pub(crate) fn resolver_rho(&self, res_id: ResolverId) -> Lit {
        self.planner.borrow().graph.resolver(res_id).rho
    }

    pub(crate) fn is_resolver_active(&self, res_id: ResolverId) -> bool {
        let rho = self.resolver_rho(res_id);
        self.smt.borrow().get_lit_val(rho) == Some(true)
    }

    pub(crate) fn is_flaw_expanded(&self, flw_id: FlawId) -> bool {
        self.planner.borrow().graph.is_expanded(flw_id)
    }

    pub(crate) fn is_ancestor(&self, anc: ResolverId, flw_id: FlawId) -> bool {
        self.planner.borrow().graph.is_ancestor(anc, flw_id)
    }

    pub(crate) fn is_flaw_res_mutex(&self, flw_id: FlawId, res_id: ResolverId) -> bool {
        let p = self.planner.borrow();
        p.mutex.is_flaw_res_mutex(&p.graph, flw_id, res_id)
    }

    pub(crate) fn track_expr(&self, expr: impl AsRef<ast::BoolExpr>) -> Result<Lit, SolverError> {
        let mut smt = self.smt.borrow_mut();
        let mut planner = self.planner.borrow_mut();
        self.track_expr_with(&mut smt, &mut planner, expr)
    }

    pub(crate) fn add_clause(&self, clause: impl IntoIterator<Item = Lit>) -> Result<(), SolverError> {
        let mut smt = self.smt.borrow_mut();
        let mut planner = self.planner.borrow_mut();
        self.add_clause_with(&mut smt, &mut planner, clause)
    }

    fn track_expr_with(&self, smt: &mut SeMiTONE, planner: &mut Planner, expr: impl AsRef<ast::BoolExpr>) -> Result<Lit, SolverError> {
        loop {
            match smt.track_expr(&expr) {
                Ok(lit) => return Ok(lit),
                Err((bt_level, lemma)) => {
                    if !self.backtrack_and_learn(smt, planner, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    fn add_clause_with(&self, smt: &mut SeMiTONE, planner: &mut Planner, clause: impl IntoIterator<Item = Lit>) -> Result<(), SolverError> {
        let clause: Vec<Lit> = clause.into_iter().collect();
        loop {
            match smt.add_clause(clause.clone()) {
                Ok(()) => return Ok(()),
                Err((bt_level, lemma)) => {
                    if !self.backtrack_and_learn(smt, planner, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    fn sync_trail(&self) -> bool {
        let smt = self.smt.borrow();
        let mut planner = self.planner.borrow_mut();
        self.sync_trail_with(&smt, &mut planner)
    }

    fn sync_trail_with(&self, smt: &SeMiTONE, planner: &mut Planner) -> bool {
        let current_len = smt.current_trail_len();
        let prev_len = self.notified_len.get();
        if current_len <= prev_len {
            return false;
        }
        let delta = smt.get_trail_delta(prev_len);
        self.notified_len.set(current_len);
        let Planner { graph, search, heuristic, .. } = planner;
        if search.propagate(graph, delta, &self.tx_event) {
            heuristic.invalidate();
        }
        true
    }

    fn refresh_heuristic(&self) {
        let updates = {
            let mut p = self.planner.borrow_mut();
            let Planner { graph, mutex, search, heuristic, .. } = &mut *p;
            heuristic.ensure_fresh(graph, mutex, search)
        };
        #[cfg(feature = "server")]
        for (flaw_id, cost) in updates {
            let _ = self.tx_event.send(SolverEvent::FlawCostUpdate { flaw_id, cost });
        }
        #[cfg(not(feature = "server"))]
        let _ = updates;
    }

    fn backtrack_and_learn(&self, smt: &mut SeMiTONE, planner: &mut Planner, bt_level: usize, lemma: Vec<Lit>) -> bool {
        if smt.decision_level() == 0 {
            return false;
        }
        if lemma.len() == 2 && planner.mutex.learn_binary_clause(&planner.graph, lemma[0], lemma[1]) {
            planner.heuristic.invalidate();
        }
        let vars_to_undo = smt.cancel_until(bt_level);
        self.notified_len.set(smt.current_trail_len());
        let Planner { graph, search, heuristic, .. } = planner;
        if search.cancel_until(graph, bt_level, &vars_to_undo, &self.tx_event) {
            heuristic.invalidate();
        }
        smt.add_clause(lemma).is_ok()
    }

    fn cancel_until(&self, bt_level: usize) {
        let mut smt = self.smt.borrow_mut();
        let mut planner = self.planner.borrow_mut();
        let vars_to_undo = smt.cancel_until(bt_level);
        self.notified_len.set(smt.current_trail_len());
        let Planner { graph, search, heuristic, .. } = &mut *planner;
        if search.cancel_until(graph, bt_level, &vars_to_undo, &self.tx_event) {
            heuristic.invalidate();
        }
    }

    fn current_causes(&self) -> Vec<ResolverId> {
        self.active_resolver.get().into_iter().collect()
    }

    fn to_json(&self) -> Value {
        let smt = self.smt.borrow();
        let env = to_json(&smt, self);
        let mut objects_map = serde_json::Map::new();
        for object in &self.core.get_objects() {
            let mut obj = json!({
                "class": object.class().full_name(),
                "env": to_json(&smt, object.as_ref()),
            });
            if let Some(name) = self.core.get_object_name(object.id()) {
                obj["name"] = json!(name);
            }
            objects_map.insert(object.id().to_string(), obj);
        }
        let mut atoms_map = serde_json::Map::new();
        for atom in &self.core.get_atoms() {
            atoms_map.insert(
                atom.id().to_string(),
                json!({
                    "predicate": atom.predicate().full_name(),
                    "fact": match atom.kind() {
                        AtomKind::Fact => true,
                        AtomKind::Goal => false,
                    },
                    "env": to_json(&smt, atom.as_ref()),
                }),
            );
        }

        drop(smt);

        let mut timelines_map = serde_json::Map::new();
        for timeline in self.timelines.borrow().iter() {
            let timeline_json = timeline.to_json(self);
            if let Value::Object(map) = timeline_json {
                timelines_map.extend(map);
            }
        }

        json!({
            "env": env,
            "objects": Value::Object(objects_map),
            "atoms": Value::Object(atoms_map),
            "flaws": Vec::<Value>::new(),
            "resolvers": Vec::<Value>::new(),
            "timelines": Value::Object(timelines_map),
        })
    }
}

delegate_scope!(SolverState, core);
delegate_env!(SolverState, core);

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Slot {
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), if value { ast::BoolExpr::True } else { ast::BoolExpr::False })))
    }
    fn new_bool_var(&self) -> Slot {
        let var = self.smt.borrow_mut().new_bool();
        let causes = self.current_causes();
        self.add_flaw(causes, Rc::new(ClauseFlaw::new(vec![var.clone(), !var.clone()]))).expect("Failed to add ClauseFlaw to graph");
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), var)))
    }
    fn new_int(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), ast::ArithExpr::Const(rug::Rational::from_str(value).expect("Invalid integer literal")))))
    }
    fn new_int_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), self.smt.borrow_mut().new_int())))
    }
    fn new_real(&self, num: &str, den: &str) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), ast::ArithExpr::Const(rug::Rational::from_str(&format!("{}/{}", num, den)).expect("Invalid rational literal")))))
    }
    fn new_real_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), self.smt.borrow_mut().new_real())))
    }
    fn new_string(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), value.into())))
    }
    fn new_string_var(&self) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), String::new())))
    }

    fn sum(&self, sum: &[Slot]) -> Result<Slot, RiddleError> {
        Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_type(self, sum)?, ast::ArithExpr::Add(sum.iter().map(extract_arith).collect::<Result<Vec<_>, _>>()?)))))
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        if let Slot::Primitive(p) = &term {
            if let Some(bool_var) = p.downcast::<BoolVar>() {
                Ok(Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), ast::BoolExpr::Not(Box::new(bool_var.lit.clone()))))))
            } else if let Some(arith_var) = p.downcast::<ArithVar>() {
                Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_var.var_type().clone(), ast::ArithExpr::Neg(Box::new(arith_var.lin.clone()))))))
            } else {
                Err(RiddleError::TypeError(format!("Expected a boolean variable, got {}", term)))
            }
        } else {
            Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", term)))
        }
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_type(self, mul)?, ast::ArithExpr::Mul(mul.iter().map(extract_arith).collect::<Result<Vec<_>, _>>()?)))))
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_type(self, &[left.clone(), right.clone()])?, ast::ArithExpr::Div(Box::new(extract_arith(&left)?), Box::new(extract_arith(&right)?))))))
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        let expr = match self.track_expr(expr_to_bool(&term)) {
            Ok(lit) => lit,
            Err(_) => return false,
        };

        if let Some(res_id) = self.active_resolver.get() {
            let rho = self.resolver_rho(res_id);
            if self.add_clause(vec![!rho, expr]).is_err() {
                return false;
            }
        } else if self.add_clause(vec![expr]).is_err() {
            return false;
        }

        let cnf_expr = to_cnf(&term);
        match cnf_expr.as_ref() {
            BoolExpr::And { terms, .. } => {
                for clause in terms {
                    if let BoolExpr::Or { terms, .. } = clause.as_ref()
                        && terms.len() > 1
                    {
                        let causes = self.current_causes();
                        let terms = terms.iter().map(expr_to_bool).collect::<Vec<_>>();
                        self.add_flaw(causes, Rc::new(ClauseFlaw::new(terms))).expect("Failed to add ClauseFlaw to graph");
                    }
                }
            }
            BoolExpr::Or { terms, .. } if terms.len() > 1 => {
                let causes = self.current_causes();
                let terms = terms.iter().map(expr_to_bool).collect::<Vec<_>>();
                self.add_flaw(causes, Rc::new(ClauseFlaw::new(terms))).expect("Failed to add ClauseFlaw to graph");
            }
            _ => {}
        }

        true
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        if instances.is_empty() {
            return Err(RiddleError::InconsistencyError(format!("Cannot create a new variable of type {} with no instances", tp.full_name())));
        }

        let var = self.smt.borrow_mut().new_enum(instances.iter().map(|&id| usize::from(id)));
        let causes = self.current_causes();
        self.add_flaw(causes, Rc::new(EnumFlaw::new(var.clone(), instances.to_vec()))).expect("Failed to add EnumFlaw to graph");
        Ok(Slot::Primitive(Rc::new(EnumVar::new(self.slv.clone(), tp, var))))
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        let causes = self.current_causes();
        self.add_flaw(causes, Rc::new(DisjunctionFlaw::new(disjunction))).expect("Failed to add DisjunctionFlaw to graph");
    }

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        let obj = self.core.new_object(class.clone());
        trace!("Created new object {} of class {}", obj, class.full_name());
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewObject { obj_id: obj, name: self.core.get_object_name(obj), class: class.full_name() });
        obj
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        self.core.get_object(id)
    }
    fn new_atom(&self, predicate: Rc<Predicate>, kind: AtomKind, args: HashMap<String, Slot>, resolution_constraint: ResolutionConstraint) -> Result<AtomId, RiddleError> {
        let atm = self.core.new_atom(predicate.clone(), kind, args, resolution_constraint)?;
        trace!("Created new atom {} with predicate {}", atm, predicate.full_name());
        #[cfg(feature = "server")]
        {
            let smt = self.smt.borrow();
            let _ = self.tx_event.send(SolverEvent::NewAtom {
                atom_id: atm,
                predicate: predicate.full_name(),
                kind,
                args: to_json(&smt, self.core.get_atom(atm).expect("Atom should exist in core").as_ref()),
                resolution_constraint,
            });
        }
        self.atom_sigma.borrow_mut().push(None);
        let causes = self.current_causes();
        let flaw = self.add_flaw(causes, Rc::new(AtomFlaw::new(atm))).expect("Failed to add AtomFlaw to graph");
        self.atom_flaw.borrow_mut().push(flaw);
        Ok(atm)
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

#[derive(Debug)]
pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

impl SolverError {
    fn runtime(msg: impl Into<String>) -> Self {
        Self::RuntimeError(msg.into())
    }
}

impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverError::RuntimeError(msg) => write!(f, "Runtime error: {msg}"),
            SolverError::Inconsistent => write!(f, "Problem is inconsistent"),
        }
    }
}

impl error::Error for SolverError {}

#[derive(Clone)]
pub enum SolverEvent {
    NewObject { obj_id: ObjectId, name: Option<String>, class: String },
    NewAtom { atom_id: AtomId, predicate: String, kind: AtomKind, args: Value, resolution_constraint: ResolutionConstraint },
    NewFlaw { flaw_id: FlawId, phi: String, causes: Vec<ResolverId>, required_by: Vec<ResolverId>, status: Option<bool>, cost: f64, data: Value },
    FlawCostUpdate { flaw_id: FlawId, cost: f64 },
    FlawStatusUpdate { flaw_id: FlawId, status: Option<bool> },
    CurrentFlaw(Option<FlawId>),
    NewResolver { resolver_id: ResolverId, rho: String, flaw_id: FlawId, preconditions: Vec<FlawId>, intrinsic_cost: f64, status: Option<bool>, data: Value },
    ResolverStatusUpdate { resolver_id: ResolverId, status: Option<bool> },
    CurrentResolver(Option<ResolverId>),
    NewCausalLink { flaw_id: FlawId, resolver_id: ResolverId },
    ToSolveFlaw { flaw_id: FlawId },
    SolvedFlaw { flaw_id: FlawId },
    StateUpdate { json: Value },
}

fn bool_expr(p: &Rc<dyn Var>) -> Option<ast::BoolExpr> {
    if let Some(var) = p.downcast::<BoolVar>() { Some(var.lit.clone()) } else { p.downcast::<BoolExpr>().map(expr_to_bool) }
}

fn expr_to_bool(expr: impl AsRef<BoolExpr>) -> ast::BoolExpr {
    match expr.as_ref() {
        BoolExpr::Term { term, .. } => {
            if let Slot::Primitive(var) = term
                && let Some(var) = var.downcast::<BoolVar>()
            {
                return var.lit.clone();
            }
            unreachable!("Expected BoolVar in BoolExpr::Term");
        }
        BoolExpr::Eq { left, right, .. } => eq_to_bool(left, right),
        BoolExpr::Lt { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>())
            {
                return left.lin.lt(&right.lin);
            }
            unreachable!("Expected compatible primitive types in BoolExpr::Lt");
        }
        BoolExpr::Leq { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>())
            {
                return left.lin.le(&right.lin);
            }
            unreachable!("Expected compatible primitive types in BoolExpr::Leq");
        }
        BoolExpr::Or { terms, .. } => ast::BoolExpr::Or(terms.iter().map(expr_to_bool).collect::<Vec<_>>()),
        BoolExpr::And { terms, .. } => ast::BoolExpr::And(terms.iter().map(expr_to_bool).collect::<Vec<_>>()),
        BoolExpr::Not { term, .. } => !expr_to_bool(term),
    }
}

fn eq_to_bool(left: &Slot, right: &Slot) -> ast::BoolExpr {
    match (left, right) {
        (Slot::Primitive(left), Slot::Primitive(right)) => {
            if let (Some(left), Some(right)) = (bool_expr(left), bool_expr(right)) {
                return left.eq(&right);
            } else if let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>()) {
                return left.lin.eq(&right.lin);
            } else if let (Some(left), Some(right)) = (left.downcast::<EnumVar>(), right.downcast::<EnumVar>()) {
                return left.var.eq(&right.var);
            } else if let (Some(left), Some(right)) = (left.downcast::<StringVar>(), right.downcast::<StringVar>()) {
                return if left.value == right.value { ast::BoolExpr::True } else { ast::BoolExpr::False };
            }
        }
        (Slot::Primitive(left), Slot::ObjectRef(right)) => {
            if let Some(left) = left.downcast::<EnumVar>() {
                if left.var_type().as_class().is_some_and(|c| !c.instances().contains(right)) {
                    return ast::BoolExpr::False;
                }
                return left.var.eq(usize::from(*right));
            }
        }
        (Slot::ObjectRef(left), Slot::Primitive(right)) => {
            if let Some(right) = right.downcast::<EnumVar>() {
                if right.var_type().as_class().is_some_and(|c| !c.instances().contains(left)) {
                    return ast::BoolExpr::False;
                }
                return right.var.eq(usize::from(*left));
            }
        }
        (Slot::ObjectRef(left), Slot::ObjectRef(right)) => {
            return if left == right { ast::BoolExpr::True } else { ast::BoolExpr::False };
        }
        _ => return ast::BoolExpr::False,
    }
    unreachable!("Expected compatible types in equality");
}

fn extract_arith(slot: &Slot) -> Result<ast::ArithExpr, RiddleError> {
    if let Slot::Primitive(p) = slot
        && let Some(arith_var) = p.downcast::<ArithVar>()
    {
        return Ok(arith_var.lin.clone());
    }
    Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", slot)))
}

fn to_json(smt: &SeMiTONE, env: &dyn Env) -> Value {
    let mut env_json = serde_json::Map::new();
    for (name, slot) in env.get_slots() {
        match slot {
            Slot::Primitive(p) => {
                if let Some(bool_expr) = bool_expr(&p) {
                    match smt.get_bool_val(&bool_expr) {
                        Some(val) => {
                            env_json.insert(name, json!(val));
                        }
                        None => {
                            env_json.insert(name, json!({ "type": "bool_var", "lit": bool_expr.to_string() }));
                        }
                    }
                } else if let Some(arith_var) = p.downcast::<ArithVar>() {
                    let value = smt.get_arith_val(&arith_var.lin).expect("Expected an arithmetic variable to have a value");
                    env_json.insert(name, inf_rat_to_json(&value));
                } else if let Some(string_var) = p.downcast::<StringVar>() {
                    env_json.insert(name, json!(string_var.value));
                } else if let Some(enum_var) = p.downcast::<EnumVar>() {
                    if let Some(val) = smt.get_enum_val(&enum_var.var) {
                        env_json.insert(
                            name,
                            json!({
                                "type": "object_ref",
                                "id": format!("obj-{}", val)
                            }),
                        );
                    } else {
                        env_json.insert(
                            name,
                            json!({
                                "type": "enum_var",
                                "var": enum_var.var.to_string()
                            }),
                        );
                    }
                } else {
                    unreachable!("Unexpected primitive type in slot {}", name);
                }
            }
            Slot::ObjectRef(obj_id) => {
                env_json.insert(
                    name,
                    json!({
                        "type": "object_ref",
                        "id": obj_id.to_string()
                    }),
                );
            }
            Slot::AtomRef(atm_id) => {
                env_json.insert(
                    name,
                    json!({
                        "type": "atom_ref",
                        "id": atm_id.to_string()
                    }),
                );
            }
        }
    }
    Value::Object(env_json)
}

pub fn inf_rat_to_json(val: &InfRational) -> Value {
    let mut json = rat_to_json(val.rational_part());
    if !val.infinitesimal_part().is_zero() {
        let inf = val.infinitesimal_part();
        json.as_object_mut().unwrap().insert(
            String::from("inf"),
            json!({
                "num": inf.numer().to_string(),
                "den": inf.denom().to_string()
            }),
        );
    }
    json
}

pub fn rat_to_json(val: &Rational) -> Value {
    match val {
        Rational::Finite(r) => json!({
            "num": r.numer().to_string(),
            "den": r.denom().to_string()
        }),
        Rational::PositiveInf => json!({
            "num": 1,
            "den": 0
        }),
        Rational::NegativeInf => json!({
            "num": -1,
            "den": 0
        }),
    }
}

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

#[derive(Clone)]
pub struct Solver {
    tx_cmd: mpsc::Sender<SolverCommand>,
    pub tx_event: broadcast::Sender<SolverEvent>,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Self {
        let (tx_cmd, mut rx_cmd) = mpsc::channel(100);
        let (tx_event, _) = broadcast::channel(100);
        let tx_event_clone = tx_event.clone();
        tokio::task::spawn_blocking(move || {
            let state = SolverState::new(tx_event_clone);

            while let Some(cmd) = rx_cmd.blocking_recv() {
                match cmd {
                    SolverCommand::ReadRiDDle(riddle, responder) => {
                        let result = state.read(&riddle);
                        let is_err = result.is_err();
                        let _ = responder.send(result);
                        if is_err {
                            break;
                        }
                    }
                    SolverCommand::Solve(responder) => {
                        let result = state.solve();
                        let is_err = result.is_err();
                        let _ = responder.send(result);
                        if is_err {
                            break;
                        }
                    }
                    SolverCommand::ToJson(responder) => {
                        let _ = responder.send(Ok(state.to_json()));
                    }
                }
            }
        });
        Self { tx_cmd, tx_event }
    }

    async fn send_command<T>(&self, make_cmd: impl FnOnce(CommandResult<T>) -> SolverCommand) -> Result<T, SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(make_cmd(reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Solver worker terminated: {e}")))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Solver worker dropped response: {e}")))?
    }

    pub async fn read(&self, riddle: impl Into<String>) -> Result<(), SolverError> {
        let riddle = riddle.into();
        self.send_command(|tx| SolverCommand::ReadRiDDle(riddle, tx)).await
    }

    pub async fn solve(&self) -> Result<(), SolverError> {
        self.send_command(SolverCommand::Solve).await
    }

    pub async fn to_json(&self) -> Result<Value, SolverError> {
        self.send_command(SolverCommand::ToJson).await
    }
}
