use crate::{
    flaws::{atom_flaw::AtomFlaw, bool_flaw::BoolFlaw, clause_flaw::ClauseFlaw, disjunction_flaw::DisjunctionFlaw, enum_flaw::EnumFlaw, residual_flaw::ResidualFlaw},
    graph::{Flaw, FlawId, Graph, Resolver, ResolverId},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
    timelines::{Timeline, consumable_resource::ConsumableResource, reusable_resource::ReusableResource},
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
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
    collections::{HashMap, HashSet, VecDeque},
    rc::{Rc, Weak},
    str::FromStr,
};
use timelines::state_variable::StateVariable;
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};

mod flaws;
mod graph;
mod objects;
mod timelines;

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    timelines: RefCell<Vec<Rc<dyn Timeline>>>,
    smt: RefCell<SeMiTONE>,
    graph: RefCell<Graph>,
    sigma: RefCell<Vec<ast::BoolExpr>>,
    atom_flaw: RefCell<Vec<FlawId>>,
    notified_len: Cell<usize>,
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
            timelines: RefCell::new(Vec::new()),
            smt: RefCell::new(SeMiTONE::new()),
            graph: RefCell::new(Graph::new(tx_event.clone())),
            sigma: RefCell::new(Vec::new()),
            atom_flaw: RefCell::new(Vec::new()),
            notified_len: Cell::new(0),
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
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    fn solve(&self) -> Result<(), SolverError> {
        info!("Solving problem...");
        loop {
            let prop_result = self.smt.borrow_mut().propagate();
            match prop_result {
                Ok(_) => {
                    self.graph.borrow_mut().refresh_costs();
                    let new_literals = self.smt.borrow().get_trail_delta(self.notified_len.get()).to_vec();
                    let mutexes = self.detect_propagation_mutexes(&new_literals);

                    self.graph.borrow_mut().propagate(&new_literals);
                    self.notified_len.set(self.smt.borrow().current_trail_len());
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::StateUpdate { json: self.to_json() });

                    if !mutexes.is_empty() {
                        for (r1, r2) in mutexes {
                            self.add_mutex_residuals(r1, r2)?;
                        }
                        continue;
                    }

                    if !self.graph.borrow().has_estimated_solution() {
                        self.cancel_to_root();

                        trace!("Expanding graph...");
                        let flw_id = self.graph.borrow_mut().pop_flaw().ok_or(SolverError::Inconsistent)?;
                        self.expand_flaw(flw_id)?;
                    } else {
                        trace!("Picking branching literal...");
                        let decision = self.graph.borrow().pick_branching_literal();
                        if let Some(decision_var) = decision {
                            self.graph.borrow_mut().push();
                            self.smt.borrow_mut().decide(decision_var);
                        } else {
                            trace!("No more decisions to make, checking timelines for new flaws...");
                            let mut extracted_flaws = Vec::new();
                            for timeline in self.timelines.borrow().iter() {
                                extracted_flaws.extend(timeline.extract_flaws(self)?);
                            }
                            if !extracted_flaws.is_empty() {
                                trace!("Extracted {} new flaws from timelines", extracted_flaws.len());
                                let mut smt = self.smt.borrow_mut();
                                let mut graph = self.graph.borrow_mut();
                                for (causes, flaw) in extracted_flaws {
                                    self.add_flaw(&mut smt, &mut graph, causes, flaw)?;
                                }
                                self.sync_graph(&smt, &mut graph);
                                continue;
                            }

                            trace!("No more decisions to make, solution found");
                            break;
                        }
                    }
                }
                Err((bt_level, lemma)) => {
                    let mut smt = self.smt.borrow_mut();
                    let mut graph = self.graph.borrow_mut();
                    if !self.backtrack_and_learn(&mut smt, &mut graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
        Ok(())
    }

    /// Backtracks both `smt` and `graph` to decision level 0 and refreshes heuristic costs.
    fn cancel_to_root(&self) {
        if self.smt.borrow().decision_level() > 0 {
            trace!("Backtracking to decision level 0...");
            let mut smt = self.smt.borrow_mut();
            let mut graph = self.graph.borrow_mut();
            let vars_to_undo = smt.cancel_until(0);
            self.notified_len.set(smt.current_trail_len());
            graph.cancel_until(0, &vars_to_undo);
            graph.refresh_costs();
        }
    }

    /// Expands `flw_id`, applies its resolvers, adds the closure clause, and propagates heuristic costs.
    fn expand_flaw(&self, flw_id: FlawId) -> Result<(), SolverError> {
        let mut flaw = self.graph.borrow_mut().take_flaw(flw_id).expect("Flaw should exist in graph");
        flaw.expand(self)?;
        let resolvers = self.graph.borrow().flaw_resolvers(flw_id).to_vec();

        // ϕ → (ρ₁ ∨ ρ₂ ∨ ... ∨ ρₙ) (solving the flaw implies applying at least one of its resolvers)
        let mut clause = Vec::with_capacity(resolvers.len() + 1);
        clause.push(!self.graph.borrow().phi(flw_id));
        for res_id in resolvers {
            clause.push(self.graph.borrow().rho(res_id));
            let mut resolver = self.graph.borrow_mut().take_resolver(res_id).expect("Resolver should exist in graph");
            resolver.apply(self)?;
            self.graph.borrow_mut().return_resolver(resolver);
        }
        {
            let mut smt = self.smt.borrow_mut();
            let mut graph = self.graph.borrow_mut();
            self.add_clause(&mut smt, &mut graph, clause)?;
        }

        let mut graph = self.graph.borrow_mut();
        graph.return_flaw(flaw);
        self.sync_graph(&self.smt.borrow(), &mut graph);
        graph.propagate_costs(&[flw_id]);
        Ok(())
    }

    /// Inspects newly propagated literals at decision level > 0 to detect unit-propagated mutexes (ρ₁ ⊢ ¬ρ₂).
    fn detect_propagation_mutexes(&self, new_literals: &[Lit]) -> Vec<(ResolverId, ResolverId)> {
        let mut mutexes = Vec::new();
        let smt = self.smt.borrow();
        if smt.decision_level() == 0 {
            return mutexes;
        }

        let graph = self.graph.borrow();
        for &lit in new_literals {
            if smt.get_lit_level(lit) == Some(0) {
                continue;
            }
            if let Some(res_ids) = graph.resolvers_for_lit(!lit)
                && let Some(&r2_raw) = res_ids.first()
                && let Some(ants) = smt.get_lit_antecedents(lit)
                && let Some(causes) = self.extract_conflicting_resolvers(&smt, &graph, ants)
                && causes.len() == 1
            {
                let r1 = causes[0];
                for r2 in graph.branching_resolvers(r2_raw) {
                    if graph.resolver_flaw(r1) != graph.resolver_flaw(r2) && !graph.is_causal_ancestor(r1, r2) && !graph.is_causal_ancestor(r2, r1) && !mutexes.contains(&(r1, r2)) && !mutexes.contains(&(r2, r1)) {
                        trace!("Propagation mutex detected: {} and {}", r1, r2);
                        mutexes.push((r1, r2));
                    }
                }
            }
        }

        mutexes
    }

    /// Builds residual flaws in both directions (when acyclic) for a pair of mutually exclusive resolvers.
    fn add_mutex_residuals(&self, r1: ResolverId, r2: ResolverId) -> Result<(), SolverError> {
        self.try_add_residual_for_pair(r1, r2)?;
        self.try_add_residual_for_pair(r2, r1)?;
        Ok(())
    }

    /// Attaches `f2 \ {r2}` as a precondition of `r1`.
    fn try_add_residual_for_pair(&self, r1: ResolverId, r2: ResolverId) -> Result<(), SolverError> {
        let (f1, f2, allowed_resolvers, causes) = {
            let graph = self.graph.borrow();
            let smt = self.smt.borrow();

            if smt.get_lit_val_and_level(graph.rho(r1)) == Some((false, 0)) || smt.get_lit_val_and_level(graph.rho(r2)) == Some((false, 0)) {
                return Ok(());
            }

            let f1 = graph.resolver_flaw(r1);
            let f2 = graph.resolver_flaw(r2);
            if f1 == f2 || !graph.is_expanded(f2) {
                return Ok(());
            }

            let allowed: Vec<ResolverId> = graph.flaw_resolvers(f2).iter().copied().filter(|&r| r != r2 && smt.get_lit_val_and_level(graph.rho(r)) != Some((false, 0))).collect();

            let mut target_preconditions = vec![f2];
            for &r in &allowed {
                for &pre in graph.resolver_preconditions(r) {
                    if !target_preconditions.contains(&pre) {
                        target_preconditions.push(pre);
                    }
                }
            }

            if !graph.can_depend_on(f1, &target_preconditions) {
                return Ok(());
            }

            let mut causes = vec![r1];
            for &c in graph.flaw_causes(f2) {
                if smt.get_lit_val_and_level(graph.rho(c)) != Some((true, 0)) && !causes.contains(&c) {
                    causes.push(c);
                }
            }

            (f1, f2, allowed, causes)
        };

        // Degenerate case: r2 was the only remaining resolver for f2 -> (r1 ∧ causes(f2)) → ¬ϕ2
        if allowed_resolvers.is_empty() {
            let mut smt = self.smt.borrow_mut();
            let mut graph = self.graph.borrow_mut();
            let mut clause: Vec<Lit> = causes.iter().map(|&c| !graph.rho(c)).collect();
            clause.push(!graph.phi(f2));
            return self.add_clause(&mut smt, &mut graph, clause);
        }

        if !self.graph.borrow_mut().register_residual(r1, f2, r2) {
            return Ok(());
        }

        trace!("Creating ResidualFlaw for {} excluding {} as precondition of {}", f2, r2, r1);

        let res_flw_id = {
            let mut smt = self.smt.borrow_mut();
            let mut graph = self.graph.borrow_mut();
            let res_flw = Box::new(ResidualFlaw::new(f2, r2, allowed_resolvers));
            let flw_id = self.add_flaw(&mut smt, &mut graph, causes, res_flw)?;
            graph.remove_from_flaw_q(flw_id);
            graph.add_precondition_to_resolver(r1, flw_id);
            flw_id
        };

        self.expand_flaw(res_flw_id)?;
        self.graph.borrow_mut().propagate_costs(&[f1]);
        Ok(())
    }

    fn extract_conflicting_resolvers(&self, smt: &SeMiTONE, graph: &Graph, clause: &[Lit]) -> Option<Vec<ResolverId>> {
        let mut queue: VecDeque<Lit> = clause.iter().map(|&l| !l).collect();
        let mut visited: HashSet<Lit> = queue.iter().copied().collect();
        let mut raw_resolvers = Vec::new();

        while let Some(p) = queue.pop_front() {
            if smt.get_lit_level(p) == Some(0) {
                continue;
            }

            if let Some(res_ids) = graph.resolvers_for_lit(p) {
                if let Some(&r_id) = res_ids.first() {
                    for b_res in graph.branching_resolvers(r_id) {
                        if smt.get_lit_level(graph.rho(b_res)) != Some(0) && !raw_resolvers.contains(&b_res) {
                            raw_resolvers.push(b_res);
                        }
                    }
                }
                continue;
            }

            if let Some(antecedents) = smt.get_lit_antecedents(p) {
                for &q in antecedents {
                    let premise = !q;
                    if visited.insert(premise) {
                        queue.push_back(premise);
                    }
                }
            } else {
                // `p` is a decision literal that is not a resolver (e.g., `!ϕ` on an unexpanded flaw)
                return None;
            }
        }

        // Filter out any resolver that is already a causal ancestor of another resolver in the conflict
        let resolvers: Vec<ResolverId> = raw_resolvers.iter().copied().filter(|&r_anc| !raw_resolvers.iter().any(|&r_desc| graph.is_causal_ancestor(r_anc, r_desc))).collect();

        Some(resolvers)
    }

    /// Backtracks `smt` and `graph` to `bt_level` and learns `lemma`.
    /// Returns `false` if the conflict is at the root level and cannot be recovered from.
    fn backtrack_and_learn(&self, smt: &mut SeMiTONE, graph: &mut Graph, bt_level: usize, lemma: Vec<Lit>) -> bool {
        if smt.decision_level() == 0 {
            return false;
        }
        let vars_to_undo = smt.cancel_until(bt_level);
        self.notified_len.set(smt.current_trail_len());
        graph.cancel_until(bt_level, &vars_to_undo);
        smt.add_clause(lemma).is_ok()
    }

    /// Notifies `graph` of any SAT literals assigned since the last sync (e.g. forced by a clause
    /// just added), keeping its flaw/resolver status and agenda consistent with `smt`'s trail.
    /// A no-op while a flaw/resolver is checked out (`graph.is_busy()`): the sync is deferred to the
    /// next safe point.
    fn sync_graph(&self, smt: &SeMiTONE, graph: &mut Graph) {
        if graph.is_busy() {
            return;
        }
        let current_len = smt.current_trail_len();
        if current_len > self.notified_len.get() {
            graph.propagate(smt.get_trail_delta(self.notified_len.get()));
        }
        self.notified_len.set(current_len);
    }

    /// Tracks `expr` as a SAT literal. Each time the encoding conflicts, backtracks, learns the
    /// conflict clause and retries: after backtracking to `bt_level`, re-encoding always succeeds
    /// unless the conflict is at the root level, in which case the problem is truly inconsistent.
    pub fn track_expr(&self, smt: &mut SeMiTONE, graph: &mut Graph, expr: impl AsRef<ast::BoolExpr>) -> Result<Lit, SolverError> {
        loop {
            match smt.track_expr(expr.as_ref()) {
                Ok(lit) => {
                    self.sync_graph(smt, graph);
                    return Ok(lit);
                }
                Err((bt_level, lemma)) => {
                    if !self.backtrack_and_learn(smt, graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    /// Adds `clause` to the SAT core, retrying after backtrack-and-learn on conflict (see `track_expr`).
    pub fn add_clause(&self, smt: &mut SeMiTONE, graph: &mut Graph, clause: impl IntoIterator<Item = Lit>) -> Result<(), SolverError> {
        let clause: Vec<Lit> = clause.into_iter().collect();
        loop {
            match smt.add_clause(clause.clone()) {
                Ok(()) => {
                    self.sync_graph(smt, graph);
                    return Ok(());
                }
                Err((bt_level, lemma)) => {
                    if !self.backtrack_and_learn(smt, graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    /// Registers a new flaw: allocates its ϕ literal (and the causes → ϕ clause) in `smt`, then
    /// delegates bookkeeping to `graph`. This is the only place where a flaw's SAT encoding is created.
    pub fn add_flaw(&self, smt: &mut SeMiTONE, graph: &mut Graph, causes: Vec<ResolverId>, flw: Box<dyn Flaw>) -> Result<FlawId, SolverError> {
        let phi = if causes.is_empty() {
            Lit::TRUE
        } else {
            let phi = smt.new_lit();
            // (ρ₁ ∧ ρ₂ ∧ ... ∧ ρₙ) → ϕ (the flaw is active if all its causes are active)
            let mut clause: Vec<Lit> = graph.resolver_rhos(&causes).into_iter().map(|r| !r).collect();
            clause.push(phi);
            self.add_clause(smt, graph, clause)?;
            phi
        };
        let status = smt.get_lit_val(phi);
        let cost = smt.new_dl_var();

        for &res_id in &causes {
            let rho = graph.rho(res_id);
            let res_cost = graph.resolver_cost(res_id);
            // ρ → (cost(ρ) >= cost(ϕ)) (the flaw's cost is bounded by the cost of any of its resolvers)
            let dl_cnstr = self.track_expr(smt, graph, ast::BoolExpr::DlGe(res_cost, cost, rug::Rational::from(0)))?;
            self.add_clause(smt, graph, vec![!rho, dl_cnstr])?;
        }

        Ok(graph.add_flaw(flw, causes, phi, status, cost))
    }

    /// Registers a new resolver for the currently checked-out flaw: adds its ρ → ϕ implication
    /// and DL cost constraint to `smt`, then delegates bookkeeping to `graph`.
    pub fn add_resolver(&self, smt: &mut SeMiTONE, graph: &mut Graph, res: Box<dyn Resolver>, rho: Lit) -> Result<ResolverId, SolverError> {
        assert!(smt.get_lit_val_and_level(rho) != Some((false, 0)), "Cannot add resolver with a false ρ");

        let (flaw_id, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw when adding resolver")))?;
        // ρ → ϕ (applying the resolver implies solving the flaw)
        self.add_clause(smt, graph, vec![!rho, phi])?;

        let cost = smt.new_dl_var();
        let parent_cost_var = graph.flaw_cost(flaw_id);
        // ρ → (cost(ϕ) >= cost(ρ) + intrinsic_cost(ρ))
        let dl_cnstr = self.track_expr(smt, graph, ast::BoolExpr::DlGe(parent_cost_var, cost, res.intrinsic_cost()))?;
        self.add_clause(smt, graph, vec![!rho, dl_cnstr])?;

        let status = smt.get_lit_val(rho);
        Ok(graph.add_resolver(res, rho, status, cost))
    }

    /// Adds a causal link from the current resolver to `flw_id`, wiring the ρ → ϕ clause
    /// and the DL cost constraint into `smt`.
    pub(crate) fn add_causal_link(&self, smt: &mut SeMiTONE, graph: &mut Graph, flw_id: FlawId) -> Result<(), SolverError> {
        let (rho, phi) = graph.add_causal_link(flw_id)?;
        self.add_clause(smt, graph, vec![!rho, phi])?;

        let (res_id, _) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver for DL causal link")))?;
        let res_cost = graph.resolver_cost(res_id);
        let flw_cost = graph.flaw_cost(flw_id);
        // ρ → (cost(ρ) >= cost(ϕ))
        let dl_cnstr = self.track_expr(smt, graph, ast::BoolExpr::DlGe(res_cost, flw_cost, rug::Rational::from(0)))?;
        self.add_clause(smt, graph, vec![!rho, dl_cnstr])
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

impl Scope for SolverState {
    fn core(&self) -> Rc<dyn Core> {
        self.slv.upgrade().expect("SolverState should never be dropped while in use")
    }
    fn scope(&self) -> Option<Rc<dyn Scope>> {
        None
    }

    fn fields(&self) -> Vec<Rc<Field>> {
        self.core.fields()
    }

    fn get_field(&self, name: &str) -> Option<Rc<Field>> {
        self.core.get_field(name)
    }

    fn functions(&self) -> Vec<Rc<Function>> {
        self.core.functions()
    }

    fn get_function(&self, name: &str, types: &[Rc<dyn Type>]) -> Option<Rc<Function>> {
        self.core.get_function(name, types)
    }

    fn types(&self) -> Vec<Rc<dyn Type>> {
        self.core.types()
    }

    fn get_type(&self, name: &str) -> Option<Rc<dyn Type>> {
        self.core.get_type(name)
    }

    fn predicates(&self) -> Vec<Rc<Predicate>> {
        self.core.predicates()
    }

    fn get_predicate(&self, name: &str) -> Option<Rc<Predicate>> {
        self.core.get_predicate(name)
    }
}

impl Env for SolverState {
    fn parent(&self) -> Option<Rc<dyn Env>> {
        None
    }

    fn get_slots(&self) -> HashMap<String, Slot> {
        self.core.get_slots()
    }

    fn get(&self, name: &str) -> Option<Slot> {
        self.core.get(name)
    }

    fn set(&self, name: String, value: Slot) {
        self.core.set(name, value);
    }
}

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Slot {
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), if value { ast::BoolExpr::True } else { ast::BoolExpr::False })))
    }
    fn new_bool_var(&self) -> Slot {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let var = smt.new_bool();
        let causes = graph.current_cause();
        self.add_flaw(&mut smt, &mut graph, causes, Box::new(BoolFlaw::new(var.clone()))).expect("Failed to add BoolFlaw to graph");
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
        let tp = arith_type(self, sum)?;
        let sum = sum
            .iter()
            .map(|s| match s {
                Slot::Primitive(p) => {
                    if let Some(arith_var) = p.downcast::<ArithVar>() {
                        Ok(arith_var.lin.clone())
                    } else {
                        Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", s)))
                    }
                }
                _ => Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", s))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Add(sum)))))
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
        let tp = arith_type(self, mul)?;
        let mul = mul
            .iter()
            .map(|s| match s {
                Slot::Primitive(p) => {
                    if let Some(arith_var) = p.downcast::<ArithVar>() {
                        Ok(arith_var.lin.clone())
                    } else {
                        Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", s)))
                    }
                }
                _ => Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", s))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Mul(mul)))))
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        let tp = arith_type(self, &[left.clone(), right.clone()])?;
        let left_lin = if let Slot::Primitive(p) = &left {
            if let Some(arith_var) = p.downcast::<ArithVar>() {
                arith_var.lin.clone()
            } else {
                return Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", left)));
            }
        } else {
            return Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", left)));
        };
        let right_lin = if let Slot::Primitive(p) = &right {
            if let Some(arith_var) = p.downcast::<ArithVar>() {
                arith_var.lin.clone()
            } else {
                return Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", right)));
            }
        } else {
            return Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", right)));
        };
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Div(Box::new(left_lin), Box::new(right_lin))))))
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();

        let expr = match self.track_expr(&mut smt, &mut graph, expr_to_bool(term.as_ref())) {
            Ok(lit) => lit,
            Err(_) => return false,
        };

        if let Some((_c_res, rho)) = graph.current_resolver() {
            if self.add_clause(&mut smt, &mut graph, vec![!rho, expr]).is_err() {
                return false;
            }
        } else if self.add_clause(&mut smt, &mut graph, vec![expr]).is_err() {
            return false;
        }

        let cnf_expr = to_cnf(term.clone());
        match cnf_expr.as_ref() {
            BoolExpr::And { terms, .. } => {
                for clause in terms {
                    if let BoolExpr::Or { terms, .. } = clause.as_ref()
                        && terms.len() > 1
                    {
                        let causes = graph.current_cause();
                        let terms = terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>();
                        self.add_flaw(&mut smt, &mut graph, causes, Box::new(ClauseFlaw::new(terms))).expect("Failed to add ClauseFlaw to graph");
                    }
                }
            }
            BoolExpr::Or { terms, .. } if terms.len() > 1 => {
                let causes = graph.current_cause();
                let terms = terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>();
                self.add_flaw(&mut smt, &mut graph, causes, Box::new(ClauseFlaw::new(terms))).expect("Failed to add ClauseFlaw to graph");
            }
            _ => {}
        }

        true
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        if instances.is_empty() {
            return Err(RiddleError::InconsistencyError(format!("Cannot create a new variable of type {} with no instances", tp.full_name())));
        }

        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let domain = instances.iter().map(|id| **id as i32).collect::<Vec<_>>();
        let var = smt.new_enum(domain.clone());
        let causes = graph.current_cause();
        self.add_flaw(&mut smt, &mut graph, causes, Box::new(EnumFlaw::new(var.clone(), domain))).expect("Failed to add EnumFlaw to graph");
        Ok(Slot::Primitive(Rc::new(EnumVar::new(self.slv.clone(), tp, var))))
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let causes = graph.current_cause();
        self.add_flaw(&mut smt, &mut graph, causes, Box::new(DisjunctionFlaw::new(disjunction))).expect("Failed to add DisjunctionFlaw to graph");
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
        let mut smt = self.smt.borrow_mut();
        let mut graph = self.graph.borrow_mut();
        let atm = self.core.new_atom(predicate.clone(), kind, args, resolution_constraint)?;
        trace!("Created new atom {} with predicate {}", atm, predicate.full_name());
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewAtom {
            atom_id: atm,
            predicate: predicate.full_name(),
            kind,
            args: to_json(&smt, self.core.get_atom(atm).expect("Atom should exist in core").as_ref()),
            resolution_constraint,
        });
        self.sigma.borrow_mut().push(smt.new_bool());
        let causes = graph.current_cause();
        let flaw = self.add_flaw(&mut smt, &mut graph, causes, Box::new(AtomFlaw::new(atm))).expect("Failed to add AtomFlaw to graph");
        self.atom_flaw.borrow_mut().push(flaw);
        Ok(atm)
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

fn expr_to_bool(expr: &BoolExpr) -> ast::BoolExpr {
    match expr {
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
        BoolExpr::Or { terms, .. } => ast::BoolExpr::Or(terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::And { terms, .. } => ast::BoolExpr::And(terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::Not { term, .. } => !expr_to_bool(term),
    }
}

/// Extracts the SAT expression of a boolean value, either a plain `BoolVar` or a riddle `BoolExpr` wrapping one.
pub(crate) fn bool_expr(p: &Rc<dyn Var>) -> Option<ast::BoolExpr> {
    if let Some(var) = p.downcast::<BoolVar>() { Some(var.lit.clone()) } else { p.downcast::<BoolExpr>().map(|expr| expr_to_bool(&expr)) }
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
            }
        }
        (Slot::Primitive(left), Slot::ObjectRef(right)) => {
            if let Some(left) = left.downcast::<EnumVar>() {
                return left.var.eq(**right as i32);
            }
        }
        (Slot::ObjectRef(left), Slot::Primitive(right)) => {
            if let Some(right) = right.downcast::<EnumVar>() {
                return right.var.eq(**left as i32);
            }
        }
        (Slot::ObjectRef(left), Slot::ObjectRef(right)) => {
            return (**left as i32).eq(&(**right as i32)).into();
        }
        _ => return ast::BoolExpr::False,
    }
    unreachable!("Expected compatible types in equality");
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

    pub async fn read(&self, riddle: String) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ReadRiDDle(riddle, reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send ReadRiDDle command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive ReadRiDDle response: {:?}", e)))?
    }

    pub async fn solve(&self) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::Solve(reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send Solve command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive Solve response: {:?}", e)))?
    }

    pub async fn to_json(&self) -> Result<Value, SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ToJson(reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send ToJson command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive ToJson response: {:?}", e)))?
    }
}

fn to_json(smt: &SeMiTONE, env: &dyn Env) -> Value {
    let mut env_json = serde_json::Map::new();
    for (name, slot) in env.get_slots() {
        match slot {
            Slot::Primitive(p) => {
                if let Some(bool_expr) = bool_expr(&p) {
                    match smt.get_bool_val(&bool_expr) {
                        Some(true) => {
                            env_json.insert(name, json!(true));
                        }
                        Some(false) => {
                            env_json.insert(name, json!(false));
                        }
                        None => {
                            env_json.insert(
                                name,
                                json!({
                                    "type": "bool_var",
                                    "lit": bool_expr.to_string()
                                }),
                            );
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

#[derive(Debug)]
pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

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
