use crate::{
    SolverError, SolverState, eq_to_bool,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use riddle::{
    core::Core,
    env::{Atom, AtomId, Env},
    scope::{Type, get_predicate_by_path},
};
use semitone::{Lit, ast};
use std::{collections::HashSet, rc::Rc};
use tracing::trace;

pub(crate) struct AtomFlaw {
    id: FlawId,
    phi: Lit,
    status: Option<bool>,

    causes: Vec<ResolverId>,
    supports: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    atom: Rc<Atom>,
}

impl AtomFlaw {
    pub(crate) fn new(phi: Lit, status: Option<bool>, cause: Option<ResolverId>, atom: Rc<Atom>) -> Self {
        assert!(status != Some(false), "Cannot create an AtomFlaw with status Some(false)");
        Self {
            id: FlawId::default(),
            phi,
            status,
            causes: cause.into_iter().collect(),
            supports: cause.into_iter().collect(),
            resolvers: Vec::new(),
            estimated_cost: f64::INFINITY,
            is_expanded: false,
            atom,
        }
    }
}

impl Flaw for AtomFlaw {
    fn id(&self) -> FlawId {
        self.id
    }
    fn set_id(&mut self, id: FlawId) {
        self.id = id;
    }

    fn phi(&self) -> Lit {
        self.phi
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn causes(&self) -> &[ResolverId] {
        &self.causes
    }
    fn supports(&self) -> &[ResolverId] {
        &self.supports
    }
    fn add_support(&mut self, id: ResolverId) {
        self.supports.push(id);
    }
    fn atom_id(&self) -> Option<AtomId> {
        Some(self.atom.id())
    }
    fn resolvers(&self) -> &[ResolverId] {
        &self.resolvers
    }
    fn add_resolver(&mut self, id: ResolverId) {
        self.resolvers.push(id);
    }
    fn estimated_cost(&self) -> f64 {
        self.estimated_cost
    }
    fn set_estimated_cost(&mut self, cost: f64) {
        self.estimated_cost = cost;
    }
    fn is_expanded(&self) -> bool {
        self.is_expanded
    }

    fn expand(&mut self, core: &SolverState) -> Result<(), SolverError> {
        self.is_expanded = true;

        let predicate = self.atom.predicate();

        let forbidden_atoms = if let Some(&primary_cause) = self.causes.first() { core.planner_state.borrow().graph.get_causal_ancestor_atoms(primary_cause) } else { HashSet::new() };
        let candidate_ids = predicate.atoms();

        let mut state = core.planner_state.borrow_mut();
        for target_id in candidate_ids {
            if target_id == self.atom.id() {
                continue;
            }

            if forbidden_atoms.contains(&target_id) {
                trace!("Unification skipped: Atom {} is a causal ancestor of Atom {}", target_id, self.atom.id());
                continue;
            }

            if let Some(target_atom) = core.get_atom(target_id) {
                if let Some(target_res_id) = state.graph.atom_to_res.get(&target_id) {
                    let target_res = state.graph.get_resolver(*target_res_id);
                    if target_res.status() == Some(false) {
                        continue;
                    }

                    let rho = core.smt.borrow_mut().new_lit();
                    let unif_eqs = build_unification_equations(&self.atom, &target_atom, &predicate);
                    self.resolvers.push(state.graph.add_resolver(Box::new(UnificationResolver::new(self.id, rho, None, self.atom.id(), target_id, unif_eqs))));
                }
            }
        }

        let (rho, status) = if self.resolvers.is_empty() { (self.phi, self.status) } else { (core.smt.borrow_mut().new_lit(), None) };
        if self.atom.is_fact() {
            let res_id = state.graph.add_resolver(Box::new(FactResolver::new(self.id, rho, status, self.atom.id())));
            state.graph.atom_to_res.insert(self.atom.id(), res_id);
            self.resolvers.push(res_id);
        } else {
            let res_id = state.graph.add_resolver(Box::new(RuleResolver::new(self.id, rho, status, self.atom.clone(), predicate.clone())));
            state.graph.atom_to_res.insert(self.atom.id(), res_id);
            self.resolvers.push(res_id);
        }

        Ok(())
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "atom",
            "atom_id": *self.atom.id(),
            "predicate": self.atom.predicate().name(),
        })
    }
}

struct RuleResolver {
    id: ResolverId,
    flaw: FlawId,
    rho: Lit,
    status: Option<bool>,
    sub_flaws: Vec<FlawId>,
    atom: Rc<Atom>,
    predicate: Rc<riddle::scope::Predicate>,
}

impl RuleResolver {
    fn new(flaw: FlawId, rho: Lit, status: Option<bool>, atom: Rc<Atom>, predicate: Rc<riddle::scope::Predicate>) -> Self {
        assert!(status != Some(false), "Cannot create a RuleResolver with status Some(false)");
        Self { id: ResolverId::default(), flaw, rho, status, sub_flaws: Vec::new(), atom, predicate }
    }
}

impl Resolver for RuleResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> Lit {
        self.rho
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn sub_flaws(&self) -> &[FlawId] {
        &self.sub_flaws
    }
    fn add_sub_flaw(&mut self, id: FlawId) {
        self.sub_flaws.push(id);
    }

    fn intrinsic_cost(&self) -> f64 {
        10.0
    }

    fn apply(&mut self, state: &SolverState) -> Result<(), SolverError> {
        let atom_sigma = state.planner_state.borrow().atom_sigma.get(*self.atom.id()).cloned().ok_or(SolverError::Inconsistent)?;

        let rho_xpr = if self.rho.sign() { !ast::BoolExpr::Var(self.rho.var()) } else { ast::BoolExpr::Var(self.rho.var()) };
        if !state.smt.borrow_mut().assert(ast::BoolExpr::Or(vec![!rho_xpr, atom_sigma])) {
            return Err(SolverError::Inconsistent);
        }
        self.predicate.clone().call(self.atom.clone()).map_err(|e| SolverError::RuntimeError(format!("Error applying rule: {:?}", e)))?;
        Ok(())
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "rule"
        })
    }
}

struct FactResolver {
    id: ResolverId,
    flaw: FlawId,
    rho: Lit,
    status: Option<bool>,
    sub_flaws: Vec<FlawId>,
    atom_id: AtomId,
}

impl FactResolver {
    fn new(flaw: FlawId, rho: Lit, status: Option<bool>, atom_id: AtomId) -> Self {
        assert!(status != Some(false), "Cannot create a FactResolver with status Some(false)");
        Self { id: ResolverId::default(), flaw, rho, status, sub_flaws: Vec::new(), atom_id }
    }
}

impl Resolver for FactResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> Lit {
        self.rho
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn flaw(&self) -> FlawId {
        self.flaw
    }
    fn sub_flaws(&self) -> &[FlawId] {
        &self.sub_flaws
    }

    fn intrinsic_cost(&self) -> f64 {
        1.0
    }

    fn apply(&mut self, state: &SolverState) -> Result<(), SolverError> {
        let atom_sigma = state.planner_state.borrow().atom_sigma.get(*self.atom_id).cloned().ok_or(SolverError::Inconsistent)?;

        let rho_xpr = if self.rho.sign() { !ast::BoolExpr::Var(self.rho.var()) } else { ast::BoolExpr::Var(self.rho.var()) };
        if !state.smt.borrow_mut().assert(ast::BoolExpr::Or(vec![!rho_xpr, atom_sigma])) {
            return Err(SolverError::Inconsistent);
        }
        Ok(())
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "fact"
        })
    }
}

struct UnificationResolver {
    id: ResolverId,
    flaw: FlawId,
    rho: Lit,
    status: Option<bool>,
    sub_flaws: Vec<FlawId>,
    source_atom_id: AtomId,
    target_atom_id: AtomId,
    unification_constraints: Vec<ast::BoolExpr>,
}

impl UnificationResolver {
    fn new(flaw: FlawId, rho: Lit, status: Option<bool>, source_atom_id: AtomId, target_atom_id: AtomId, unification_constraints: Vec<ast::BoolExpr>) -> Self {
        assert!(status != Some(false), "Cannot create a UnificationResolver with status Some(false)");
        Self {
            id: ResolverId::default(),
            flaw,
            rho,
            status,
            sub_flaws: Vec::new(),
            source_atom_id,
            target_atom_id,
            unification_constraints,
        }
    }
}

impl Resolver for UnificationResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> Lit {
        self.rho
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn flaw(&self) -> FlawId {
        self.flaw
    }
    fn sub_flaws(&self) -> &[FlawId] {
        &self.sub_flaws
    }

    fn intrinsic_cost(&self) -> f64 {
        0.1
    }

    fn apply(&mut self, state: &SolverState) -> Result<(), SolverError> {
        let source_sigma = state.planner_state.borrow().atom_sigma.get(*self.source_atom_id).cloned().ok_or(SolverError::Inconsistent)?;
        let target_sigma = state.planner_state.borrow().atom_sigma.get(*self.target_atom_id).cloned().ok_or(SolverError::Inconsistent)?;

        let mut conjunction = self.unification_constraints.clone();
        conjunction.push(!source_sigma);
        conjunction.push(target_sigma);

        let rho_xpr = if self.rho.sign() { !ast::BoolExpr::Var(self.rho.var()) } else { ast::BoolExpr::Var(self.rho.var()) };
        if !state.smt.borrow_mut().assert(ast::BoolExpr::Or(vec![!rho_xpr, ast::BoolExpr::And(conjunction)])) {
            return Err(SolverError::Inconsistent);
        }
        state.add_causal_link(self.id, self.target_atom_id)?;
        Ok(())
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "unification",
            "source": *self.source_atom_id,
            "target": *self.target_atom_id,
        })
    }
}

fn build_unification_equations(atom_a: &Rc<Atom>, atom_b: &Rc<Atom>, predicate: &Rc<riddle::scope::Predicate>) -> Vec<ast::BoolExpr> {
    let mut eqs = Vec::new();
    let mut queue = vec![predicate.clone()];
    let mut visited = HashSet::new();

    while let Some(curr_pred) = queue.pop() {
        let ptr = Rc::as_ptr(&curr_pred) as usize;
        if !visited.insert(ptr) {
            continue;
        }

        for (_types, arg_name) in curr_pred.args() {
            if let (Some(slot_a), Some(slot_b)) = (atom_a.get(arg_name), atom_b.get(arg_name)) {
                eqs.push(eq_to_bool(&slot_a, &slot_b));
            }
        }

        for parent_path in curr_pred.parents() {
            match get_predicate_by_path(curr_pred.as_ref(), parent_path) {
                Ok(parent_pred) => {
                    queue.push(parent_pred);
                }
                Err(e) => {
                    tracing::warn!("Unification warning: Failed to resolve parent {:?} - {}", parent_path, e);
                }
            }
        }
    }

    eqs
}
