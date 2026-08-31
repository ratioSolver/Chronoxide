use crate::{
    SolverError, SolverState, eq_to_bool,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use riddle::{
    core::Core,
    env::{Atom, AtomId, Env},
    scope::{Type, get_predicate_by_path},
};
use semitone::ast::{self, BoolExpr};
use std::{collections::HashSet, rc::Rc};

pub(crate) struct AtomFlaw {
    id: FlawId,
    phi: BoolExpr,

    causes: Vec<ResolverId>,
    supports: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    atom: Rc<Atom>,
}

impl AtomFlaw {
    pub(crate) fn new(phi: BoolExpr, cause: Option<ResolverId>, atom: Rc<Atom>) -> Self {
        Self {
            id: 0,
            phi,
            causes: cause.into_iter().collect(),
            supports: Vec::new(),
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
    fn phi(&self) -> &BoolExpr {
        &self.phi
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

    fn expand(&mut self, state: &SolverState) -> Result<Vec<Box<dyn Resolver>>, SolverError> {
        self.is_expanded = true;
        let mut resolvers: Vec<Box<dyn Resolver>> = Vec::new();

        let predicate = self.atom.predicate();

        let rho_strutturale = state.smt.borrow_mut().new_bool();

        if self.atom.is_fact() {
            resolvers.push(Box::new(FactResolver::new(self.id, rho_strutturale, self.atom.id())));
        } else {
            resolvers.push(Box::new(RuleResolver::new(self.id, rho_strutturale, self.atom.clone(), predicate.clone())));
        }

        let forbidden_atoms = if let Some(&primary_cause) = self.causes.first() { state.planner_state.borrow().graph.get_causal_ancestor_atoms(primary_cause) } else { HashSet::new() };
        let candidate_ids = predicate.atoms();

        for target_id in candidate_ids {
            if target_id == self.atom.id() {
                continue;
            }

            if forbidden_atoms.contains(&target_id) {
                tracing::trace!("Unification skipped: Atom {} is a causal ancestor of Atom {}", target_id, self.atom.id());
                continue;
            }

            if let Some(target_atom) = state.get_atom(target_id) {
                let rho_unif = state.smt.borrow_mut().new_bool();

                let unif_eqs = build_unification_equations(&self.atom, &target_atom, &predicate);

                resolvers.push(Box::new(UnificationResolver::new(self.id, rho_unif, self.atom.id(), target_id, unif_eqs)));
            }
        }

        Ok(resolvers)
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
    rho: BoolExpr,
    sub_flaws: Vec<FlawId>,
    atom: Rc<Atom>,
    predicate: Rc<riddle::scope::Predicate>,
}

impl RuleResolver {
    fn new(flaw: FlawId, rho: BoolExpr, atom: Rc<Atom>, predicate: Rc<riddle::scope::Predicate>) -> Self {
        Self { id: 0, flaw, rho, sub_flaws: Vec::new(), atom, predicate }
    }
}

impl Resolver for RuleResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn rho(&self) -> &BoolExpr {
        &self.rho
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }
    fn sub_flaws(&self) -> &[FlawId] {
        &self.sub_flaws
    }

    fn intrinsic_cost(&self) -> f64 {
        10.0
    }

    fn apply(&mut self, state: &SolverState) -> Result<(), SolverError> {
        let atom_sigma = state.planner_state.borrow().atom_sigma.get(*self.atom.id()).copied().ok_or(SolverError::Inconsistent)?;

        if !state.smt.borrow_mut().assert(&ast::BoolExpr::Or(vec![!self.rho.clone(), ast::BoolExpr::Var(atom_sigma)])) {
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
    rho: BoolExpr,
    sub_flaws: Vec<FlawId>,
    atom_id: AtomId,
}

impl FactResolver {
    fn new(flaw: FlawId, rho: BoolExpr, atom_id: AtomId) -> Self {
        Self { id: 0, flaw, rho, sub_flaws: Vec::new(), atom_id }
    }
}

impl Resolver for FactResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn rho(&self) -> &BoolExpr {
        &self.rho
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
        let atom_sigma = state.planner_state.borrow().atom_sigma.get(*self.atom_id).copied().ok_or(SolverError::Inconsistent)?;

        if !state.smt.borrow_mut().assert(&ast::BoolExpr::Or(vec![!self.rho.clone(), ast::BoolExpr::Var(atom_sigma)])) {
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
    rho: BoolExpr,
    sub_flaws: Vec<FlawId>,
    source_atom_id: AtomId,
    target_atom_id: AtomId,
    unification_constraints: Vec<ast::BoolExpr>,
}

impl UnificationResolver {
    fn new(flaw: FlawId, rho: BoolExpr, source_atom_id: AtomId, target_atom_id: AtomId, unification_constraints: Vec<ast::BoolExpr>) -> Self {
        Self {
            id: 0,
            flaw,
            rho,
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
    fn rho(&self) -> &BoolExpr {
        &self.rho
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
        let source_sigma = state.planner_state.borrow().atom_sigma.get(*self.source_atom_id).copied().ok_or(SolverError::Inconsistent)?;
        let target_sigma = state.planner_state.borrow().atom_sigma.get(*self.target_atom_id).copied().ok_or(SolverError::Inconsistent)?;

        let mut conjunction = self.unification_constraints.clone();
        conjunction.push(!ast::BoolExpr::Var(source_sigma));
        conjunction.push(ast::BoolExpr::Var(target_sigma));

        if !state.smt.borrow_mut().assert(&ast::BoolExpr::Or(vec![!self.rho.clone(), ast::BoolExpr::And(conjunction)])) {
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
