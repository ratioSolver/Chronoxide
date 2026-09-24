use crate::{
    SolverError, SolverState, eq_to_bool,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use riddle::{
    core::Core,
    env::{Atom, AtomId, Env},
    scope::{Predicate, get_predicate_by_path},
};
use semitone::ast::{self, BoolExpr::And};
use serde_json::{Value, json};
use std::{collections::HashSet, rc::Rc};
use tracing::trace;

pub(crate) struct AtomFlaw {
    id: FlawId,

    causes: Vec<ResolverId>,
    required_by: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    atom: AtomId,
}

impl AtomFlaw {
    pub(crate) fn new(cause: Option<ResolverId>, atom: AtomId) -> Self {
        Self {
            id: FlawId::default(),
            causes: cause.into_iter().collect(),
            required_by: cause.into_iter().collect(),
            resolvers: Vec::new(),
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
    fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }

    fn required_by(&self) -> Vec<ResolverId> {
        self.required_by.clone()
    }
    fn add_required_by(&mut self, res_id: ResolverId) {
        self.required_by.push(res_id);
    }

    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        trace!("Expanding AtomFlaw {} for atom: {}", self.id, self.atom);
        let atom = slv.get_atom(self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found", self.atom)))?;

        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let sigma = slv.sigma.borrow();

        for target in atom.predicate().atoms() {
            if target == self.atom {
                continue;
            }
            if !graph.can_unify(slv.atom_flaw.borrow().get(*target).cloned().ok_or(SolverError::RuntimeError(format!("Target atom {} does not have an associated flaw", target)))?) {
                continue;
            }
            let mut unif_eqs = build_unification_equations(atom.clone(), slv.get_atom(target).ok_or(SolverError::RuntimeError(format!("Target atom {} not found", target)))?, atom.predicate());
            unif_eqs.push(!sigma.get(*self.atom).ok_or(SolverError::RuntimeError(format!("Current atom {} not found in sigma", self.atom)))?.clone());
            unif_eqs.push(sigma.get(*target).ok_or(SolverError::RuntimeError(format!("Target atom {} not found in sigma", target)))?.clone());
            let rho = smt.track_expr(And(unif_eqs));
            if smt.get_lit_val(rho) == Some(false) {
                continue;
            }
            self.resolvers.push(graph.add_resolver(&mut smt, Box::new(UnificationResolver::new(self.id, self.atom, target)), rho)?);
        }

        if self.resolvers.is_empty() {
            let (_, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError("No current flaw found".to_string()))?;
            if atom.is_fact() {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(FactResolver::new(self.id, self.atom)), phi)?);
            } else {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(GoalResolver::new(self.id, self.atom)), phi)?);
            }
        } else {
            let rho = smt.new_lit();
            if atom.is_fact() {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(FactResolver::new(self.id, self.atom)), rho)?);
            } else {
                self.resolvers.push(graph.add_resolver(&mut smt, Box::new(GoalResolver::new(self.id, self.atom)), rho)?);
            }
        }

        Ok(())
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "atom",
            "atom": self.atom.to_string()
        })
    }
}

struct GoalResolver {
    id: ResolverId,
    flaw: FlawId,
    atom: AtomId,
}

impl GoalResolver {
    fn new(flaw: FlawId, atom: AtomId) -> Self {
        Self { id: ResolverId::default(), flaw, atom }
    }
}

impl Resolver for GoalResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let atom = slv.get_atom(self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found", self.atom)))?;
        atom.predicate().call(atom).map_err(|e| SolverError::RuntimeError(format!("Failed to apply GoalResolver for atom {}: {}", self.atom, e)))?;

        let (_, rho) = slv.graph.borrow().current_resolver().ok_or(SolverError::RuntimeError("No current resolver found".to_string()))?;
        let mut smt = slv.smt.borrow_mut();
        let sigma = smt.track_expr(slv.sigma.borrow().get(*self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found in sigma", self.atom)))?);
        smt.add_clause(vec![!rho, sigma]).map_err(|_e| SolverError::RuntimeError(format!("Failed to add fact clause for atom {}", self.atom)))
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "goal",
            "atom": self.atom.to_string()
        })
    }
}

struct FactResolver {
    id: ResolverId,
    flaw: FlawId,
    atom: AtomId,
}

impl FactResolver {
    fn new(flaw: FlawId, atom: AtomId) -> Self {
        Self { id: ResolverId::default(), flaw, atom }
    }
}

impl Resolver for FactResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let (_, rho) = slv.graph.borrow().current_resolver().ok_or(SolverError::RuntimeError("No current resolver found".to_string()))?;
        let mut smt = slv.smt.borrow_mut();
        let sigma = smt.track_expr(slv.sigma.borrow().get(*self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found in sigma", self.atom)))?);
        smt.add_clause(vec![!rho, sigma]).map_err(|_e| SolverError::RuntimeError(format!("Failed to add fact clause for atom {}", self.atom)))
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "fact",
            "atom": self.atom.to_string()
        })
    }
}

struct UnificationResolver {
    id: ResolverId,
    flaw: FlawId,
    current_atom: AtomId,
    target_atom: AtomId,
}

impl UnificationResolver {
    fn new(flaw: FlawId, current_atom: AtomId, target_atom: AtomId) -> Self {
        Self { id: ResolverId::default(), flaw, current_atom, target_atom }
    }
}

impl Resolver for UnificationResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(0)
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "unification",
            "current_atom": self.current_atom.to_string(),
            "target_atom": self.target_atom.to_string()
        })
    }
}

fn build_unification_equations(atom_a: Rc<Atom>, atom_b: Rc<Atom>, predicate: Rc<Predicate>) -> Vec<ast::BoolExpr> {
    let mut eqs = Vec::new();
    let mut queue = vec![predicate];
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
