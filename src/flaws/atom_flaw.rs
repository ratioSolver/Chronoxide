use crate::{
    SolverError, SolverState, eq_to_bool,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use riddle::{
    RiddleError,
    core::Core,
    env::{Atom, AtomId, Env},
    language::{AtomKind, ResolutionConstraint},
    scope::{Predicate, Type, get_predicate_by_path},
};
use semitone::{
    Lit,
    ast::{self, BoolExpr::And},
};
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
    fn causes(&self) -> &Vec<ResolverId> {
        &self.causes
    }

    fn required_by(&self) -> &Vec<ResolverId> {
        &self.required_by
    }
    fn add_required_by(&mut self, res_id: ResolverId) {
        self.required_by.push(res_id);
    }

    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let atom = slv.get_atom(self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found", self.atom)))?;
        let predicate = atom.predicate();
        trace!(
            "Expanding AtomFlaw for {} {} with predicate {}",
            match atom.kind() {
                AtomKind::Fact => "fact",
                AtomKind::Goal => "goal",
            },
            self.atom,
            predicate.name()
        );

        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let sigma = slv.sigma.borrow();

        if atom.resolution_constraint() != ResolutionConstraint::CannotUnify {
            for target in predicate.atoms() {
                if target == self.atom {
                    continue;
                }
                trace!("Checking if {} can unify with {}", self.atom, target);
                let target_flaw = slv.atom_flaw.borrow().get(*target).cloned().ok_or(SolverError::RuntimeError(format!("Target atom {} does not have an associated flaw", target)))?;
                if !graph.is_expanded(target_flaw) {
                    trace!("Skipping unification with {} for atom {} because target flaw is not expanded", target, self.atom);
                    continue;
                }
                if !graph.can_unify(self.causes().as_slice(), target_flaw) {
                    trace!("Skipping unification with {} for atom {} because it would create a cycle", target, self.atom);
                    continue;
                }
                let mut unif_eqs = build_unification_equations(atom.clone(), slv.get_atom(target).ok_or(SolverError::RuntimeError(format!("Target atom {} not found", target)))?, atom.predicate());
                unif_eqs.push(!sigma.get(*self.atom).ok_or(SolverError::RuntimeError(format!("Current atom {} not found in sigma", self.atom)))?.clone());
                unif_eqs.push(sigma.get(*target).ok_or(SolverError::RuntimeError(format!("Target atom {} not found in sigma", target)))?.clone());
                let rho = slv.track_expr(&mut smt, &mut graph, And(unif_eqs))?;
                if smt.get_lit_val(rho) == Some(false) {
                    trace!("Skipping unification with {} for atom {} due to unsatisfiable unification equations", target, self.atom);
                    continue;
                }
                trace!("{} can unify with {}", self.atom, target);
                self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(UnificationResolver::new(self.id, self.atom, target)), rho)?);
            }
        }

        if atom.resolution_constraint() != ResolutionConstraint::MustUnify {
            if self.resolvers.is_empty() {
                let (_, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
                match atom.kind() {
                    AtomKind::Fact => {
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(FactResolver::new(self.id, self.atom)), phi)?);
                    }
                    AtomKind::Goal => {
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(GoalResolver::new(self.id, self.atom)), phi)?);
                    }
                }
            } else {
                let rho = smt.new_lit();
                match atom.kind() {
                    AtomKind::Fact => {
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(FactResolver::new(self.id, self.atom)), rho)?);
                    }
                    AtomKind::Goal => {
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(GoalResolver::new(self.id, self.atom)), rho)?);
                    }
                }
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
    preconditions: Vec<FlawId>,
    atom: AtomId,
}

impl GoalResolver {
    fn new(flaw: FlawId, atom: AtomId) -> Self {
        Self { id: ResolverId::default(), flaw, preconditions: vec![], atom }
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
        trace!("Applying GoalResolver for atom {}", self.atom);
        let atom = slv.get_atom(self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found", self.atom)))?;
        match atom.predicate().call(atom) {
            Ok(_) => Ok(()),
            Err(e) => match e {
                RiddleError::InconsistencyError(msg) => {
                    trace!("GoalResolver inconsistency for atom {}: {}", self.atom, msg);
                    slv.add_clause(&mut slv.smt.borrow_mut(), &mut slv.graph.borrow_mut(), vec![Lit::FALSE])
                }
                _ => Err(SolverError::RuntimeError(format!("Failed to apply GoalResolver for atom {}: {}", self.atom, e))),
            },
        }?;

        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;
        let sigma = slv.track_expr(&mut smt, &mut graph, slv.sigma.borrow().get(*self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found in sigma", self.atom)))?.clone())?;
        slv.add_clause(&mut smt, &mut graph, vec![!rho, sigma])
    }

    fn preconditions(&self) -> Vec<FlawId> {
        self.preconditions.clone()
    }

    fn add_precondition(&mut self, flaw_id: FlawId) {
        self.preconditions.push(flaw_id);
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
        trace!("Applying FactResolver for atom {}", self.atom);
        let atom = slv.get_atom(self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found", self.atom)))?;
        let predicate = atom.predicate();
        for parent in predicate.parents() {
            let parent_predicate = get_predicate_by_path(predicate.as_ref(), parent).map_err(|e| SolverError::RuntimeError(format!("Failed to resolve parent predicate {:?} for atom {}: {}", parent, self.atom, e)))?;
            match parent_predicate.call(atom.clone()) {
                Ok(_) => Ok(()),
                Err(e) => match e {
                    RiddleError::InconsistencyError(msg) => {
                        trace!("FactResolver inconsistency for atom {}: {}", self.atom, msg);
                        slv.add_clause(&mut slv.smt.borrow_mut(), &mut slv.graph.borrow_mut(), vec![Lit::FALSE])
                    }
                    _ => Err(SolverError::RuntimeError(format!("Failed to apply FactResolver for atom {}: {}", self.atom, e))),
                },
            }?;
        }

        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;
        let sigma = slv.track_expr(&mut smt, &mut graph, slv.sigma.borrow().get(*self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found in sigma", self.atom)))?.clone())?;
        slv.add_clause(&mut smt, &mut graph, vec![!rho, sigma])
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
    preconditions: Vec<FlawId>,
    current_atom: AtomId,
    target_atom: AtomId,
}

impl UnificationResolver {
    fn new(flaw: FlawId, current_atom: AtomId, target_atom: AtomId) -> Self {
        Self { id: ResolverId::default(), flaw, preconditions: vec![], current_atom, target_atom }
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

    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        trace!("Applying UnificationResolver for atoms {} and {}", self.current_atom, self.target_atom);
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let target_flaw = slv.atom_flaw.borrow().get(*self.target_atom).cloned().ok_or(SolverError::RuntimeError(format!("Target atom {} does not have an associated flaw", self.target_atom)))?;
        slv.add_causal_link(&mut smt, &mut graph, target_flaw)
    }

    fn preconditions(&self) -> Vec<FlawId> {
        self.preconditions.clone()
    }

    fn add_precondition(&mut self, flaw_id: FlawId) {
        self.preconditions.push(flaw_id);
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
