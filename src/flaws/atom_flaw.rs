use crate::{
    SolverError, SolverState, eq_to_bool,
    graph::{Flaw, Resolver},
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
    atom: AtomId,
}

impl AtomFlaw {
    pub(crate) fn new(atom: AtomId) -> Self {
        Self { atom }
    }
}

impl Flaw for AtomFlaw {
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let atom = slv.get_atom(self.atom).ok_or(SolverError::RuntimeError(format!("Atom {} not found", self.atom)))?;
        let predicate = atom.predicate();

        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;

        trace!(
            "Expanding AtomFlaw {} for {} {} with predicate {}",
            flw_id,
            match atom.kind() {
                AtomKind::Fact => "fact",
                AtomKind::Goal => "goal",
            },
            self.atom,
            predicate.name()
        );

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
                if !graph.can_unify(flw_id, target_flaw) {
                    trace!("Skipping unification with {} for atom {} because it would create a cycle", target, self.atom);
                    continue;
                }
                let mut unif_eqs = build_unification_equations(atom.clone(), slv.get_atom(target).ok_or(SolverError::RuntimeError(format!("Target atom {} not found", target)))?, atom.predicate());
                unif_eqs.push(!sigma.get(*self.atom).ok_or(SolverError::RuntimeError(format!("Current atom {} not found in sigma", self.atom)))?.clone());
                unif_eqs.push(sigma.get(*target).ok_or(SolverError::RuntimeError(format!("Target atom {} not found in sigma", target)))?.clone());
                let rho = slv.track_expr(&mut smt, &mut graph, And(unif_eqs))?;
                if smt.get_lit_val_and_level(rho) != Some((false, 0)) {
                    trace!("{} can unify with {}", self.atom, target);
                    slv.add_resolver(&mut smt, &mut graph, Box::new(UnificationResolver::new(self.atom, target)), rho)?;
                } else {
                    trace!("Skipping unification with {} for atom {} due to unsatisfiable unification equations", target, self.atom);
                }
            }
        }

        if atom.resolution_constraint() != ResolutionConstraint::MustUnify {
            let rho = if graph.flaw_resolvers(flw_id).is_empty() { phi } else { smt.new_lit() };
            match atom.kind() {
                AtomKind::Fact => {
                    slv.add_resolver(&mut smt, &mut graph, Box::new(FactResolver::new(self.atom)), rho)?;
                }
                AtomKind::Goal => {
                    slv.add_resolver(&mut smt, &mut graph, Box::new(GoalResolver::new(self.atom)), rho)?;
                }
            }
        }

        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "atom",
            "atom": self.atom.to_string()
        })
    }
}

struct GoalResolver {
    atom: AtomId,
}

impl GoalResolver {
    fn new(atom: AtomId) -> Self {
        Self { atom }
    }
}

impl Resolver for GoalResolver {
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

    fn to_json(&self) -> Value {
        json!({
            "kind": "goal",
            "atom": self.atom.to_string()
        })
    }
}

struct FactResolver {
    atom: AtomId,
}

impl FactResolver {
    fn new(atom: AtomId) -> Self {
        Self { atom }
    }
}

impl Resolver for FactResolver {
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
    current_atom: AtomId,
    target_atom: AtomId,
}

impl UnificationResolver {
    fn new(current_atom: AtomId, target_atom: AtomId) -> Self {
        Self { current_atom, target_atom }
    }
}

impl Resolver for UnificationResolver {
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
                let expr = eq_to_bool(&slot_a, &slot_b);
                if expr == ast::BoolExpr::False {
                    return vec![ast::BoolExpr::False];
                } else {
                    eqs.push(expr);
                }
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
