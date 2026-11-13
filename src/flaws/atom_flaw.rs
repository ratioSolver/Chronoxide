use crate::{
    SolverError, SolverState, eq_to_bool,
    graph::{Flaw, Resolver},
};
use riddle::{
    RiddleError,
    core::Core,
    env::{Atom, AtomId, Env},
    language::{AtomKind, ResolutionConstraint},
    scope::{Predicate, get_predicate_by_path},
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

        let mut valid_unifications = Vec::new();

        if atom.resolution_constraint() != ResolutionConstraint::CannotUnify {
            for target in predicate.atoms() {
                if target == self.atom {
                    continue;
                }
                trace!("Checking if {} can unify with {}", self.atom, target);
                let target_flaw = slv.atom_flaw.borrow().get(*target).copied().ok_or(SolverError::RuntimeError(format!("Target atom {} does not have an associated flaw", target)))?;
                if !graph.is_expanded(target_flaw) {
                    trace!("Skipping unification with {} for atom {} because target flaw is not expanded", target, self.atom);
                    continue;
                }
                let Some(target_fg_res) = slv.atom_fg.borrow().get(*target).copied().flatten() else {
                    trace!("Skipping unification with {} for atom {} because target has no fact/goal resolver", target, self.atom);
                    continue;
                };
                let target_fg = graph.rho(target_fg_res);
                if !graph.can_unify(flw_id, target_flaw) || !graph.can_depend_on(flw_id, &[target_flaw]) {
                    trace!("Skipping unification with {} for atom {} because it would create a cycle", target, self.atom);
                    continue;
                }

                let unif_eqs = build_unification_equations(atom.clone(), slv.get_atom(target).ok_or(SolverError::RuntimeError(format!("Target atom {} not found", target)))?, atom.predicate());
                if unif_eqs.first() == Some(&ast::BoolExpr::False) {
                    trace!("Skipping unification with {} for atom {} due to incompatible arguments", target, self.atom);
                    continue;
                }

                let eq_lit = if unif_eqs.is_empty() { Lit::TRUE } else { slv.track_expr(&mut smt, &mut graph, And(unif_eqs))? };

                if smt.probe(&[phi, target_fg, eq_lit]).map_err(|_| SolverError::Inconsistent)? {
                    trace!("{} can unify with {}", self.atom, target);
                    valid_unifications.push((target, target_fg, eq_lit));
                } else {
                    trace!("Skipping unification with {} for atom {} due to unsatisfiable unification equations", target, self.atom);
                }
            }
        }

        let can_expand_as_new = atom.resolution_constraint() != ResolutionConstraint::MustUnify;
        let total_resolvers = valid_unifications.len() + usize::from(can_expand_as_new);

        let self_fg = if can_expand_as_new { Some(if valid_unifications.is_empty() { phi } else { smt.new_lit() }) } else { None };

        for (target, target_fg, eq_lit) in valid_unifications {
            let rho = if total_resolvers == 1 { phi } else { smt.new_lit() };
            slv.add_resolver(&mut smt, &mut graph, Box::new(UnificationResolver::new(self.atom, target, target_fg, eq_lit, self_fg)), rho)?;
        }

        if let Some(rho_fg) = self_fg {
            let res_id = match atom.kind() {
                AtomKind::Fact => slv.add_resolver(&mut smt, &mut graph, Box::new(FactResolver::new(self.atom)), rho_fg)?,
                AtomKind::Goal => slv.add_resolver(&mut smt, &mut graph, Box::new(GoalResolver::new(self.atom)), rho_fg)?,
            };
            slv.atom_fg.borrow_mut()[*self.atom] = Some(res_id);
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
        if let Err(e) = atom.predicate().call(atom) {
            return match e {
                RiddleError::InconsistencyError(msg) => {
                    trace!("GoalResolver inconsistency for atom {}: {}", self.atom, msg);
                    let mut smt = slv.smt.borrow_mut();
                    let mut graph = slv.graph.borrow_mut();
                    let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;
                    slv.add_clause(&mut smt, &mut graph, vec![!rho])
                }
                _ => Err(SolverError::RuntimeError(format!("Failed to apply GoalResolver for atom {}: {}", self.atom, e))),
            };
        }

        Ok(())
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
    target_fg: Lit,
    eq_lit: Lit,
    self_fg: Option<Lit>,
}

impl UnificationResolver {
    fn new(current_atom: AtomId, target_atom: AtomId, target_fg: Lit, eq_lit: Lit, self_fg: Option<Lit>) -> Self {
        Self { current_atom, target_atom, target_fg, eq_lit, self_fg }
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
        let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;

        // ρ → target_fg (il target deve essere attivo come Fact/Goal autonomo, non unificato a sua volta)
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.target_fg])?;
        // ρ → eq_lit (equazioni di unificazione sugli argomenti)
        if self.eq_lit != Lit::TRUE {
            slv.add_clause(&mut smt, &mut graph, vec![!rho, self.eq_lit])?;
        }
        // ρ → ¬self_fg (se l'atomo corrente unifica, non viene attivato come nuovo Fact/Goal)
        if let Some(self_fg) = self.self_fg {
            slv.add_clause(&mut smt, &mut graph, vec![!rho, !self_fg])?;
        }

        let target_flaw = slv.atom_flaw.borrow().get(*self.target_atom).copied().ok_or(SolverError::RuntimeError(format!("Target atom {} does not have an associated flaw", self.target_atom)))?;
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
