use std::{collections::HashSet, rc::Rc};

use crate::{
    SolverError, SolverState, eq_to_bool,
    graph::{Flaw, FlawId, Resolver},
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
use tracing::{trace, warn};

pub(crate) struct AtomFlaw {
    atom: AtomId,
}

impl AtomFlaw {
    pub(crate) fn new(atom: AtomId) -> Self {
        Self { atom }
    }
}

impl Flaw for AtomFlaw {
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError> {
        let atom = slv.get_atom(self.atom).unwrap_or_else(|| panic!("Atom {} not found", self.atom));
        let predicate = atom.predicate();

        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().expect("No current flaw found");

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
            for target_atom in predicate.atoms() {
                if target_atom == self.atom {
                    continue;
                }
                trace!("Checking if {} can unify with {}", self.atom, target_atom);
                let target_flaw = slv.atom_flaw.borrow()[target_atom];
                if !graph.flaw_expanded(target_flaw) {
                    trace!("Skipping unification with {} for atom {} because target flaw is not expanded", target_atom, self.atom);
                    continue;
                }
                let Some(target_sigma_res) = slv.atom_sigma.borrow()[target_atom] else {
                    trace!("Skipping unification with {} for atom {} because target has no fact/goal resolver", target_atom, self.atom);
                    continue;
                };
                let target_sigma = graph.rho(target_sigma_res);
                let unif_eqs = build_unification_equations(atom.clone(), slv.get_atom(target_atom).unwrap_or_else(|| panic!("Target atom {} not found", target_atom)).clone(), predicate.clone());
                let eq_lit = if unif_eqs.is_empty() { Lit::TRUE } else { slv.track_expr(&mut smt, &mut graph, And(unif_eqs))? };

                if smt.probe(&[phi, target_sigma, eq_lit]).map_err(|_| SolverError::Inconsistent)? {
                    trace!("{} can unify with {}", self.atom, target_atom);
                    valid_unifications.push((target_atom, target_sigma, target_flaw, eq_lit));
                } else {
                    trace!("Skipping unification with {} for atom {} due to unsatisfiable unification equations", target_atom, self.atom);
                }
            }
        }

        let sigma = if atom.resolution_constraint() != ResolutionConstraint::MustUnify {
            let rho = if valid_unifications.is_empty() { phi } else { smt.new_lit() };
            let res_id = match atom.kind() {
                AtomKind::Fact => slv.add_resolver(&mut smt, &mut graph, rho, Box::new(FactResolver::new(self.atom)))?,
                AtomKind::Goal => slv.add_resolver(&mut smt, &mut graph, rho, Box::new(GoalResolver::new(self.atom)))?,
            };
            slv.atom_sigma.borrow_mut()[self.atom] = Some(res_id);
            Some(rho)
        } else {
            None
        };

        let total_resolvers = valid_unifications.len() + usize::from(sigma.is_some());
        for (target_atom, target_sigma, target_flaw, eq_lit) in valid_unifications {
            let rho = if total_resolvers == 1 { phi } else { smt.new_lit() };
            slv.add_resolver(&mut smt, &mut graph, rho, Box::new(UnificationResolver::new(self.atom, sigma, target_atom, target_sigma, target_flaw, eq_lit)))?;
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
    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        trace!("Applying GoalResolver for atom {}", self.atom);
        let atom = slv.get_atom(self.atom).unwrap_or_else(|| panic!("Atom {} not found", self.atom));
        if let Err(e) = atom.predicate().call(atom) {
            return match e {
                RiddleError::InconsistencyError(msg) => {
                    trace!("GoalResolver inconsistency for atom {}: {}", self.atom, msg);
                    let mut smt = slv.smt.borrow_mut();
                    let mut graph = slv.graph.borrow_mut();
                    let (_, rho) = graph.current_resolver().expect("No current resolver found");
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
    atom: AtomId,
    sigma: Option<Lit>,
    target_atom: AtomId,
    target_sigma: Lit,
    target_flaw: FlawId,
    eq_lit: Lit,
}

impl UnificationResolver {
    fn new(atom: AtomId, sigma: Option<Lit>, target_atom: AtomId, target_sigma: Lit, target_flaw: FlawId, eq_lit: Lit) -> Self {
        Self { atom, sigma, target_atom, target_sigma, target_flaw, eq_lit }
    }
}

impl Resolver for UnificationResolver {
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(0)
    }

    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        trace!("Applying UnificationResolver for atoms {} and {}", self.atom, self.target_atom);
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;

        // ρ → target_sigma (if the current atom unifies, the target atom must be activated)
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.target_sigma])?;
        // ρ → eq_lit (if the current atom unifies, the unification equations must hold)
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.eq_lit])?;
        if let Some(sigma) = self.sigma {
            // ρ → !sigma (if the current atom unifies, the current atom's resolver must be deactivated)
            slv.add_clause(&mut smt, &mut graph, vec![!rho, !sigma])?;
        }

        slv.add_causal_link(&mut smt, &mut graph, self.target_flaw)
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "unification",
            "current_atom": self.atom.to_string(),
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
                    warn!("Unification warning: Failed to resolve parent {:?} - {}", parent_path, e);
                }
            }
        }
    }

    eqs
}
