use crate::{
    SolverError, SolverState, eq_to_bool,
    graph::{Flaw, Resolver, ResolverId},
};
use riddle::{
    RiddleError,
    core::Core,
    env::{Atom, AtomId, Env},
    language::{AtomKind, ResolutionConstraint},
};
use semitone::{
    Lit,
    ast::{self, BoolExpr::And},
};
use serde_json::{Value, json};
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

        if atom.resolution_constraint() != ResolutionConstraint::CannotUnify && smt.get_lit_val(phi) != Some(false) {
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
                if graph.is_ancestor(target_sigma_res, flw_id) {
                    continue;
                }
                if graph.is_flaw_res_mutex(flw_id, target_sigma_res) {
                    trace!("Skipping unification with {} for atom {} because target resolver {} is mutex with {}", target_atom, self.atom, target_sigma_res, flw_id);
                    continue;
                }
                let target_sigma = graph.rho(target_sigma_res);
                if smt.get_lit_val(target_sigma) == Some(false) {
                    trace!("Skipping unification with {} for atom {} because target resolver is false", target_atom, self.atom);
                    continue;
                }
                let unif_eqs = build_unification_equations(atom.as_ref(), slv.get_atom(target_atom).unwrap_or_else(|| panic!("Target atom {} not found", target_atom)).as_ref());
                if unif_eqs.len() == 1 && unif_eqs[0] == ast::BoolExpr::False {
                    trace!("Skipping unification with {} for atom {} due to statically unsatisfiable unification equations", target_atom, self.atom);
                    continue;
                }
                let eq_lit = if unif_eqs.is_empty() { Lit::TRUE } else { slv.track_expr(&mut smt, &mut graph, And(unif_eqs))? };

                if smt.get_lit_val(phi) == Some(false) {
                    valid_unifications.clear();
                    break;
                }
                if smt.get_lit_val(target_sigma) == Some(false) || smt.get_lit_val(eq_lit) == Some(false) {
                    trace!("Skipping unification with {} for atom {} due to false literal at level 0", target_atom, self.atom);
                    continue;
                }
                trace!("{} can unify with {}", self.atom, target_atom);
                valid_unifications.push((target_atom, target_sigma_res, eq_lit));
            }
        }

        if smt.get_lit_val(phi) == Some(false) {
            return Ok(());
        }

        let can_expand = atom.resolution_constraint() != ResolutionConstraint::MustUnify;
        let total_resolvers = valid_unifications.len() + usize::from(can_expand);
        let sigma = can_expand.then(|| if total_resolvers == 1 { phi } else { smt.new_lit() });

        for (target_atom, target_sigma_res, eq_lit) in valid_unifications {
            let rho = if total_resolvers == 1 { phi } else { smt.new_lit() };
            slv.add_resolver(&mut smt, &mut graph, rho, Box::new(UnificationResolver::new(self.atom, target_atom, target_sigma_res, eq_lit)))?;
        }

        if let Some(rho) = sigma {
            let res_id = match atom.kind() {
                AtomKind::Fact => slv.add_resolver(&mut smt, &mut graph, rho, Box::new(FactResolver::new(self.atom)))?,
                AtomKind::Goal => slv.add_resolver(&mut smt, &mut graph, rho, Box::new(GoalResolver::new(self.atom)))?,
            };
            slv.atom_sigma.borrow_mut()[self.atom] = Some(res_id);
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
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(0)
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "fact",
            "atom": self.atom.to_string()
        })
    }
}

struct UnificationResolver {
    atom: AtomId,
    target_atom: AtomId,
    target_sigma_res: ResolverId,
    eq_lit: Lit,
}

impl UnificationResolver {
    fn new(atom: AtomId, target_atom: AtomId, target_sigma_res: ResolverId, eq_lit: Lit) -> Self {
        Self { atom, target_atom, target_sigma_res, eq_lit }
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

        // ρ → eq_lit (if the current atom unifies, the unification equations must hold)
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.eq_lit])?;

        // Wires ρ → target_sigma, DL cost constraint, and unidirectional mutex inheritance.
        // Note: `!rho ∨ !sigma` is handled by the pairwise AMO clauses in `expand_flaw`.
        slv.add_causal_link(&mut smt, &mut graph, self.target_sigma_res)
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "unification",
            "current_atom": self.atom.to_string(),
            "target_atom": self.target_atom.to_string()
        })
    }
}

fn build_unification_equations(atom_a: &Atom, atom_b: &Atom) -> Vec<ast::BoolExpr> {
    let mut eqs = Vec::new();

    for (name, slot_a) in atom_a.get_slots() {
        if let Some(slot_b) = atom_b.get(&name) {
            let expr = eq_to_bool(&slot_a, &slot_b);
            if expr == ast::BoolExpr::False {
                return vec![ast::BoolExpr::False];
            } else {
                eqs.push(expr);
            }
        }
    }

    eqs
}
