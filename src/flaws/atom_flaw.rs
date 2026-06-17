use crate::{
    ToJson,
    flaws::{Flaw, FlawData, FlawId, Resolver, ResolverData, ResolverId},
    solver::SolverError,
    solver_state::SolverState,
};
use linarith::Rational;
use riddle::{
    core::Core,
    env::{AtomId, BoolExpr, Env},
    scope::{Predicate, get_predicate_by_path},
};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::VecDeque,
    rc::{Rc, Weak},
};
use watchsat::{LBool, VarId, neg, pos};

pub(crate) struct AtomFlaw {
    flw: FlawData,
    atom_id: AtomId,
}

impl AtomFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, cause: Option<ResolverId>, atom: AtomId) -> Box<Self> {
        Box::new(Self { flw: FlawData::new(slv, id, phi, cause.into_iter().collect()), atom_id: atom })
    }
}

impl Flaw for AtomFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.flw.solver()
    }
    fn id(&self) -> FlawId {
        self.flw.id()
    }
    fn phi(&self) -> VarId {
        self.flw.phi()
    }
    fn causes(&self) -> Vec<ResolverId> {
        self.flw.causes()
    }
    fn supports(&self) -> Vec<ResolverId> {
        self.flw.supports()
    }
    fn add_support(&mut self, support_id: ResolverId) {
        self.flw.add_support(support_id);
    }
    fn resolvers(&self) -> Vec<ResolverId> {
        self.flw.resolvers()
    }
    fn is_expanded(&self) -> bool {
        self.flw.is_expanded()
    }

    fn compute_resolvers(&mut self) {
        let solver = self.solver();
        let atom = solver.get_atom(self.atom_id).expect("Flaw's atom should exist");
        for atom_id in atom.predicate().atoms() {
            if atom_id == self.atom_id {
                continue; // No need to unify an atom with itself
            }
            if !solver.is_expanded(atom_id) {
                continue; // Only unify with expanded atoms
            }
            let sigma = solver.get_sigma(atom_id);
            if solver.sat.borrow().value(sigma) == LBool::False {
                continue; // Can't unify with an atom that is already unified with another atom
            }

            let rho = solver.sat.borrow_mut().add_var();
            let res_id = ResolverId(solver.get_resolvers_len());
            let res = UnifyAtom::new(self.flw.slv.clone(), res_id, self.id(), rho, self.atom_id, atom_id);
            solver.add_resolver(self, res);
        }
        let rho = if self.resolvers().is_empty() { self.phi() } else { self.solver().sat.borrow_mut().add_var() };
        let res_id = ResolverId(self.solver().get_resolvers_len());
        if atom.is_fact() {
            let res = ActivateFact::new(self.flw.slv.clone(), res_id, self.id(), rho, self.atom_id);
            self.solver().add_resolver(self, res);
        } else {
            let res = ActivateGoal::new(self.flw.slv.clone(), res_id, self.id(), rho, self.atom_id);
            self.solver().add_resolver(self, res);
        }
        self.flw.set_expanded();
    }

    fn add_resolver(&mut self, resolver_id: ResolverId) {
        self.flw.add_resolver(resolver_id);
    }

    fn cost(&self) -> Rational {
        self.flw.cost()
    }
    fn set_cost(&mut self, cost: Rational) {
        self.flw.set_cost(cost);
    }
}

impl ToJson for AtomFlaw {
    fn to_json(&self) -> Value {
        json!({
            "kind": "atom",
            "atom": format!("{}", self.atom_id),
        })
    }
}

struct UnifyAtom {
    res: ResolverData,
    atom: AtomId,
    target: AtomId,
    ac_constraints: RefCell<Vec<ac3rm::ConstraintId>>,
    lin_guard: linarith::GuardId,
}

impl UnifyAtom {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, atom: AtomId, target: AtomId) -> Box<Self> {
        let solver = slv.upgrade().expect("Solver has been dropped");
        Box::new(Self {
            res: ResolverData::new(slv, id, flaw, rho, Rational::from(1)),
            atom,
            target,
            ac_constraints: RefCell::new(vec![]),
            lin_guard: solver.lin.borrow_mut().add_guard(),
        })
    }
}

impl Resolver for UnifyAtom {
    fn solver(&self) -> Rc<SolverState> {
        self.res.solver()
    }
    fn id(&self) -> ResolverId {
        self.res.id()
    }
    fn flaw(&self) -> FlawId {
        self.res.flaw()
    }
    fn rho(&self) -> VarId {
        self.res.rho()
    }
    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
    }

    fn apply(&mut self) -> Result<(), SolverError> {
        let solver = self.solver();
        let atom = solver.get_atom(self.atom).expect("Flaw's atom should exist");
        let target = solver.get_atom(self.target).expect("Target atom should exist");
        solver.add_causal_link(solver.get_atom_flaw(target.id()), self.id());
        // If rho is true, then the source atom must be unified
        solver.sat.borrow_mut().add_clause(vec![neg(self.rho()), neg(solver.get_sigma(self.atom))]).expect("Failed to add clause for UnifyAtom resolver");
        // If rho is true, then the target atom must be active
        solver.sat.borrow_mut().add_clause(vec![neg(self.rho()), pos(solver.get_sigma(self.target))]).expect("Failed to add clause for UnifyAtom resolver");

        let mut terms: Vec<Rc<BoolExpr>> = Vec::new();
        let mut pred_q: VecDeque<Rc<Predicate>> = VecDeque::new();
        pred_q.push_back(atom.predicate());
        while let Some(pred) = pred_q.pop_front() {
            for (_, name) in pred.args() {
                terms.push(Rc::new(BoolExpr::Eq {
                    var_type: Rc::downgrade(&solver.bool_type()),
                    left: atom.get(name).expect("Atom should have the argument"),
                    right: target.get(name).expect("Target atom should have the argument"),
                }));
            }
            for super_pred in pred.parents() {
                pred_q.push_back(get_predicate_by_path(pred.as_ref(), super_pred).expect("Predicate should exist"));
            }
        }

        if !solver.assert(Rc::new(BoolExpr::And { var_type: Rc::downgrade(&solver.bool_type()), terms })) {
            return Err(SolverError::RuntimeError("Failed to unify atoms due to a contradiction".into()));
        }
        Ok(())
    }
    fn requirements(&self) -> Vec<FlawId> {
        self.res.requirements()
    }

    fn ac_constraints(&self) -> Option<Vec<ac3rm::ConstraintId>> {
        Some(self.ac_constraints.borrow().clone())
    }
    fn lin_guard(&self) -> Option<linarith::GuardId> {
        Some(self.lin_guard)
    }
}

impl ToJson for UnifyAtom {
    fn to_json(&self) -> Value {
        json!({
            "kind": "unify",
            "atom": format!("{}", self.atom),
            "target": format!("{}", self.target),
        })
    }
}

struct ActivateFact {
    res: ResolverData,
    atom: AtomId,
}

impl ActivateFact {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, atom: AtomId) -> Box<Self> {
        Box::new(Self { res: ResolverData::new(slv, id, flaw, rho, Rational::from(1)), atom })
    }
}

impl Resolver for ActivateFact {
    fn solver(&self) -> Rc<SolverState> {
        self.res.solver()
    }
    fn id(&self) -> ResolverId {
        self.res.id()
    }
    fn flaw(&self) -> FlawId {
        self.res.flaw()
    }
    fn rho(&self) -> VarId {
        self.res.rho()
    }
    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
    }

    fn apply(&mut self) -> Result<(), SolverError> {
        let solver = self.solver();
        solver.sat.borrow_mut().add_clause(vec![neg(self.rho()), pos(solver.get_sigma(self.atom))]).expect("Failed to add clause for ActivateFact resolver");
        Ok(())
    }
    fn requirements(&self) -> Vec<FlawId> {
        self.res.requirements()
    }
}

impl ToJson for ActivateFact {
    fn to_json(&self) -> Value {
        json!({
            "kind": "fact",
            "atom": format!("{}", self.atom),
        })
    }
}

struct ActivateGoal {
    res: ResolverData,
    atom: AtomId,
    ac_constraints: RefCell<Vec<ac3rm::ConstraintId>>,
    lin_guard: linarith::GuardId,
}

impl ActivateGoal {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, atom: AtomId) -> Box<Self> {
        let solver = slv.upgrade().expect("Solver has been dropped");
        Box::new(Self {
            res: ResolverData::new(slv, id, flaw, rho, Rational::from(1)),
            atom,
            ac_constraints: RefCell::new(vec![]),
            lin_guard: solver.lin.borrow_mut().add_guard(),
        })
    }
}

impl Resolver for ActivateGoal {
    fn solver(&self) -> Rc<SolverState> {
        self.res.solver()
    }
    fn id(&self) -> ResolverId {
        self.res.id()
    }
    fn flaw(&self) -> FlawId {
        self.res.flaw()
    }
    fn rho(&self) -> VarId {
        self.res.rho()
    }
    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
    }

    fn apply(&mut self) -> Result<(), SolverError> {
        let solver = self.solver();
        let atom = solver.get_atom(self.atom).expect("Flaw's atom should exist");
        atom.predicate().call(atom.clone()).map_err(|e| SolverError::RuntimeError(format!("Failed to execute goal atom: {}", e)))?;
        let solver = self.solver();
        solver.sat.borrow_mut().add_clause(vec![neg(self.rho()), pos(solver.get_sigma(self.atom))]).expect("Failed to add clause for ActivateGoal resolver");
        Ok(())
    }
    fn requirements(&self) -> Vec<FlawId> {
        self.res.requirements()
    }
    fn add_requirement(&mut self, flaw_id: FlawId) {
        self.res.add_requirement(flaw_id);
    }

    fn ac_constraints(&self) -> Option<Vec<ac3rm::ConstraintId>> {
        Some(self.ac_constraints.borrow().clone())
    }
    fn lin_guard(&self) -> Option<linarith::GuardId> {
        Some(self.lin_guard)
    }
}

impl ToJson for ActivateGoal {
    fn to_json(&self) -> Value {
        json!({
            "kind": "goal",
            "atom": format!("{}", self.atom),
        })
    }
}
