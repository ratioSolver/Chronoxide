use crate::{
    ToJson,
    flaws::{Flaw, FlawData, FlawId, Resolver, ResolverData, ResolverId},
    solver::SolverError,
    solver_state::SolverState,
};
use linarith::Rational;
use riddle::env::AtomId;
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};
use watchsat::VarId;

pub(crate) struct AtomFlaw {
    flw: FlawData,
    atom: AtomId,
    sigma: VarId,
}

impl AtomFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, cause: Option<ResolverId>, atom: AtomId, sigma: VarId) -> Box<Self> {
        Box::new(Self { flw: FlawData::new(slv, id, phi, cause.into_iter().collect()), atom, sigma })
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
    fn resolvers(&self) -> Vec<ResolverId> {
        self.flw.resolvers()
    }
    fn is_expanded(&self) -> bool {
        self.flw.is_expanded()
    }

    fn compute_resolvers(&mut self) {
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
            "atom": format!("{}", self.atom),
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

    fn apply(&self) -> Result<(), SolverError> {
        Ok(())
    }
    fn requirements(&self) -> Vec<FlawId> {
        self.res.requirements()
    }

    fn ac_constraints(&self) -> Option<Vec<ac3rm::ConstraintId>> {
        Some(self.ac_constraints.borrow().clone())
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
