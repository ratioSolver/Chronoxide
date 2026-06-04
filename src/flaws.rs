use crate::{
    ToJson,
    objects::EnumVar,
    solver::{SolverError, SolverState},
};
use linarith::Rational;
use riddle::{
    core::Core,
    env::{AtomId, BoolExpr, Env},
    scope::{Predicate, Type, get_predicate_by_path},
};
use serde_json::{Value, json};
use std::{
    any::Any,
    cell::RefCell,
    collections::{HashMap, VecDeque},
    fmt,
    ops::{Deref, DerefMut},
    rc::{Rc, Weak},
};
use tracing::trace;
use watchsat::{LBool, Lit, VarId, neg, pos};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FlawId(pub(crate) usize);

impl Deref for FlawId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for FlawId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ϕ{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ResolverId(pub(crate) usize);

impl Deref for ResolverId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ResolverId {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl fmt::Display for ResolverId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ρ{}", self.0)
    }
}

pub trait Flaw: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> FlawId;
    fn phi(&self) -> VarId;
    fn causes(&self) -> Vec<ResolverId>;
    fn supports(&self) -> Vec<ResolverId>;
    fn resolvers(&self) -> Vec<ResolverId>;
    fn cost(&self) -> Rational;
    fn set_cost(&self, cost: Rational);
    fn compute_resolvers(self: Rc<Self>, start_id: ResolverId) -> Vec<Rc<dyn Resolver>>;
    fn is_expanded(&self) -> bool;
    fn as_any(self: Rc<Self>) -> Rc<dyn Any>;
}

pub struct FlawData {
    slv: Weak<SolverState>,
    id: FlawId,
    phi: VarId,
    causes: Vec<ResolverId>,
    supports: RefCell<Vec<ResolverId>>,
    resolvers: RefCell<Vec<ResolverId>>,
    cost: RefCell<Rational>,
}

impl FlawData {
    pub fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, causes: Vec<ResolverId>) -> Self {
        Self {
            slv,
            id,
            phi,
            causes: causes.clone(),
            supports: RefCell::new(causes),
            resolvers: RefCell::new(Vec::new()),
            cost: RefCell::new(Rational::POSITIVE_INFINITY),
        }
    }

    pub fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    pub fn id(&self) -> FlawId {
        self.id
    }

    pub fn phi(&self) -> VarId {
        self.phi
    }

    pub fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }

    pub fn supports(&self) -> Vec<ResolverId> {
        self.supports.borrow().clone()
    }

    pub fn add_support(&self, support_id: ResolverId) {
        self.supports.borrow_mut().push(support_id);
    }

    pub fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.borrow().clone()
    }

    pub fn add_resolver(&self, resolver_id: ResolverId) {
        self.resolvers.borrow_mut().push(resolver_id);
    }

    pub fn cost(&self) -> Rational {
        *self.cost.borrow()
    }

    pub fn set_cost(&self, cost: Rational) {
        *self.cost.borrow_mut() = cost;
    }

    pub fn to_json(&self) -> Value {
        json!({
            "id": format!("f{}", self.id),
            "phi": *self.phi(),
            "causes": self.causes.iter().map(|id| format!("r{}", id)).collect::<Vec<_>>(),
            "supports": self.supports.borrow().iter().map(|id| format!("r{}", id)).collect::<Vec<_>>(),
            "status": self.solver().sat.borrow().value(self.phi()).to_json(),
            "cost": self.cost.borrow().to_json(),
        })
    }
}

pub trait Resolver: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> ResolverId;
    fn flaw(&self) -> FlawId;
    fn rho(&self) -> VarId;
    fn apply(&self) -> Result<(), SolverError>;
    fn requirements(&self) -> Vec<FlawId> {
        Vec::new()
    }
    fn intrinsic_cost(&self) -> Rational;
    fn ac_constraints(&self) -> Option<Vec<ac3rm::ConstraintId>> {
        None
    }
    fn add_ac_constraint(&self, _constraint: ac3rm::ConstraintId) {
        unimplemented!()
    }
    fn lin_guard(&self) -> Option<linarith::GuardId> {
        None
    }
}

pub struct ResolverData {
    slv: Weak<SolverState>,
    id: ResolverId,
    flaw: FlawId,
    rho: VarId,
    requirements: Vec<FlawId>,
    intrinsic_cost: Rational,
}

impl ResolverData {
    pub fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, requirements: Vec<FlawId>, intrinsic_cost: Rational) -> Self {
        Self { slv, id, flaw, rho, requirements, intrinsic_cost }
    }

    pub fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    pub fn id(&self) -> ResolverId {
        self.id
    }

    pub fn flaw(&self) -> FlawId {
        self.flaw
    }

    pub fn rho(&self) -> VarId {
        self.rho
    }

    pub fn intrinsic_cost(&self) -> Rational {
        self.intrinsic_cost
    }

    pub fn to_json(&self) -> Value {
        json!({
            "id": format!("r{}", self.id),
            "flaw": format!("f{}", self.flaw),
            "requirements": self.requirements.iter().map(|id| format!("f{}", id)).collect::<Vec<_>>(),
            "intrinsic_cost": self.intrinsic_cost.to_json(),
            "status": self.solver().sat.borrow().value(self.rho()).to_json(),
            "rho": *self.rho(),
        })
    }
}

pub(crate) struct ClauseFlaw {
    flw: FlawData,
    expanded: RefCell<bool>,
    lits: Vec<Lit>,
}

impl ClauseFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, cause: Option<ResolverId>, lits: Vec<Lit>) -> Rc<Self> {
        Rc::new(Self {
            flw: FlawData::new(slv, id, phi, cause.into_iter().collect()),
            expanded: RefCell::new(false),
            lits,
        })
    }
}

impl Flaw for ClauseFlaw {
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

    fn cost(&self) -> Rational {
        self.flw.cost()
    }

    fn set_cost(&self, cost: Rational) {
        self.flw.set_cost(cost);
    }

    fn compute_resolvers(self: Rc<Self>, mut start_id: ResolverId) -> Vec<Rc<dyn Resolver>> {
        let solver = self.solver();
        let mut result: Vec<Rc<dyn Resolver>> = Vec::new();
        for lit in &self.lits {
            trace!("Adding resolver {} to satisfy literal {} and solving flaw {}", start_id, lit, self.id());
            solver.sat.borrow_mut().add_clause(vec![!lit, pos(self.phi())]).expect("Failed to add clause for OR flaw resolver");

            let resolver = ClauseResolver::new(self.flw.slv.clone(), start_id, self.id(), *lit);
            *start_id += 1;
            self.flw.add_resolver(resolver.id());
            result.push(resolver);
        }
        *self.expanded.borrow_mut() = true;
        result
    }

    fn is_expanded(&self) -> bool {
        *self.expanded.borrow()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

impl ToJson for ClauseFlaw {
    fn to_json(&self) -> Value {
        let mut json = self.flw.to_json();
        json["kind"] = "clause".into();
        json["lits"] = self.lits.iter().map(|lit| lit.to_string()).collect::<Vec<_>>().into();
        json
    }
}

struct ClauseResolver {
    res: ResolverData,
    lit: Lit,
}

impl ClauseResolver {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, lit: Lit) -> Rc<Self> {
        Rc::new(Self { res: ResolverData::new(slv, id, flaw, lit.var(), Vec::new(), Rational::from(1)), lit })
    }
}

impl Resolver for ClauseResolver {
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

    fn apply(&self) -> Result<(), SolverError> {
        Ok(())
    }

    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
    }
}

impl ToJson for ClauseResolver {
    fn to_json(&self) -> Value {
        let mut json = self.res.to_json();
        json["lit"] = self.lit.to_string().into();
        json
    }
}

pub(crate) struct EnumFlaw {
    flw: FlawData,
    expanded: RefCell<bool>,
    var: Rc<EnumVar>,
    rhos: RefCell<HashMap<i32, VarId>>,
}

impl EnumFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, cause: Option<ResolverId>, var: Rc<EnumVar>) -> Rc<Self> {
        Rc::new(Self {
            flw: FlawData::new(slv, id, phi, cause.into_iter().collect()),
            expanded: RefCell::new(false),
            var,
            rhos: RefCell::new(HashMap::new()),
        })
    }
}

impl Flaw for EnumFlaw {
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

    fn cost(&self) -> Rational {
        self.flw.cost()
    }

    fn set_cost(&self, cost: Rational) {
        self.flw.set_cost(cost);
    }

    fn compute_resolvers(self: Rc<Self>, mut start_id: ResolverId) -> Vec<Rc<dyn Resolver>> {
        let solver = self.solver();
        let vals = solver.ac.borrow().val(self.var.var);
        let num_vals = vals.len();
        let mut result: Vec<Rc<dyn Resolver>> = Vec::new();
        for val in vals {
            let rho = {
                let mut sat = solver.sat.borrow_mut();
                let rho = sat.add_var();
                trace!("Adding resolver {} to assign value {} to variable {:?} and solving flaw {}", start_id, val, self.var.var, self.id());
                sat.add_clause(vec![neg(rho), pos(self.phi())]).expect("Failed to add clause for Enum flaw resolver");
                rho
            };

            let resolver = EnumResolver::new(self.flw.slv.clone(), start_id, self.id(), rho, self.var.clone(), val, Rational::new(1, num_vals as i64));
            *start_id += 1;
            self.flw.add_resolver(resolver.id());
            self.rhos.borrow_mut().insert(val, rho);
            result.push(resolver);
        }
        let c_solver = self.solver().clone();
        solver.ac.borrow_mut().set_listener(self.var.var, {
            let rhos = self.rhos.clone();
            move |_var, c_vals| {
                for (val, rho) in rhos.borrow().iter() {
                    if !c_vals.contains(val) {
                        c_solver.enqueue(neg(*rho));
                    }
                }
            }
        });
        *self.expanded.borrow_mut() = true;
        result
    }

    fn is_expanded(&self) -> bool {
        *self.expanded.borrow()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

impl ToJson for EnumFlaw {
    fn to_json(&self) -> Value {
        let mut json = self.flw.to_json();
        json["kind"] = "enum".into();
        json["var"] = format!("{:?}", self.var.var).into();
        json
    }
}

struct EnumResolver {
    res: ResolverData,
    var: Rc<EnumVar>,
    val: i32,
    ac_constraints: RefCell<Vec<ac3rm::ConstraintId>>,
}

impl EnumResolver {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, var: Rc<EnumVar>, val: i32, intrinsic_cost: Rational) -> Rc<Self> {
        Rc::new(Self {
            res: ResolverData::new(slv, id, flaw, rho, Vec::new(), intrinsic_cost),
            var,
            val,
            ac_constraints: RefCell::new(Vec::new()),
        })
    }
}

impl Resolver for EnumResolver {
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

    fn apply(&self) -> Result<(), SolverError> {
        self.ac_constraints.borrow_mut().push(self.solver().ac.borrow_mut().new_constraint(ac3rm::Constraint::Set(self.var.var, self.val)));
        Ok(())
    }

    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
    }

    fn ac_constraints(&self) -> Option<Vec<ac3rm::ConstraintId>> {
        Some(self.ac_constraints.borrow().clone())
    }
}

impl ToJson for EnumResolver {
    fn to_json(&self) -> Value {
        let mut json = self.res.to_json();
        json["val"] = self.val.into();
        json
    }
}

pub(crate) struct AtomFlaw {
    flw: FlawData,
    expanded: RefCell<bool>,
    atom: AtomId,
    sigma: VarId,
}

impl AtomFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, cause: Option<ResolverId>, atom: AtomId, sigma: VarId) -> Rc<Self> {
        Rc::new(Self {
            flw: FlawData::new(slv, id, phi, cause.into_iter().collect()),
            expanded: RefCell::new(false),
            atom,
            sigma,
        })
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

    fn cost(&self) -> Rational {
        self.flw.cost()
    }

    fn set_cost(&self, cost: Rational) {
        self.flw.set_cost(cost);
    }

    fn compute_resolvers(self: Rc<Self>, mut start_id: ResolverId) -> Vec<Rc<dyn Resolver>> {
        let mut result: Vec<Rc<dyn Resolver>> = Vec::new();
        let solver = self.solver();
        let atom = solver.get_atom(self.atom).expect("Flaw's atom should exist");
        for atom in atom.predicate().atoms() {
            if atom == self.atom {
                continue; // No need to unify an atom with itself
            }
            let trgt_flw = solver.atom_flaw(&atom).expect("Target atom does not have a corresponding flaw");
            if !trgt_flw.is_expanded() {
                continue; // Can't unify with an atom whose flaw hasn't been expanded yet
            }
            let mut sat = solver.sat.borrow_mut();
            if sat.value(trgt_flw.sigma) == LBool::False {
                continue; // Can't unify with an atom that is already unified with another atom
            }

            let rho = {
                let rho = sat.add_var();
                trace!("Adding resolver {} to unify atom {} with atom {} and solving flaw {}", start_id, self.atom, atom, self.id());
                sat.add_clause(vec![neg(rho), pos(self.phi())]).expect("Failed to add clause for Atom flaw resolver");
                rho
            };
            let resolver = UnifyAtom::new(self.flw.slv.clone(), start_id, self.id(), rho, self.atom, atom);
            *start_id += 1;
            self.flw.add_resolver(resolver.id());
            trgt_flw.flw.add_support(resolver.id());
            result.push(resolver);
        }
        let rho = if result.is_empty() { solver.sat.borrow_mut().add_var() } else { self.sigma };
        if atom.is_fact() {
            trace!("Adding resolver {} to activate fact {} and solving flaw {}", start_id, self.atom, self.id());
            solver.sat.borrow_mut().add_clause(vec![neg(rho), pos(self.phi())]).expect("Failed to add clause for Atom flaw resolver");
            let resolver = ActivateFact::new(self.flw.slv.clone(), start_id, self.id(), rho, self.atom);
            self.flw.add_resolver(resolver.id());
            result.push(resolver);
        } else {
            trace!("Adding resolver {} to activate goal {} and solving flaw {}", start_id, self.atom, self.id());
            solver.sat.borrow_mut().add_clause(vec![neg(rho), pos(self.phi())]).expect("Failed to add clause for Atom flaw resolver");
            let resolver = ActivateGoal::new(self.flw.slv.clone(), start_id, self.id(), rho, self.atom);
            self.flw.add_resolver(resolver.id());
            result.push(resolver);
        }

        *self.expanded.borrow_mut() = true;
        result
    }

    fn is_expanded(&self) -> bool {
        *self.expanded.borrow()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

impl ToJson for AtomFlaw {
    fn to_json(&self) -> Value {
        let solver = self.solver();
        let atom = solver.get_atom(self.atom).expect("Flaw's atom should exist");
        let mut json = self.flw.to_json();
        json["fact"] = atom.is_fact().into();
        json["predicate"] = atom.predicate().name().into();
        json["sigma"] = (*self.sigma).into();
        json
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
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, atom: AtomId, target: AtomId) -> Rc<Self> {
        let solver = slv.upgrade().expect("Solver has been dropped");
        Rc::new(Self {
            res: ResolverData::new(slv, id, flaw, rho, Vec::new(), Rational::from(1)),
            atom,
            target,
            ac_constraints: RefCell::new(Vec::new()),
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

    fn apply(&self) -> Result<(), SolverError> {
        let solver = self.solver();
        let atom = solver.get_atom(self.atom).expect("Flaw's atom should exist");
        let target = solver.get_atom(self.target).expect("Target atom should exist");

        let mut terms: Vec<Rc<BoolExpr>> = Vec::new();
        let mut pred_q: VecDeque<Rc<Predicate>> = VecDeque::new();
        pred_q.push_back(atom.predicate());
        while let Some(pred) = pred_q.pop_front() {
            for (_, name) in pred.args() {
                terms.push(Rc::new(BoolExpr::Eq {
                    var_type: Rc::downgrade(&solver.bool_type()),
                    left: atom.get(name).expect("Atom should have the argument").into(),
                    right: target.get(name).expect("Target atom should have the argument").into(),
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

    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
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
        let mut json = self.res.to_json();
        json["atom"] = (*self.atom).into();
        json["target"] = (*self.target).into();
        json
    }
}

struct ActivateFact {
    res: ResolverData,
    atom: AtomId,
}

impl ActivateFact {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, atom: AtomId) -> Rc<Self> {
        Rc::new(Self { res: ResolverData::new(slv, id, flaw, rho, Vec::new(), Rational::from(1)), atom })
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

    fn apply(&self) -> Result<(), SolverError> {
        let solver = self.solver();
        let flaw = solver.atom_flaw(&self.atom).expect("Atom does not have a corresponding flaw");
        solver.sat.borrow_mut().add_clause(vec![neg(self.rho()), pos(flaw.sigma)]).expect("Failed to add clause for ActivateFact resolver");
        Ok(())
    }

    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
    }
}

impl ToJson for ActivateFact {
    fn to_json(&self) -> Value {
        let mut json = self.res.to_json();
        json["atom"] = (*self.atom).into();
        json
    }
}

struct ActivateGoal {
    res: ResolverData,
    atom: AtomId,
    ac_constraints: RefCell<Vec<ac3rm::ConstraintId>>,
    lin_guard: linarith::GuardId,
}

impl ActivateGoal {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, atom: AtomId) -> Rc<Self> {
        let solver = slv.upgrade().expect("Solver has been dropped");
        Rc::new(Self {
            res: ResolverData::new(slv, id, flaw, rho, Vec::new(), Rational::from(1)),
            atom,
            ac_constraints: RefCell::new(Vec::new()),
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

    fn apply(&self) -> Result<(), SolverError> {
        let solver = self.solver();
        let flaw = solver.atom_flaw(&self.atom).expect("Atom does not have a corresponding flaw");
        let atom = solver.get_atom(self.atom).expect("Flaw's atom should exist");
        atom.predicate().call(atom.clone()).map_err(|e| SolverError::RuntimeError(format!("Failed to execute goal atom: {}", e)))?;

        solver.sat.borrow_mut().add_clause(vec![neg(self.rho()), pos(flaw.sigma)]).expect("Failed to add clause for ActivateGoal resolver");
        Ok(())
    }

    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
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
        let mut json = self.res.to_json();
        json["atom"] = (*self.atom).into();
        json
    }
}

impl ToJson for Rational {
    fn to_json(&self) -> Value {
        json!({
            "num": self.num,
            "den": self.den
        })
    }
}
