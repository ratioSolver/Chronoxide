use crate::{
    ToJson,
    objects::EnumVar,
    solver::{SolverError, SolverState},
};
use linarith::Rational;
use riddle::{
    env::Atom,
    scope::{Scope, Type},
    serde_json::{Value, json},
};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};
use watchsat::{Lit, VarId, neg, pos};

pub trait Flaw: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> usize;
    fn phi(&self) -> VarId;
    fn causes(&self) -> Vec<usize>;
    fn supports(&self) -> Vec<usize>;
    fn resolvers(&self) -> Vec<usize>;
    fn cost(&self) -> Rational;
    fn set_cost(&self, cost: Rational);
    fn compute_resolvers(self: Rc<Self>, start_id: usize) -> Vec<Rc<dyn Resolver>>;
}

pub struct FlawData {
    slv: Weak<SolverState>,
    id: usize,
    phi: VarId,
    causes: Vec<usize>,
    supports: RefCell<Vec<usize>>,
    resolvers: RefCell<Vec<usize>>,
    cost: RefCell<Rational>,
}

impl FlawData {
    pub fn new(slv: Weak<SolverState>, id: usize, phi: VarId, causes: Vec<usize>) -> Self {
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

    pub fn id(&self) -> usize {
        self.id
    }

    pub fn phi(&self) -> VarId {
        self.phi
    }

    pub fn causes(&self) -> Vec<usize> {
        self.causes.clone()
    }

    pub fn supports(&self) -> Vec<usize> {
        self.supports.borrow().clone()
    }

    pub fn add_support(&self, support_id: usize) {
        self.supports.borrow_mut().push(support_id);
    }

    pub fn resolvers(&self) -> Vec<usize> {
        self.resolvers.borrow().clone()
    }

    pub fn add_resolver(&self, resolver_id: usize) {
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
    fn id(&self) -> usize;
    fn flaw(&self) -> usize;
    fn rho(&self) -> VarId;
    fn apply(&self) -> Result<(), SolverError>;
    fn requirements(&self) -> Vec<usize> {
        Vec::new()
    }
    fn intrinsic_cost(&self) -> Rational;
    fn ac_constraints(&self) -> Option<Vec<ac3rm::ConstraintId>> {
        None
    }
    fn add_ac_constraint(&self, _constraint: ac3rm::ConstraintId) {
        unimplemented!()
    }
    fn lin_constraints(&self) -> Option<linarith::GuardId> {
        None
    }
}

pub struct ResolverData {
    slv: Weak<SolverState>,
    id: usize,
    flaw: usize,
    rho: VarId,
    requirements: Vec<usize>,
    intrinsic_cost: Rational,
}

impl ResolverData {
    pub fn new(slv: Weak<SolverState>, id: usize, flaw: usize, rho: VarId, requirements: Vec<usize>, intrinsic_cost: Rational) -> Self {
        Self { slv, id, flaw, rho, requirements, intrinsic_cost }
    }

    pub fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    pub fn id(&self) -> usize {
        self.id
    }

    pub fn flaw(&self) -> usize {
        self.flaw
    }

    pub fn rho(&self) -> VarId {
        self.rho
    }

    pub fn requirements(&self) -> Vec<usize> {
        self.requirements.clone()
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
    lits: Vec<Lit>,
}

impl ClauseFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: usize, phi: VarId, cause: Option<usize>, lits: Vec<Lit>) -> Rc<Self> {
        Rc::new(Self { flw: FlawData::new(slv, id, phi, cause.into_iter().collect()), lits })
    }
}

impl Flaw for ClauseFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.flw.solver()
    }

    fn id(&self) -> usize {
        self.flw.id()
    }

    fn phi(&self) -> VarId {
        self.flw.phi()
    }

    fn causes(&self) -> Vec<usize> {
        self.flw.causes()
    }

    fn supports(&self) -> Vec<usize> {
        self.flw.supports()
    }

    fn resolvers(&self) -> Vec<usize> {
        self.flw.resolvers()
    }

    fn cost(&self) -> Rational {
        self.flw.cost()
    }

    fn set_cost(&self, cost: Rational) {
        self.flw.set_cost(cost);
    }

    fn compute_resolvers(self: Rc<Self>, mut start_id: usize) -> Vec<Rc<dyn Resolver>> {
        let solver = self.solver();
        let mut result: Vec<Rc<dyn Resolver>> = Vec::new();
        for lit in &self.lits {
            solver.sat.borrow_mut().add_clause(vec![!lit, pos(self.phi())]).expect("Failed to add clause for OR flaw resolver");

            let resolver = ClauseResolver::new(self.flw.slv.clone(), start_id, self.id(), *lit);
            start_id += 1;
            self.flw.add_resolver(resolver.id());
            result.push(resolver);
        }
        result
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

pub(crate) struct ClauseResolver {
    res: ResolverData,
    lit: Lit,
}

impl ClauseResolver {
    fn new(slv: Weak<SolverState>, id: usize, flaw: usize, lit: Lit) -> Rc<Self> {
        Rc::new(Self { res: ResolverData::new(slv, id, flaw, lit.var(), Vec::new(), Rational::from(1)), lit })
    }
}

impl Resolver for ClauseResolver {
    fn solver(&self) -> Rc<SolverState> {
        self.res.solver()
    }

    fn id(&self) -> usize {
        self.res.id()
    }

    fn flaw(&self) -> usize {
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
    var: Rc<EnumVar>,
    rhos: RefCell<HashMap<i32, VarId>>,
}

impl EnumFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: usize, phi: VarId, cause: Option<usize>, var: Rc<EnumVar>) -> Rc<Self> {
        Rc::new(Self {
            flw: FlawData::new(slv, id, phi, cause.into_iter().collect()),
            var,
            rhos: RefCell::new(HashMap::new()),
        })
    }
}

impl Flaw for EnumFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.flw.solver()
    }

    fn id(&self) -> usize {
        self.flw.id()
    }

    fn phi(&self) -> VarId {
        self.flw.phi()
    }

    fn causes(&self) -> Vec<usize> {
        self.flw.causes()
    }

    fn supports(&self) -> Vec<usize> {
        self.flw.supports()
    }

    fn resolvers(&self) -> Vec<usize> {
        self.flw.resolvers()
    }

    fn cost(&self) -> Rational {
        self.flw.cost()
    }

    fn set_cost(&self, cost: Rational) {
        self.flw.set_cost(cost);
    }

    fn compute_resolvers(self: Rc<Self>, mut start_id: usize) -> Vec<Rc<dyn Resolver>> {
        let solver = self.solver();
        let vals = solver.ac.borrow().val(self.var.var);
        let num_vals = vals.len();
        let mut result: Vec<Rc<dyn Resolver>> = Vec::new();
        for val in vals {
            let rho = {
                let mut sat = solver.sat.borrow_mut();
                let rho = sat.add_var();
                sat.add_clause(vec![neg(rho), pos(self.phi())]).expect("Failed to add clause for Enum flaw resolver");
                rho
            };

            let resolver = EnumResolver::new(self.flw.slv.clone(), start_id, self.id(), rho, self.var.clone(), val, Rational::new(1, num_vals as i64));
            start_id += 1;
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
        result
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

pub(crate) struct EnumResolver {
    res: ResolverData,
    var: Rc<EnumVar>,
    val: i32,
    ac_constraints: RefCell<Vec<ac3rm::ConstraintId>>,
}

impl EnumResolver {
    fn new(slv: Weak<SolverState>, id: usize, flaw: usize, rho: VarId, var: Rc<EnumVar>, val: i32, intrinsic_cost: Rational) -> Rc<Self> {
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

    fn id(&self) -> usize {
        self.res.id()
    }

    fn flaw(&self) -> usize {
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

impl ToJson for Rational {
    fn to_json(&self) -> Value {
        json!({
            "num": self.num,
            "den": self.den
        })
    }
}

pub(crate) struct AtomFlaw {
    flw: FlawData,
    atom: Rc<Atom>,
}

impl AtomFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: usize, phi: VarId, cause: Option<usize>, atom: Rc<Atom>) -> Rc<Self> {
        Rc::new(Self { flw: FlawData::new(slv, id, phi, cause.into_iter().collect()), atom })
    }
}

impl Flaw for AtomFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.flw.solver()
    }

    fn id(&self) -> usize {
        self.flw.id()
    }

    fn phi(&self) -> VarId {
        self.flw.phi()
    }

    fn causes(&self) -> Vec<usize> {
        self.flw.causes()
    }

    fn supports(&self) -> Vec<usize> {
        self.flw.supports()
    }

    fn resolvers(&self) -> Vec<usize> {
        self.flw.resolvers()
    }

    fn cost(&self) -> Rational {
        self.flw.cost()
    }

    fn set_cost(&self, cost: Rational) {
        self.flw.set_cost(cost);
    }

    fn compute_resolvers(self: Rc<Self>, mut start_id: usize) -> Vec<Rc<dyn Resolver>> {
        unimplemented!()
    }
}

impl ToJson for AtomFlaw {
    fn to_json(&self) -> Value {
        let mut json = self.flw.to_json();
        json["fact"] = self.atom.is_fact().into();
        json["predicate"] = self.atom.predicate().name().into();
        json
    }
}
