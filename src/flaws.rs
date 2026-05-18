use crate::{
    ToJson,
    objects::EnumVar,
    solver::{SolverError, SolverState},
};
use linarith::Rational;
use riddle::serde_json::{Value, json};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};
use watchsat::{Lit, VarId, neg, pos};

pub trait Flaw: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> usize;
    fn phi(&self) -> VarId;
    fn causes(&self) -> Vec<usize>;
    fn supports(&self) -> Vec<usize> {
        Vec::new()
    }
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
            causes,
            supports: RefCell::new(Vec::new()),
            resolvers: RefCell::new(Vec::new()),
            cost: RefCell::new(Rational::POSITIVE_INFINITY),
        }
    }

    pub fn add_support(&self, support_id: usize) {
        self.supports.borrow_mut().push(support_id);
    }

    pub fn add_resolver(&self, resolver_id: usize) {
        self.resolvers.borrow_mut().push(resolver_id);
    }
}

impl Flaw for FlawData {
    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn id(&self) -> usize {
        self.id
    }

    fn phi(&self) -> VarId {
        self.phi
    }

    fn causes(&self) -> Vec<usize> {
        self.causes.clone()
    }

    fn resolvers(&self) -> Vec<usize> {
        self.resolvers.borrow().clone()
    }

    fn cost(&self) -> Rational {
        *self.cost.borrow()
    }

    fn set_cost(&self, cost: Rational) {
        *self.cost.borrow_mut() = cost;
    }

    fn compute_resolvers(self: Rc<Self>, mut _start_id: usize) -> Vec<Rc<dyn Resolver>> {
        vec![]
    }
}

impl ToJson for FlawData {
    fn to_json(&self) -> Value {
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
    fn intrinsic_cost(&self) -> Rational {
        Rational::from(1)
    }
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
}

impl Resolver for ResolverData {
    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn id(&self) -> usize {
        self.id
    }

    fn flaw(&self) -> usize {
        self.flaw
    }

    fn rho(&self) -> VarId {
        self.rho
    }

    fn apply(&self) -> Result<(), SolverError> {
        Ok(())
    }

    fn requirements(&self) -> Vec<usize> {
        self.requirements.clone()
    }

    fn intrinsic_cost(&self) -> Rational {
        self.intrinsic_cost
    }
}

impl ToJson for ResolverData {
    fn to_json(&self) -> Value {
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
}

impl EnumFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: usize, phi: VarId, cause: Option<usize>, var: Rc<EnumVar>) -> Rc<Self> {
        Rc::new(Self { flw: FlawData::new(slv, id, phi, cause.into_iter().collect()), var })
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
        let mut result: Vec<Rc<dyn Resolver>> = Vec::new();
        for val in vals {
            let rho = {
                let mut sat = solver.sat.borrow_mut();
                let rho = sat.add_var();
                sat.add_clause(vec![neg(rho), pos(self.phi())]).expect("Failed to add clause for Enum flaw resolver");
                rho
            };

            let resolver = EnumResolver::new(self.flw.slv.clone(), start_id, self.id(), rho, self.var.clone(), val);
            start_id += 1;
            self.flw.add_resolver(resolver.id());
            result.push(resolver);
        }
        print!("SAT solver {:}", solver.sat.borrow());
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
    fn new(slv: Weak<SolverState>, id: usize, flaw: usize, rho: VarId, var: Rc<EnumVar>, val: i32) -> Rc<Self> {
        Rc::new(Self {
            res: ResolverData::new(slv, id, flaw, rho, Vec::new(), Rational::from(1)),
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
        let c_id = self.solver().ac.borrow_mut().new_constraint(ac3rm::Constraint::Set(self.var.var, self.val));
        self.ac_constraints.borrow_mut().push(c_id);
        Ok(())
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
