use crate::{
    ToJson,
    objects::EnumVar,
    solver::{SolverError, SolverState},
};
use consensus::{Lit, neg, pos};
use linspire::rational::Rational;
use riddle::serde_json::{Value, json};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

pub trait Flaw: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> usize;
    fn phi(&self) -> usize;
    fn causes(&self) -> Vec<usize>;
    fn supports(&self) -> Vec<usize> {
        Vec::new()
    }
    fn resolvers(&self) -> Vec<usize>;
    fn cost(&self) -> Rational;
    fn set_cost(&self, cost: Rational);
    fn compute_resolvers(self: Rc<Self>, start_id: usize) -> Vec<Rc<dyn Resolver>>;
}

pub trait Resolver: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> usize;
    fn flaw(&self) -> usize;
    fn rho(&self) -> usize;
    fn apply(&self) -> Result<(), SolverError>;
    fn requirements(&self) -> Vec<usize> {
        Vec::new()
    }
    fn intrinsic_cost(&self) -> Rational {
        Rational::from(1)
    }
    fn ac_constraints(&self) -> Option<Vec<usize>> {
        None
    }
    fn add_ac_constraint(&self, _constraint: usize) {
        unimplemented!()
    }
    fn lin_constraints(&self) -> Option<usize> {
        None
    }
}

pub(crate) struct ClauseFlaw {
    slv: Weak<SolverState>,
    id: usize,
    phi: usize,
    cause: Option<usize>,
    resolvers: RefCell<Vec<usize>>,
    cost: RefCell<Rational>,
    lits: Vec<Lit>,
}

impl ClauseFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: usize, phi: usize, cause: Option<usize>, lits: Vec<Lit>) -> Rc<Self> {
        Rc::new(Self {
            slv,
            id,
            phi,
            cause,
            resolvers: RefCell::new(Vec::new()),
            cost: RefCell::new(Rational::POSITIVE_INFINITY),
            lits,
        })
    }
}

impl Flaw for ClauseFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn id(&self) -> usize {
        self.id
    }

    fn phi(&self) -> usize {
        self.phi
    }

    fn causes(&self) -> Vec<usize> {
        if let Some(cause) = self.cause { vec![cause] } else { Vec::new() }
    }

    fn resolvers(&self) -> Vec<usize> {
        self.resolvers.borrow().clone()
    }

    fn cost(&self) -> Rational {
        self.cost.borrow().clone()
    }

    fn set_cost(&self, cost: Rational) {
        *self.cost.borrow_mut() = cost;
    }

    fn compute_resolvers(self: Rc<Self>, mut start_id: usize) -> Vec<Rc<dyn Resolver>> {
        let solver = self.solver();
        let mut result: Vec<Rc<dyn Resolver>> = Vec::new();
        for lit in &self.lits {
            let c = solver.sat.borrow_mut().add_clause(vec![!lit, pos(self.phi)]);
            assert!(c, "Failed to add clause for OR flaw resolver");

            let resolver = ClauseResolver::new(self.slv.clone(), start_id, self.id, *lit);
            start_id += 1;
            self.resolvers.borrow_mut().push(resolver.id());
            result.push(resolver);
        }
        result
    }
}

impl ToJson for ClauseFlaw {
    fn to_json(&self) -> Value {
        let mut json = flaw_to_json(self);
        json["kind"] = "clause".into();
        json["lits"] = self.lits.iter().map(|lit| lit.to_string()).collect::<Vec<_>>().into();
        json
    }
}

pub(crate) struct ClauseResolver {
    slv: Weak<SolverState>,
    id: usize,
    flaw: usize,
    lit: Lit,
}

impl ClauseResolver {
    fn new(slv: Weak<SolverState>, id: usize, flaw: usize, lit: Lit) -> Rc<Self> {
        Rc::new(Self { slv, id, flaw, lit })
    }
}

impl Resolver for ClauseResolver {
    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn id(&self) -> usize {
        self.id
    }

    fn flaw(&self) -> usize {
        self.flaw
    }

    fn rho(&self) -> usize {
        self.lit.var()
    }

    fn apply(&self) -> Result<(), SolverError> {
        Ok(())
    }
}

impl ToJson for ClauseResolver {
    fn to_json(&self) -> Value {
        let mut json = resolver_to_json(self);
        json["lit"] = self.lit.to_string().into();
        json
    }
}

pub(crate) struct EnumFlaw {
    slv: Weak<SolverState>,
    id: usize,
    phi: usize,
    cause: Option<usize>,
    resolvers: RefCell<Vec<usize>>,
    cost: RefCell<Rational>,
    var: Rc<EnumVar>,
}

impl EnumFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: usize, phi: usize, cause: Option<usize>, var: Rc<EnumVar>) -> Rc<Self> {
        Rc::new(Self {
            slv,
            id,
            phi,
            cause,
            resolvers: RefCell::new(Vec::new()),
            cost: RefCell::new(Rational::POSITIVE_INFINITY),
            var,
        })
    }
}

impl Flaw for EnumFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn id(&self) -> usize {
        self.id
    }

    fn phi(&self) -> usize {
        self.phi
    }

    fn causes(&self) -> Vec<usize> {
        if let Some(cause) = self.cause { vec![cause] } else { Vec::new() }
    }

    fn resolvers(&self) -> Vec<usize> {
        self.resolvers.borrow().clone()
    }

    fn cost(&self) -> Rational {
        self.cost.borrow().clone()
    }

    fn set_cost(&self, cost: Rational) {
        *self.cost.borrow_mut() = cost;
    }

    fn compute_resolvers(self: Rc<Self>, mut start_id: usize) -> Vec<Rc<dyn Resolver>> {
        let solver = self.solver();
        let vals = solver.ac.borrow().val(self.var.var);
        let mut result: Vec<Rc<dyn Resolver>> = Vec::new();
        for val in vals {
            let (rho, c) = {
                let mut sat = solver.sat.borrow_mut();
                let rho = sat.add_var();
                let c = sat.add_clause(vec![neg(rho), pos(self.phi)]);
                (rho, c)
            };
            assert!(c, "Failed to add clause for Enum flaw resolver");

            let resolver = EnumResolver::new(self.slv.clone(), start_id, self.id, rho, val);
            start_id += 1;
            self.resolvers.borrow_mut().push(resolver.id());
            result.push(resolver);
        }
        print!("SAT solver {:}", solver.sat.borrow());
        result
    }
}

impl ToJson for EnumFlaw {
    fn to_json(&self) -> Value {
        let mut json = flaw_to_json(self);
        json["kind"] = "enum".into();
        json["var"] = format!("{:?}", self.var.var).into();
        json
    }
}

pub(crate) struct EnumResolver {
    slv: Weak<SolverState>,
    id: usize,
    flaw: usize,
    rho: usize,
    val: i32,
}

impl EnumResolver {
    fn new(slv: Weak<SolverState>, id: usize, flaw: usize, rho: usize, val: i32) -> Rc<Self> {
        Rc::new(Self { slv, id, flaw, rho, val })
    }
}

impl Resolver for EnumResolver {
    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn id(&self) -> usize {
        self.id
    }

    fn flaw(&self) -> usize {
        self.flaw
    }

    fn rho(&self) -> usize {
        self.rho
    }

    fn apply(&self) -> Result<(), SolverError> {
        Ok(())
    }
}

impl ToJson for EnumResolver {
    fn to_json(&self) -> Value {
        let mut json = resolver_to_json(self);
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

fn flaw_to_json(flaw: &dyn Flaw) -> Value {
    json!({
        "id": format!("f{}", flaw.id()),
        "phi": flaw.phi(),
        "causes": flaw.causes().into_iter().map(|id| format!("r{}", id)).collect::<Vec<_>>(),
        "supports": flaw.supports().into_iter().map(|id| format!("r{}", id)).collect::<Vec<_>>(),
        "status": flaw.solver().sat.borrow().value(flaw.phi()).to_json(),
        "cost": flaw.cost().to_json(),
    })
}

fn resolver_to_json(resolver: &dyn Resolver) -> Value {
    json!({
        "id": format!("r{}", resolver.id()),
        "flaw": format!("f{}", resolver.flaw()),
        "requirements": resolver.requirements().into_iter().map(|id| format!("f{}", id)).collect::<Vec<_>>(),
        "intrinsic_cost": resolver.intrinsic_cost().to_json(),
        "status": resolver.solver().sat.borrow().value(resolver.rho()).to_json(),
        "rho": resolver.rho(),
    })
}
