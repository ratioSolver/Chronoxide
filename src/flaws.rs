use crate::{
    ToJson,
    objects::EnumVar,
    solver::{SolverError, SolverState},
};
use consensus::{LBool, Lit, neg, pos};
use linspire::rational::Rational;
use riddle::serde_json::{Value, json};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

pub trait Flaw: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn id(&self) -> usize {
        let ptr: *const Self = self;
        ptr as *const () as usize
    }
    fn phi(&self) -> usize;
    fn resolvers(&self) -> Vec<Rc<dyn Resolver>>;
    fn cost(&self) -> Rational;
    fn set_cost(&self, cost: Rational);
    fn compute_resolvers(self: Rc<Self>);
}

pub trait Resolver: ToJson {
    fn id(&self) -> usize {
        let ptr: *const Self = self;
        ptr as *const () as usize
    }
    fn flaw(&self) -> Rc<dyn Flaw>;
    fn rho(&self) -> usize;
    fn apply(&self) -> Result<(), SolverError>;
    fn requirements(&self) -> Vec<Rc<dyn Flaw>> {
        Vec::new()
    }
    fn intrinsic_cost(&self) -> Rational {
        Rational::from(1)
    }
    fn cost(&self) -> Rational {
        self.requirements().iter().map(|r| r.cost()).fold(self.intrinsic_cost(), |max_cost, c| if c > max_cost { c } else { max_cost })
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
    phi: usize,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    cost: RefCell<Rational>,
    lits: Vec<Lit>,
}

impl ClauseFlaw {
    pub(crate) fn new(slv: Rc<SolverState>, phi: usize, lits: Vec<Lit>) -> Rc<Self> {
        Rc::new(Self {
            slv: Rc::downgrade(&slv),
            phi,
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

    fn phi(&self) -> usize {
        self.phi
    }

    fn resolvers(&self) -> Vec<Rc<dyn Resolver>> {
        self.resolvers.borrow().clone()
    }

    fn cost(&self) -> Rational {
        self.cost.borrow().clone()
    }

    fn set_cost(&self, cost: Rational) {
        *self.cost.borrow_mut() = cost;
    }

    fn compute_resolvers(self: Rc<Self>) {
        for lit in &self.lits {
            let c = self.solver().sat.borrow_mut().add_clause(vec![!lit, pos(self.phi)]);
            assert!(c, "Failed to add clause for OR flaw resolver");
            self.resolvers.borrow_mut().push(ClauseResolver::new(self.clone(), *lit));
        }
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
    flaw: Weak<ClauseFlaw>,
    lit: Lit,
}

impl ClauseResolver {
    fn new(flaw: Rc<ClauseFlaw>, lit: Lit) -> Rc<Self> {
        Rc::new(Self { flaw: Rc::downgrade(&flaw), lit })
    }
}

impl Resolver for ClauseResolver {
    fn flaw(&self) -> Rc<dyn Flaw> {
        self.flaw.upgrade().expect("Flaw has been dropped") as Rc<dyn Flaw>
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
    phi: usize,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    cost: RefCell<Rational>,
    var: Rc<EnumVar>,
}

impl EnumFlaw {
    pub(crate) fn new(slv: Rc<SolverState>, phi: usize, var: Rc<EnumVar>) -> Rc<Self> {
        Rc::new(Self {
            slv: Rc::downgrade(&slv),
            phi,
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

    fn phi(&self) -> usize {
        self.phi
    }

    fn resolvers(&self) -> Vec<Rc<dyn Resolver>> {
        self.resolvers.borrow().clone()
    }

    fn cost(&self) -> Rational {
        self.cost.borrow().clone()
    }

    fn set_cost(&self, cost: Rational) {
        *self.cost.borrow_mut() = cost;
    }

    fn compute_resolvers(self: Rc<Self>) {
        let vals = self.solver().ac.borrow().val(self.var.var);
        for val in vals {
            let rho = self.solver().sat.borrow_mut().add_var();
            let c = self.solver().sat.borrow_mut().add_clause(vec![neg(rho), pos(self.phi)]);
            assert!(c, "Failed to add clause for Enum flaw resolver");
            self.resolvers.borrow_mut().push(EnumResolver::new(self.clone(), rho, val));
        }
    }
}

impl ToJson for EnumFlaw {
    fn to_json(&self) -> Value {
        let mut json = flaw_to_json(self);
        json["kind"] = "enum".into();
        json["var"] = format!("{:?}", self.var).into();
        json
    }
}

pub(crate) struct EnumResolver {
    flaw: Weak<EnumFlaw>,
    rho: usize,
    val: i32,
}

impl EnumResolver {
    fn new(flaw: Rc<EnumFlaw>, rho: usize, val: i32) -> Rc<Self> {
        Rc::new(Self { flaw: Rc::downgrade(&flaw), rho, val })
    }
}

impl Resolver for EnumResolver {
    fn flaw(&self) -> Rc<dyn Flaw> {
        self.flaw.upgrade().expect("Flaw has been dropped") as Rc<dyn Flaw>
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

impl ToJson for LBool {
    fn to_json(&self) -> Value {
        match self {
            LBool::True => "active".into(),
            LBool::False => "forbidden".into(),
            LBool::Undef => "inactive".into(),
        }
    }
}

fn flaw_to_json(flaw: &dyn Flaw) -> Value {
    json!({
        "id": flaw.id(),
        "phi": flaw.phi(),
        "status": flaw.solver().sat.borrow().value(flaw.phi()).to_json(),
        "cost": flaw.cost().to_json(),
    })
}

fn resolver_to_json(resolver: &dyn Resolver) -> Value {
    json!({
        "id": resolver.id(),
        "flaw": resolver.flaw().id(),
        "status": resolver.flaw().solver().sat.borrow().value(resolver.rho()).to_json(),
        "rho": resolver.rho(),
    })
}
