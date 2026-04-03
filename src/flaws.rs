use crate::{ToJson, objects::EnumVar, solver::SolverState};
use consensus::{Lit, neg, pos};
use linspire::rational::Rational;
use riddle::serde_json::{Value, json};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

pub trait RationalJsonExt {
    fn to_json(&self) -> Value;
}

impl RationalJsonExt for Rational {
    fn to_json(&self) -> Value {
        json!({
            "num": self.num,
            "den": self.den
        })
    }
}

pub trait Flaw: ToJson {
    fn solver(&self) -> Rc<SolverState>;
    fn phi(&self) -> usize;
    fn resolvers(&self) -> Vec<Rc<dyn Resolver>>;
    fn cost(&self) -> &Rational;
    fn compute_resolvers(self: Rc<Self>);
}

pub trait Resolver: ToJson {
    fn flaw(&self) -> Rc<dyn Flaw>;
    fn rho(&self) -> usize;
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

pub(crate) struct OrFlaw {
    slv: Weak<SolverState>,
    phi: usize,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    cost: Rational,
    lits: Vec<Lit>,
}

impl OrFlaw {
    pub(crate) fn new(slv: Rc<SolverState>, phi: usize, lits: Vec<Lit>) -> Rc<Self> {
        Rc::new(Self {
            slv: Rc::downgrade(&slv),
            phi,
            resolvers: RefCell::new(Vec::new()),
            cost: Rational::POSITIVE_INFINITY,
            lits,
        })
    }
}

impl Flaw for OrFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn phi(&self) -> usize {
        self.phi
    }

    fn resolvers(&self) -> Vec<Rc<dyn Resolver>> {
        self.resolvers.borrow().clone()
    }

    fn cost(&self) -> &Rational {
        &self.cost
    }

    fn compute_resolvers(self: Rc<Self>) {
        for lit in &self.lits {
            let c = self.solver().sat.borrow_mut().add_clause(vec![!lit, pos(self.phi)]);
            assert!(c, "Failed to add clause for OR flaw resolver");
            self.resolvers.borrow_mut().push(OrResolver::new(self.clone(), *lit));
        }
    }
}

impl ToJson for OrFlaw {
    fn to_json(&self) -> Value {
        json!({
            "kind": "or",
            "phi": self.phi,
            "cost": self.cost.to_json(),
            "lits": self.lits.iter().map(|lit| lit.to_string()).collect::<Vec<_>>()
        })
    }
}

pub(crate) struct OrResolver {
    flaw: Weak<OrFlaw>,
    lit: Lit,
}

impl OrResolver {
    fn new(flaw: Rc<OrFlaw>, lit: Lit) -> Rc<Self> {
        Rc::new(Self { flaw: Rc::downgrade(&flaw), lit })
    }
}

impl Resolver for OrResolver {
    fn flaw(&self) -> Rc<dyn Flaw> {
        self.flaw.upgrade().expect("Flaw has been dropped") as Rc<dyn Flaw>
    }

    fn rho(&self) -> usize {
        self.lit.var()
    }
}

impl ToJson for OrResolver {
    fn to_json(&self) -> Value {
        json!({
            "flaw": Rc::as_ptr(&self.flaw()) as *const () as usize,
            "lit": self.lit.to_string()
        })
    }
}

pub(crate) struct EnumFlaw {
    slv: Weak<SolverState>,
    phi: usize,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    cost: Rational,
    var: Rc<EnumVar>,
}

impl EnumFlaw {
    pub(crate) fn new(slv: Rc<SolverState>, phi: usize, var: Rc<EnumVar>) -> Rc<Self> {
        Rc::new(Self {
            slv: Rc::downgrade(&slv),
            phi,
            resolvers: RefCell::new(Vec::new()),
            cost: Rational::POSITIVE_INFINITY,
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

    fn cost(&self) -> &Rational {
        &self.cost
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
        json!({
            "kind": "enum",
            "phi": self.phi,
            "cost": self.cost.to_json(),
            "var": format!("{:?}", self.var)
        })
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
}

impl ToJson for EnumResolver {
    fn to_json(&self) -> Value {
        json!({
            "flaw": Rc::as_ptr(&self.flaw()) as *const () as usize,
            "rho": self.rho,
            "val": self.val
        })
    }
}
