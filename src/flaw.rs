use crate::{Solver, objects::EnumVar};
use consensus::{Lit, neg, pos};
use riddle::serde_json::{Value, json};
use std::{
    cell::RefCell,
    fmt::Debug,
    rc::{Rc, Weak},
};

pub trait Flaw: Debug {
    fn solver(&self) -> Rc<Solver>;
    fn phi(&self) -> usize;
    fn to_json(&self) -> Value {
        json!({
            "phi": self.phi()
        })
    }
    fn resolvers(&self) -> Vec<Rc<dyn Resolver>>;
    fn compute_resolvers(self: Rc<Self>);
}

pub trait Resolver: Debug {
    fn flaw(&self) -> Rc<dyn Flaw>;
    fn rho(&self) -> usize;
    fn to_json(&self) -> Value {
        json!({
            "flaw": Rc::as_ptr(&self.flaw()) as *const () as usize,
            "rho": self.rho()
        })
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

#[derive(Debug)]
pub(crate) struct OrFlaw {
    slv: Weak<Solver>,
    phi: usize,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    lits: Vec<Lit>,
}

impl OrFlaw {
    pub(crate) fn new(slv: Rc<Solver>, phi: usize, lits: Vec<Lit>) -> Rc<Self> {
        Rc::new(Self { slv: Rc::downgrade(&slv), phi, resolvers: RefCell::new(Vec::new()), lits })
    }
}

impl Flaw for OrFlaw {
    fn solver(&self) -> Rc<Solver> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn phi(&self) -> usize {
        self.phi
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "or",
            "phi": self.phi,
            "lits": self.lits.iter().map(|lit| lit.to_string()).collect::<Vec<_>>()
        })
    }

    fn resolvers(&self) -> Vec<Rc<dyn Resolver>> {
        self.resolvers.borrow().clone()
    }

    fn compute_resolvers(self: Rc<Self>) {
        for lit in &self.lits {
            let c = self.solver().sat.borrow_mut().add_clause(vec![!lit, pos(self.phi)]);
            assert!(c, "Failed to add clause for OR flaw resolver");
            self.resolvers.borrow_mut().push(OrResolver::new(self.clone(), *lit));
        }
    }
}

#[derive(Debug)]
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

#[derive(Debug)]
pub(crate) struct EnumFlaw {
    slv: Weak<Solver>,
    phi: usize,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    var: Rc<EnumVar>,
}

impl EnumFlaw {
    pub(crate) fn new(slv: Rc<Solver>, phi: usize, var: Rc<EnumVar>) -> Rc<Self> {
        Rc::new(Self { slv: Rc::downgrade(&slv), phi, resolvers: RefCell::new(Vec::new()), var })
    }
}

impl Flaw for EnumFlaw {
    fn solver(&self) -> Rc<Solver> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn phi(&self) -> usize {
        self.phi
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "enum",
            "phi": self.phi,
            "var": format!("{:?}", self.var)
        })
    }

    fn resolvers(&self) -> Vec<Rc<dyn Resolver>> {
        self.resolvers.borrow().clone()
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

#[derive(Debug)]
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
