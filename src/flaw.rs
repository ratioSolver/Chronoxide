use consensus::{Lit, pos};

use crate::Solver;
use std::rc::{Rc, Weak};

pub trait Flaw {
    fn slv(&self) -> Rc<Solver>;
    fn phi(&self) -> usize;
    fn resolvers(&self) -> &Vec<Rc<dyn Resolver>>;
    fn compute_resolvers(&mut self);
}

pub trait Resolver {
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

pub struct OrFlaw {
    slv: Weak<Solver>,
    flw: Weak<OrFlaw>,
    phi: usize,
    resolvers: Vec<Rc<dyn Resolver>>,
    lits: Vec<Lit>,
}

impl OrFlaw {
    pub fn new(slv: Rc<Solver>, phi: usize, lits: Vec<Lit>) -> Rc<Self> {
        Rc::new_cyclic(|flw| Self { slv: Rc::downgrade(&slv), flw: flw.clone(), phi, resolvers: vec![], lits })
    }
}

impl Flaw for OrFlaw {
    fn slv(&self) -> Rc<Solver> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn phi(&self) -> usize {
        self.phi
    }

    fn resolvers(&self) -> &Vec<Rc<dyn Resolver>> {
        &self.resolvers
    }

    fn compute_resolvers(&mut self) {
        for lit in &self.lits {
            let rho = self.slv().sat.borrow_mut().add_var();
            let c = self.slv().sat.borrow_mut().add_clause(vec![!lit, pos(rho)]);
            assert!(c, "Failed to add clause for OR flaw resolver");
            self.resolvers.push(OrResolver::new(Rc::clone(&self.flw.upgrade().expect("Flaw has been dropped")), rho, *lit));
        }
    }
}

pub struct OrResolver {
    flaw: Weak<OrFlaw>,
    rho: usize,
    lit: Lit,
}

impl OrResolver {
    fn new(flaw: Rc<OrFlaw>, rho: usize, lit: Lit) -> Rc<Self> {
        Rc::new(Self { flaw: Rc::downgrade(&flaw), rho, lit })
    }
}

impl Resolver for OrResolver {
    fn flaw(&self) -> Rc<dyn Flaw> {
        self.flaw.upgrade().expect("Flaw has been dropped") as Rc<dyn Flaw>
    }

    fn rho(&self) -> usize {
        self.rho
    }
}
