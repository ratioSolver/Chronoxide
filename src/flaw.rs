use crate::Solver;
use std::rc::{Rc, Weak};

pub trait Flaw {
    fn slv(&self) -> Rc<Solver>;
    fn phi(&self) -> usize;
    fn resolvers(&self) -> &Vec<Rc<dyn Resolver>>;
}

pub trait Resolver {
    fn flaw(&self) -> Rc<dyn Flaw>;
    fn rho(&self) -> usize;
    fn lin_constraints(&self) -> usize;
}

pub struct CommonFlaw {
    slv: Weak<Solver>,
    phi: usize,
    resolvers: Vec<Rc<dyn Resolver>>,
}

impl CommonFlaw {
    pub fn new(slv: Rc<Solver>, phi: usize) -> Rc<Self> {
        Rc::new(Self { slv: Rc::downgrade(&slv), phi, resolvers: vec![] })
    }
}

impl Flaw for CommonFlaw {
    fn slv(&self) -> Rc<Solver> {
        self.slv.upgrade().expect("Solver has been dropped")
    }

    fn phi(&self) -> usize {
        self.phi
    }

    fn resolvers(&self) -> &Vec<Rc<dyn Resolver>> {
        &self.resolvers
    }
}

pub struct CommonResolver {
    flaw: Weak<CommonFlaw>,
    rho: usize,
    lin_constraints: usize,
}

impl CommonResolver {
    pub fn new(flaw: Rc<CommonFlaw>, rho: usize, lin_constraints: usize) -> Rc<Self> {
        Rc::new(Self { flaw: Rc::downgrade(&flaw), rho, lin_constraints })
    }
}

impl Resolver for CommonResolver {
    fn flaw(&self) -> Rc<dyn Flaw> {
        self.flaw.upgrade().expect("Flaw has been dropped") as Rc<dyn Flaw>
    }

    fn rho(&self) -> usize {
        self.rho
    }

    fn lin_constraints(&self) -> usize {
        self.lin_constraints
    }
}
