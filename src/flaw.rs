use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use crate::Solver;

pub struct Flaw {
    slv: Weak<Solver>,
    phi: usize,
    resolvers: RefCell<Vec<Rc<Resolver>>>,
}

impl Flaw {
    pub fn new(slv: Rc<Solver>, phi: usize) -> Rc<Self> {
        Rc::new(Self { slv: Rc::downgrade(&slv), phi, resolvers: RefCell::new(vec![]) })
    }
}

pub struct Resolver {
    flaw: Weak<Flaw>,
    rho: usize,
    lin_constraints: usize,
}

impl Resolver {
    pub fn new(flaw: Rc<Flaw>, rho: usize, lin_constraints: usize) -> Rc<Self> {
        let resolver = Rc::new(Self { flaw: Rc::downgrade(&flaw), rho, lin_constraints });
        flaw.resolvers.borrow_mut().push(Rc::clone(&resolver));
        resolver
    }
}
