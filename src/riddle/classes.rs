use crate::{
    Solver,
    riddle::{objects::Object, parser::Expr},
};
use std::{
    any::Any,
    rc::{Rc, Weak},
};

pub trait Class {
    fn name(&self) -> &str;
    fn as_any(self: Rc<Self>) -> Rc<dyn Any>;
    fn new_instance(&mut self) -> Rc<dyn Object>;
}

pub struct Field {
    component_type: Weak<dyn Class>,
    name: String,
    expr: Option<Expr>,
}

pub struct Bool {
    solver: Weak<Solver>,
}

impl Bool {
    pub fn new(solver: &Rc<Solver>) -> Self {
        Self { solver: Rc::downgrade(solver) }
    }
}

impl Class for Bool {
    fn name(&self) -> &str {
        "bool"
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }

    fn new_instance(&mut self) -> Rc<dyn Object> {
        self.solver.upgrade().expect("Solver has been dropped").new_bool()
    }
}

pub struct Int {
    solver: Weak<Solver>,
}

impl Int {
    pub fn new(solver: &Rc<Solver>) -> Self {
        Self { solver: Rc::downgrade(solver) }
    }
}

impl Class for Int {
    fn name(&self) -> &str {
        "int"
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }

    fn new_instance(&mut self) -> Rc<dyn Object> {
        self.solver.upgrade().expect("Solver has been dropped").new_int()
    }
}

pub struct Real {
    solver: Weak<Solver>,
}

impl Real {
    pub fn new(solver: &Rc<Solver>) -> Self {
        Self { solver: Rc::downgrade(solver) }
    }
}

impl Class for Real {
    fn name(&self) -> &str {
        "real"
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }

    fn new_instance(&mut self) -> Rc<dyn Object> {
        self.solver.upgrade().expect("Solver has been dropped").new_real()
    }
}
