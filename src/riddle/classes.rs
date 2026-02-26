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

pub struct Bool {
    solver: Weak<Solver>,
}

impl Bool {
    pub fn new(solver: Weak<Solver>) -> Self {
        Self { solver }
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
        let solver = self.solver.upgrade().expect("Solver has been dropped");
        solver.new_bool()
    }
}

pub struct Field {
    component_type: Weak<dyn Class>,
    name: String,
    expr: Option<Expr>,
}
