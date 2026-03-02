use riddle::language::{ClassDef, Field, MethodDef, PredicateDef};

use crate::{
    Solver,
    env::{
        Scope,
        objects::{CompositeObject, Object},
    },
};
use std::{
    any::Any,
    cell::RefCell,
    rc::{Rc, Weak},
};

pub trait Class {
    fn name(&self) -> &str;
    fn as_any(self: Rc<Self>) -> Rc<dyn Any>;
    fn new_instance(self: Rc<Self>) -> Rc<dyn Object>;
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

    fn new_instance(self: Rc<Self>) -> Rc<dyn Object> {
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

    fn new_instance(self: Rc<Self>) -> Rc<dyn Object> {
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

    fn new_instance(self: Rc<Self>) -> Rc<dyn Object> {
        self.solver.upgrade().expect("Solver has been dropped").new_real()
    }
}

pub struct CString {
    solver: Weak<Solver>,
}

impl CString {
    pub fn new(solver: &Rc<Solver>) -> Self {
        Self { solver: Rc::downgrade(solver) }
    }
}

impl Class for CString {
    fn name(&self) -> &str {
        "string"
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }

    fn new_instance(self: Rc<Self>) -> Rc<dyn Object> {
        self.solver.upgrade().expect("Solver has been dropped").new_string("")
    }
}

pub struct Composite {
    scp: Weak<dyn Scope>,
    name: String,
    instances: RefCell<Vec<Rc<dyn Object>>>,
}

impl Composite {
    pub fn new(scp: Rc<dyn Scope>, def: ClassDef) -> Self {
        Self { scp: Rc::downgrade(&scp), name: def.name, instances: RefCell::new(Vec::new()) }
    }
}

impl Class for Composite {
    fn name(&self) -> &str {
        &self.name
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }

    fn new_instance(self: Rc<Self>) -> Rc<dyn Object> {
        let instance = Rc::new(CompositeObject::new(self.clone()));
        self.instances.borrow_mut().push(instance.clone());
        instance
    }
}

impl Scope for Composite {
    fn solver(self: Rc<Self>) -> Rc<Solver> {
        self.scp.upgrade().expect("Scope has been dropped").solver()
    }

    fn parent(&self) -> Option<Rc<dyn Scope>> {
        self.scp.upgrade()
    }

    fn get_field(&self, _name: &str) -> Option<Field> {
        None
    }

    fn get_method(&self, _name: &str) -> Option<MethodDef> {
        None
    }

    fn get_class(&self, _name: &str) -> Option<Rc<dyn Class>> {
        None
    }

    fn get_predicate(&self, _name: &str) -> Option<PredicateDef> {
        None
    }
}
