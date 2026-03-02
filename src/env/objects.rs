use crate::env::{
    Env,
    classes::{Bool, CString, Class, Int, Real},
};
use consensus::Lit;
use linspire::lin::Lin;
use std::{
    any::Any,
    cell::RefCell,
    collections::HashMap,
    hash::Hash,
    rc::{Rc, Weak},
};

pub trait Object {
    fn class(&self) -> Rc<dyn Class>;
    fn as_any(self: Rc<Self>) -> Rc<dyn Any>;
    fn as_env(&self) -> Option<&dyn Env> {
        None
    }
}

pub struct BoolObject {
    class: Weak<Bool>,
    pub(crate) lit: Lit,
}

impl BoolObject {
    pub fn new(class: &Rc<Bool>, lit: Lit) -> Self {
        Self { class: Rc::downgrade(class), lit }
    }
}

impl Object for BoolObject {
    fn class(&self) -> Rc<dyn Class> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct IntObject {
    class: Weak<Int>,
    pub(crate) lin: Lin,
}

impl IntObject {
    pub fn new(class: &Rc<Int>, lin: Lin) -> Self {
        Self { class: Rc::downgrade(class), lin }
    }
}

impl Object for IntObject {
    fn class(&self) -> Rc<dyn Class> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct RealObject {
    class: Weak<Real>,
    pub(crate) lin: Lin,
}

impl RealObject {
    pub fn new(class: &Rc<Real>, lin: Lin) -> Self {
        Self { class: Rc::downgrade(class), lin }
    }
}

impl Object for RealObject {
    fn class(&self) -> Rc<dyn Class> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct StringObject {
    class: Weak<CString>,
    pub(crate) value: String,
}

impl StringObject {
    pub fn new(class: &Rc<CString>, value: String) -> Self {
        Self { class: Rc::downgrade(class), value }
    }
}

impl Object for StringObject {
    fn class(&self) -> Rc<dyn Class> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct CompositeObject {
    class: Weak<dyn Class>,
    fields: RefCell<HashMap<String, Rc<dyn Object>>>,
}

impl CompositeObject {
    pub fn new(class: Rc<dyn Class>) -> Self {
        Self { class: Rc::downgrade(&class), fields: RefCell::new(HashMap::new()) }
    }
}

impl Object for CompositeObject {
    fn class(&self) -> Rc<dyn Class> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

impl Env for CompositeObject {
    fn parent(&self) -> Option<Rc<dyn Env>> {
        None
    }

    fn get(&self, name: &str) -> Option<Rc<dyn Object>> {
        self.fields.borrow().get(name).cloned()
    }
}
