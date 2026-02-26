use crate::riddle::classes::{Bool, Class, Int, Real};
use consensus::Lit;
use linspire::lin::Lin;
use std::{
    any::Any,
    rc::{Rc, Weak},
};

pub trait Object {
    fn class(&self) -> Rc<dyn Class>;
    fn as_any(self: Rc<Self>) -> Rc<dyn Any>;
}

pub struct BoolObject {
    class: Weak<Bool>,
    pub(crate) lit: Lit,
}

impl BoolObject {
    pub fn new(class: Weak<Bool>, lit: Lit) -> Self {
        Self { class, lit }
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
    pub fn new(class: Weak<Int>, lin: Lin) -> Self {
        Self { class, lin }
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
    pub fn new(class: Weak<Real>, lin: Lin) -> Self {
        Self { class, lin }
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
