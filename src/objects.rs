use std::{
    any::Any,
    rc::{Rc, Weak},
};

use consensus::Lit;
use linspire::lin::Lin;
use riddle::env::{BoolType, IntType, RealType, StringType, Type, Var};

pub struct BoolVar {
    class: Weak<BoolType>,
    pub(crate) lit: Lit,
}

impl BoolVar {
    pub fn new(class: Rc<BoolType>, lit: Lit) -> Self {
        Self { class: Rc::downgrade(&class), lit }
    }
}

impl Var for BoolVar {
    fn class(&self) -> Rc<dyn Type> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct IntVar {
    class: Weak<IntType>,
    pub(crate) lin: Lin,
}

impl IntVar {
    pub fn new(class: Rc<IntType>, lin: Lin) -> Self {
        Self { class: Rc::downgrade(&class), lin }
    }
}

impl Var for IntVar {
    fn class(&self) -> Rc<dyn Type> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct RealVar {
    class: Weak<RealType>,
    pub(crate) lin: Lin,
}

impl RealVar {
    pub fn new(class: Rc<RealType>, lin: Lin) -> Self {
        Self { class: Rc::downgrade(&class), lin }
    }
}

impl Var for RealVar {
    fn class(&self) -> Rc<dyn Type> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct StringVar {
    class: Weak<StringType>,
    value: String,
}

impl StringVar {
    pub fn new(class: Rc<StringType>, value: String) -> Self {
        Self { class: Rc::downgrade(&class), value }
    }
}

impl Var for StringVar {
    fn class(&self) -> Rc<dyn Type> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}
