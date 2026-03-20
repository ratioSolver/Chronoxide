use consensus::Lit;
use linspire::lin::Lin;
use riddle::{
    env::Var,
    scope::{BoolType, StringType, Type},
};
use std::{
    any::Any,
    rc::{Rc, Weak},
};

#[derive(Debug)]
pub struct BoolVar {
    var_type: Weak<BoolType>,
    pub(crate) lit: Lit,
}

impl BoolVar {
    pub(crate) fn new(var_type: Rc<BoolType>, lit: Lit) -> Self {
        Self { var_type: Rc::downgrade(&var_type), lit }
    }
}

impl Var for BoolVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

#[derive(Debug)]
pub struct ArithVar {
    var_type: Weak<dyn Type>,
    pub(crate) lin: Lin,
}

impl ArithVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, lin: Lin) -> Self {
        Self { var_type: Rc::downgrade(&var_type), lin }
    }
}

impl Var for ArithVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

#[derive(Debug)]
pub struct StringVar {
    var_type: Weak<StringType>,
    pub(crate) value: String,
}

impl StringVar {
    pub(crate) fn new(var_type: Rc<StringType>, value: String) -> Self {
        Self { var_type: Rc::downgrade(&var_type), value }
    }
}

impl Var for StringVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

#[derive(Debug)]
pub struct EnumVar {
    var_type: Weak<dyn Type>,
    pub(crate) var: usize,
}

impl EnumVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, var: usize) -> Self {
        Self { var_type: Rc::downgrade(&var_type), var }
    }
}

impl Var for EnumVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}
