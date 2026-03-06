use consensus::Lit;
use linspire::lin::Lin;
use riddle::{
    env::Var,
    scope::{BoolType, IntType, RealType, StringType, Type},
};
use std::{
    any::Any,
    rc::{Rc, Weak},
};

pub struct BoolVar {
    var_type: Weak<BoolType>,
    pub(crate) lit: Lit,
}

impl BoolVar {
    pub fn new(var_type: Rc<BoolType>, lit: Lit) -> Self {
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

pub struct IntVar {
    var_type: Weak<IntType>,
    pub(crate) lin: Lin,
}

impl IntVar {
    pub fn new(var_type: Rc<IntType>, lin: Lin) -> Self {
        Self { var_type: Rc::downgrade(&var_type), lin }
    }
}

impl Var for IntVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct RealVar {
    var_type: Weak<RealType>,
    pub(crate) lin: Lin,
}

impl RealVar {
    pub fn new(var_type: Rc<RealType>, lin: Lin) -> Self {
        Self { var_type: Rc::downgrade(&var_type), lin }
    }
}

impl Var for RealVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped").clone()
    }

    fn as_any(self: Rc<Self>) -> Rc<dyn Any> {
        self
    }
}

pub struct StringVar {
    var_type: Weak<StringType>,
    value: String,
}

impl StringVar {
    pub fn new(var_type: Rc<StringType>, value: String) -> Self {
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
