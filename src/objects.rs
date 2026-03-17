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

pub struct ArithVar {
    var_type: Weak<dyn Type>,
    pub(crate) lin: Lin,
}

impl ArithVar {
    pub fn new(var_type: Rc<dyn Type>, lin: Lin) -> Self {
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

pub struct RealVar {
    var_type: Weak<dyn Type>,
    pub(crate) lin: Lin,
}

impl RealVar {
    pub fn new(var_type: Rc<dyn Type>, lin: Lin) -> Self {
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
    pub(crate) value: String,
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
