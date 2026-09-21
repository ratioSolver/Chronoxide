use riddle::{env::Var, scope::Type};
use semitone::ast::{ArithExpr, BoolExpr, EnumExpr};
use std::{
    any::Any,
    rc::{Rc, Weak},
};

pub struct BoolVar {
    var_type: Weak<dyn Type>,
    pub(crate) lit: BoolExpr,
}

impl BoolVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, lit: BoolExpr) -> Self {
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
    pub(crate) lin: ArithExpr,
}

impl ArithVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, lin: ArithExpr) -> Self {
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

pub struct StringVar {
    var_type: Weak<dyn Type>,
    pub(crate) value: String,
}

impl StringVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, value: String) -> Self {
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

pub struct EnumVar {
    var_type: Weak<dyn Type>,
    pub(crate) var: EnumExpr,
}

impl EnumVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, var: EnumExpr) -> Self {
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
