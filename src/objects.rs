use riddle::{
    env::{ObjectId, Var},
    scope::{BoolType, IntType, RealType, StringType, Type},
};
use std::{
    any::Any,
    rc::{Rc, Weak},
};
use z3::ast::{Bool, Int, Real};

#[derive(Debug)]
pub struct BoolVar {
    var_type: Weak<BoolType>,
    pub(crate) lit: Bool,
}

impl BoolVar {
    pub(crate) fn new(var_type: Rc<BoolType>, lit: Bool) -> Self {
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
pub struct IntVar {
    var_type: Weak<IntType>,
    pub(crate) lit: Int,
}

impl IntVar {
    pub(crate) fn new(var_type: Rc<IntType>, lit: Int) -> Self {
        Self { var_type: Rc::downgrade(&var_type), lit }
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

#[derive(Debug)]
pub struct RealVar {
    var_type: Weak<RealType>,
    pub(crate) lit: Real,
}

impl RealVar {
    pub(crate) fn new(var_type: Rc<RealType>, lit: Real) -> Self {
        Self { var_type: Rc::downgrade(&var_type), lit }
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

#[derive(Debug)]
pub struct StringVar {
    var_type: Weak<StringType>,
    pub(crate) val: z3::ast::String,
}

impl StringVar {
    pub(crate) fn new(var_type: Rc<StringType>, val: z3::ast::String) -> Self {
        Self { var_type: Rc::downgrade(&var_type), val }
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
    pub(crate) var: Int,
}

impl EnumVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, var: Int) -> Self {
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
