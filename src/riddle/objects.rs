use consensus::Lit;
use linspire::lin::Lin;

use crate::riddle::classes::{Bool, Class, Int};
use std::rc::{Rc, Weak};

pub trait Object {
    fn class(&self) -> Rc<dyn Class>;
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
}

pub struct ArithObject {
    class: Weak<Int>,
    pub(crate) lin: Lin,
}

impl ArithObject {
    pub fn new(class: Weak<Int>, lin: Lin) -> Self {
        Self { class, lin }
    }
}

impl Object for ArithObject {
    fn class(&self) -> Rc<dyn Class> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }
}
