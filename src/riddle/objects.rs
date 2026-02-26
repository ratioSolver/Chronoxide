use crate::riddle::classes::{Bool, Class, Int};
use std::rc::{Rc, Weak};

pub trait Object {
    fn class(&self) -> Rc<dyn Class>;
}

pub struct BoolObject {
    class: Weak<Bool>,
    pub(crate) var: usize,
}

impl BoolObject {
    pub fn new(class: Weak<Bool>, var: usize) -> Self {
        Self { class, var }
    }
}

impl Object for BoolObject {
    fn class(&self) -> Rc<dyn Class> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }
}

pub struct IntObject {
    class: Weak<Int>,
    pub(crate) var: usize,
}

impl IntObject {
    pub fn new(class: Weak<Int>, var: usize) -> Self {
        Self { class, var }
    }
}

impl Object for IntObject {
    fn class(&self) -> Rc<dyn Class> {
        self.class.upgrade().expect("Class has been dropped").clone()
    }
}
