use crate::riddle::classes::{Bool, Class};
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
