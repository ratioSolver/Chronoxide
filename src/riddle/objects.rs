use std::rc::Rc;

use crate::riddle::classes::Class;

pub trait Object {
    fn class(&self) -> Rc<dyn Class>;
}
