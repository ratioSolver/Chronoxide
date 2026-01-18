use std::rc::Rc;

use crate::riddle::{env::BoolItem, scope::Scope};

pub trait Core: Scope {
    fn new_bool(&self) -> Rc<BoolItem>;
}
