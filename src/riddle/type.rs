use crate::riddle::env::Component;
use std::rc::Rc;

pub trait Type {
    fn get_name(&self) -> &str;
}

pub struct ComponentType {
    name: String,
    instances: Vec<Rc<Component>>,
}

impl Type for ComponentType {
    fn get_name(&self) -> &str {
        &self.name
    }
}
