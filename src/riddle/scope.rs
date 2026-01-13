use crate::riddle::class::Kind;
use std::rc::Weak;

pub struct Field {
    component_type: Weak<dyn Kind>,
    name: String,
}

pub trait Scope {
    fn field(&self, key: &str) -> Option<&Field>;
}
