use crate::riddle::r#type::Type;
use std::rc::Weak;

pub struct Field {
    component_type: Weak<dyn Type>,
    name: String,
}

pub trait Scope {
    fn get_field(&self, key: &str) -> Option<&Field>;
}
