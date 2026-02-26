use std::rc::Weak;

use crate::riddle::parser::Expr;

pub trait Class {
    fn name(&self) -> &str;
}

pub struct Field {
    component_type: Weak<dyn Class>,
    name: String,
    expr: Option<Expr>,
}
