use crate::riddle::r#type::Type;
use std::{collections::HashMap, rc::Weak};

pub trait Item {
    fn get_type(&self) -> std::rc::Rc<Type>;

    fn as_env(&self) -> Option<&Env> {
        None
    }
}

pub struct Component {
    component_type: Weak<Type>,
    env: Env,
}

pub struct Env {
    items: HashMap<String, Box<dyn Item>>,
}

impl Item for Component {
    fn get_type(&self) -> std::rc::Rc<Type> {
        self.component_type
            .upgrade()
            .expect("Type has been dropped")
    }

    fn as_env(&self) -> Option<&Env> {
        Some(&self.env)
    }
}

impl Env {
    pub fn new() -> Self {
        Env {
            items: HashMap::new(),
        }
    }

    pub fn get(&self, key: &str) -> Option<&dyn Item> {
        self.items.get(key).map(|item| item.as_ref())
    }
}
