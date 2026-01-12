use crate::riddle::r#type::Type;
use std::{collections::HashMap, rc::Rc, rc::Weak};

pub trait Item {
    fn get_type(&self) -> Rc<dyn Type>;

    fn as_env(&self) -> Option<&dyn Env> {
        None
    }
}

pub trait Env {
    fn get(&self, key: &str) -> Option<&dyn Item>;
}

pub struct Component {
    component_type: Weak<dyn Type>,
    items: HashMap<String, Rc<dyn Item>>,
}

impl Component {
    pub fn new(component_type: Weak<dyn Type>, items: HashMap<String, Rc<dyn Item>>) -> Self {
        Self {
            component_type,
            items,
        }
    }
}

impl Item for Component {
    fn get_type(&self) -> Rc<dyn Type> {
        self.component_type
            .upgrade()
            .expect("Type has been dropped")
    }

    fn as_env(&self) -> Option<&dyn Env> {
        Some(self)
    }
}

impl Env for Component {
    fn get(&self, key: &str) -> Option<&dyn Item> {
        self.items.get(key).map(|item| item.as_ref())
    }
}
