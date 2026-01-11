use std::collections::HashMap;

pub trait Item {
    fn as_env(&self) -> Option<&Env> {
        None
    }
}

pub struct Component {
    env: Env,
}

pub struct Env {
    items: HashMap<String, Box<dyn Item>>,
}

impl Item for Component {
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

    pub fn get(&self, key: &str) -> Option<&Box<dyn Item>> {
        self.items.get(key)
    }
}
