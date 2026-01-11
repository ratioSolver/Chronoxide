use std::collections::HashMap;

pub struct Item {}

pub struct Env {
    items: HashMap<String, Item>,
}

impl Env {
    pub fn new() -> Self {
        Env {
            items: HashMap::new(),
        }
    }

    pub fn get(&self, key: &str) -> Option<&Item> {
        self.items.get(key)
    }
}