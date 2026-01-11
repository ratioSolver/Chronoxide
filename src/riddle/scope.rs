use std::collections::HashMap;

pub struct Field {}

pub struct Scope {
    fields: HashMap<String, Field>,
}

impl Scope {
    pub fn new() -> Self {
        Scope {
            fields: HashMap::new(),
        }
    }

    pub fn get_field(&self, key: &str) -> Option<&Field> {
        self.fields.get(key)
    }
}
