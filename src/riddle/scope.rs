use crate::riddle::kind::Kind;
use std::rc::{Rc, Weak};

pub struct Field {
    component_type: Weak<dyn Kind>,
    name: String,
}

impl Field {
    pub fn new(component_type: Weak<dyn Kind>, name: &str) -> Self {
        Self {
            component_type,
            name: name.to_string(),
        }
    }

    pub fn component_type(&self) -> Rc<dyn Kind> {
        self.component_type
            .upgrade()
            .expect("Component type has been dropped")
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

pub trait Scope {
    fn field(&self, key: &str) -> Result<Rc<Field>, String>;

    fn kind(&self, key: &str) -> Result<Rc<dyn Kind>, String>;
}
