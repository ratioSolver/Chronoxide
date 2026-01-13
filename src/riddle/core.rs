use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::riddle::{
    scope::{Field, Scope},
    class::{BoolKind, Kind},
};

pub struct Core {
    weak_self: Weak<Self>,
    fields: HashMap<String, Field>,
    types: RefCell<HashMap<String, Rc<dyn Kind>>>,
}

impl Scope for Core {
    fn field(&self, key: &str) -> Option<&Field> {
        self.fields.get(key)
    }
}

impl Core {
    pub fn new() -> std::rc::Rc<Self> {
        let core = std::rc::Rc::new_cyclic(|weak_self| Core {
            weak_self: weak_self.clone(),
            fields: HashMap::new(),
            types: RefCell::new(HashMap::new()),
        });
        let bool_type = BoolKind::new(&core);
        core.types
            .borrow_mut()
            .insert(bool_type.name().to_string(), bool_type);
        core
    }
}
