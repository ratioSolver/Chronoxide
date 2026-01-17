use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::riddle::{
    class::{BoolKind, Kind},
    scope::{Field, Scope},
};

pub struct Core {
    weak_self: Weak<Self>,
    fields: HashMap<String, Field>,
    kinds: RefCell<HashMap<String, RefCell<Rc<dyn Kind>>>>,
}

impl Scope for Core {
    fn field(&self, key: &str) -> Option<&Field> {
        self.fields.get(key)
    }

    fn kind(&self, key: &str) -> Option<Rc<dyn Kind>> {
        self.kinds
            .borrow()
            .get(key)
            .map(|kind_cell| kind_cell.borrow().clone())
    }
}

impl Core {
    pub fn new() -> std::rc::Rc<Self> {
        let core = std::rc::Rc::new_cyclic(|weak_self| Core {
            weak_self: weak_self.clone(),
            fields: HashMap::new(),
            kinds: RefCell::new(HashMap::new()),
        });
        let bool_type = BoolKind::new(&core);
        core.add_kind(bool_type);
        core
    }

    pub fn add_kind(&self, kind: Rc<dyn Kind>) {
        self.kinds
            .borrow_mut()
            .insert(kind.name().to_string(), RefCell::new(kind));
    }
}
