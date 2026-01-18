use std::{
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::{
    ac, lin,
    riddle::{
        core::Core,
        env::BoolItem,
        kind::Kind,
        scope::{Field, Scope},
    },
};

pub struct Solver {
    weak_self: Weak<Self>,
    ac: ac::solver::Solver,
    lin: lin::solver::Solver,
    fields: HashMap<String, Rc<Field>>,
    kinds: HashMap<String, Rc<dyn Kind>>,
}

impl Solver {
    pub fn new() -> Rc<Self> {
        Rc::new_cyclic(|weak_self| Solver {
            weak_self: weak_self.clone(),
            ac: ac::solver::Solver::new(),
            lin: lin::solver::Solver::new(),
            fields: HashMap::new(),
            kinds: HashMap::new(),
        })
    }
}

impl Core for Solver {
    fn new_bool(&self) -> Rc<BoolItem> {
        BoolItem::new(self.weak_self.clone())
    }
}

impl Scope for Solver {
    fn field(&self, key: &str) -> Result<Rc<Field>, String> {
        self.fields
            .get(key)
            .cloned()
            .ok_or_else(|| format!("Field '{}' not found", key))
    }

    fn kind(&self, key: &str) -> Result<Rc<dyn Kind>, String> {
        self.kinds
            .get(key)
            .cloned()
            .ok_or_else(|| format!("Kind '{}' not found", key))
    }
}
