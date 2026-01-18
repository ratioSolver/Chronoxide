use crate::riddle::{
    core::Core,
    env::{Component, Item},
    scope::{Field, Scope},
};
use std::{
    collections::HashMap,
    rc::{Rc, Weak},
};

pub trait Kind {
    fn name(&self) -> &str;

    fn new_instance(&mut self) -> Rc<dyn Item>;
}

pub struct BoolKind {
    core: Weak<dyn Core>,
}

impl BoolKind {
    pub fn new(core: Weak<dyn Core>) -> Rc<Self> {
        Rc::new(BoolKind { core })
    }
}

impl Kind for BoolKind {
    fn name(&self) -> &str {
        "bool"
    }

    fn new_instance(&mut self) -> Rc<dyn Item> {
        self.core
            .upgrade()
            .expect("Core has been dropped")
            .new_bool()
    }
}

pub struct ComponentKind {
    weak_self: Weak<Self>,
    core: Weak<dyn Core>,
    parent: Weak<dyn Scope>,
    name: String,
    fields: HashMap<String, Rc<Field>>,
    kinds: HashMap<String, Rc<dyn Kind>>,
    instances: Vec<Rc<dyn Item>>,
}

impl ComponentKind {
    pub fn new(core: Weak<dyn Core>, parent: Weak<dyn Scope>, name: String) -> Rc<Self> {
        Rc::new_cyclic(|weak_self| ComponentKind {
            weak_self: weak_self.clone(),
            core,
            parent,
            name,
            fields: HashMap::new(),
            kinds: HashMap::new(),
            instances: Vec::new(),
        })
    }
}

impl Kind for ComponentKind {
    fn name(&self) -> &str {
        &self.name
    }

    fn new_instance(&mut self) -> Rc<dyn Item> {
        let instance = Rc::new(Component::new(
            self.core.clone(),
            self.weak_self.clone(),
            std::collections::HashMap::new(),
        ));
        self.instances.push(instance.clone());
        instance
    }
}

impl Scope for ComponentKind {
    fn field(&self, key: &str) -> Result<Rc<Field>, String> {
        if let Some(field) = self.fields.get(key) {
            return Ok(field.clone());
        }
        if let Some(parent) = self.parent.upgrade() {
            return parent.field(key);
        }
        Err(format!(
            "Field '{}' not found in component '{}'",
            key, self.name
        ))
    }

    fn kind(&self, key: &str) -> Result<Rc<dyn Kind>, String> {
        if let Some(kind) = self.kinds.get(key) {
            return Ok(kind.clone());
        }
        if let Some(parent) = self.parent.upgrade() {
            return parent.kind(key);
        }
        Err(format!(
            "Kind '{}' not found in component '{}'",
            key, self.name
        ))
    }
}
