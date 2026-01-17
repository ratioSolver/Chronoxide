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
    core: Weak<Core>,
}

impl BoolKind {
    pub fn new(core: &Rc<Core>) -> Rc<Self> {
        Rc::new(BoolKind {
            core: Rc::downgrade(core),
        })
    }
}

impl Kind for BoolKind {
    fn name(&self) -> &str {
        "bool"
    }

    fn new_instance(&mut self) -> Rc<dyn Item> {
        unimplemented!()
    }
}

pub trait ComplexType: Kind + Scope {}

pub struct ComponentKind {
    weak_self: Weak<Self>,
    name: String,
    fields: HashMap<String, Field>,
    instances: Vec<Rc<dyn Item>>,
}

impl ComponentKind {
    pub fn new(name: String) -> Rc<Self> {
        Rc::new_cyclic(|weak_self| ComponentKind {
            weak_self: weak_self.clone(),
            name,
            fields: HashMap::new(),
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
            Rc::downgrade(
                &(self.weak_self.upgrade().expect("Type has been dropped") as Rc<dyn Kind>),
            ),
            std::collections::HashMap::new(),
        ));
        self.instances.push(instance.clone());
        instance
    }
}

impl Scope for ComponentKind {
    fn field(&self, key: &str) -> Option<&Field> {
        self.fields.get(key)
    }
}

impl ComplexType for ComponentKind {}
