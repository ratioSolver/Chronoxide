use crate::riddle::{
    core::Core,
    env::Component,
    scope::{Field, Scope},
};
use std::{
    collections::HashMap,
    rc::{Rc, Weak},
};

pub trait Type {
    fn get_name(&self) -> &str;

    fn new_instance(&mut self) -> Rc<Component>;
}

pub struct BoolType {
    core: Weak<Core>,
}

impl BoolType {
    pub fn new(core: &Rc<Core>) -> Rc<Self> {
        Rc::new(BoolType {
            core: Rc::downgrade(core),
        })
    }
}

impl Type for BoolType {
    fn get_name(&self) -> &str {
        "bool"
    }

    fn new_instance(&mut self) -> Rc<Component> {
        unimplemented!()
    }
}

pub trait ComplexType: Type + Scope {}

pub struct ComponentType {
    weak_self: Weak<Self>,
    name: String,
    fields: HashMap<String, Field>,
    instances: Vec<Rc<Component>>,
}

impl ComponentType {
    pub fn new(name: String) -> Rc<Self> {
        let component_type = Rc::new_cyclic(|weak_self| ComponentType {
            weak_self: weak_self.clone(),
            name,
            fields: HashMap::new(),
            instances: Vec::new(),
        });
        component_type
    }
}

impl Type for ComponentType {
    fn get_name(&self) -> &str {
        &self.name
    }

    fn new_instance(&mut self) -> Rc<Component> {
        let instance = Rc::new(Component::new(
            Rc::downgrade(
                &(self.weak_self.upgrade().expect("Type has been dropped") as Rc<dyn Type>),
            ),
            std::collections::HashMap::new(),
        ));
        self.instances.push(instance.clone());
        instance
    }
}

impl Scope for ComponentType {
    fn get_field(&self, key: &str) -> Option<&Field> {
        self.fields.get(key)
    }
}

impl ComplexType for ComponentType {}
