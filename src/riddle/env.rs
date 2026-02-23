use crate::riddle::{core::Core, kind::Kind};
use std::{collections::HashMap, rc::Rc, rc::Weak};

pub trait Item {
    fn kind(&self) -> Rc<dyn Kind>;

    fn as_env(&self) -> Option<&dyn Env> {
        None
    }
}

pub struct BoolItem {
    core: Weak<dyn Core>,
}

impl BoolItem {
    pub fn new(core: Weak<dyn Core>) -> Rc<Self> {
        Rc::new(BoolItem { core })
    }
}

impl Item for BoolItem {
    fn kind(&self) -> Rc<dyn Kind> {
        let core = self.core.upgrade().expect("Core has been dropped");
        core.kind("bool").expect("`bool` kind not found")
    }
}

pub trait Env {
    fn get(&self, key: &str) -> Result<&dyn Item, String>;
}

pub struct Component {
    core: Weak<dyn Core>,
    component_type: Weak<dyn Kind>,
    items: HashMap<String, Rc<dyn Item>>,
}

impl Component {
    pub fn new(core: Weak<dyn Core>, component_type: Weak<dyn Kind>, items: HashMap<String, Rc<dyn Item>>) -> Self {
        Self { core, component_type, items }
    }
}

impl Item for Component {
    fn kind(&self) -> Rc<dyn Kind> {
        self.component_type.upgrade().expect("Type has been dropped")
    }

    fn as_env(&self) -> Option<&dyn Env> {
        Some(self)
    }
}

impl Env for Component {
    fn get(&self, key: &str) -> Result<&dyn Item, String> {
        self.items.get(key).map(|item| item.as_ref()).ok_or_else(|| format!("Item '{}' not found in component", key))
    }
}
