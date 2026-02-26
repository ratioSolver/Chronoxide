use crate::riddle::classes::{Class, Field};
use std::{
    collections::HashMap,
    rc::{Rc, Weak},
};

mod riddle;

pub struct Solver {
    weak_self: Weak<Self>,
    sat: consensus::Engine,
    ac: dynamic_ac::Engine,
    lin: linspire::Engine,
    fields: HashMap<String, Rc<Field>>,
    classes: HashMap<String, Rc<dyn Class>>,
}

impl Solver {
    pub fn new() -> Rc<Self> {
        Rc::new_cyclic(|weak_self| Solver {
            weak_self: weak_self.clone(),
            sat: consensus::Engine::new(),
            ac: dynamic_ac::Engine::new(),
            lin: linspire::Engine::new(),
            fields: HashMap::new(),
            classes: HashMap::new(),
        })
    }
}
