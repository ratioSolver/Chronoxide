use std::{cell::RefCell, collections::HashMap, rc::Rc};

pub trait Listener {
    fn on_update(&mut self, var: usize);
}

struct Var {}

pub struct Solver {
    vars: Vec<Var>,
    listeners: HashMap<usize, Vec<Rc<RefCell<dyn Listener>>>>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            vars: Vec::new(),
            listeners: HashMap::new(),
        }
    }

    pub fn add_listener(&mut self, var: usize, listener: Rc<RefCell<dyn Listener>>) {
        self.listeners
            .entry(var)
            .or_insert_with(Vec::new)
            .push(listener);
    }
}
