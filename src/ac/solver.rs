use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    hash::{Hash, Hasher},
    rc::Rc,
};

pub trait Listener {
    fn on_update(&mut self, var: usize);
}

pub trait Value {}

#[derive(Clone)]
pub struct ValuePtr(pub Rc<dyn Value>);

impl PartialEq for ValuePtr {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for ValuePtr {}

impl Hash for ValuePtr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.0 as *const dyn Value).hash(state);
    }
}

struct Var {
    init_domain: HashSet<ValuePtr>,
    domain: HashSet<ValuePtr>,
}

impl Var {
    pub fn new(domain: HashSet<ValuePtr>) -> Self {
        Self {
            init_domain: domain.clone(),
            domain,
        }
    }
}

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

    pub fn add_var(&mut self, domain: HashSet<ValuePtr>) -> usize {
        let var_id = self.vars.len();
        self.vars.push(Var::new(domain));
        var_id
    }

    pub fn add_listener(&mut self, var: usize, listener: Rc<RefCell<dyn Listener>>) {
        self.listeners
            .entry(var)
            .or_insert_with(Vec::new)
            .push(listener);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestValue(i64);

    impl Value for TestValue {}

    #[test]
    fn test_add_var() {
        let mut solver = Solver::new();
        let mut domain = HashSet::new();
        domain.insert(ValuePtr(Rc::new(TestValue(1))));
        domain.insert(ValuePtr(Rc::new(TestValue(2))));
        let var_id = solver.add_var(domain);
        assert_eq!(var_id, 0);
        assert_eq!(solver.vars.len(), 1);
    }
}
