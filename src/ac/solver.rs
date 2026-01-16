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
struct ValuePtr(Rc<dyn Value>);

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

    pub(super) fn domain(&self) -> Vec<Rc<dyn Value>> {
        self.domain.iter().map(|v| v.0.clone()).collect()
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

    pub fn add_var(&mut self, domain: Vec<Rc<dyn Value>>) -> usize {
        let var_id = self.vars.len();
        self.vars
            .push(Var::new(domain.into_iter().map(|v| ValuePtr(v)).collect()));
        var_id
    }

    pub fn domain(&self, var: usize) -> Vec<Rc<dyn Value>> {
        self.vars[var].domain()
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
        let v0 = Rc::new(TestValue(0));
        let v1 = Rc::new(TestValue(1));
        let domain: Vec<Rc<dyn Value>> = vec![v0, v1.clone(), v1];
        let var_id = solver.add_var(domain);
        assert_eq!(var_id, 0);
        assert_eq!(solver.vars.len(), 1);
        assert_eq!(solver.domain(var_id).len(), 2);
    }
}
