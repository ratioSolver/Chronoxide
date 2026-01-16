use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

pub trait Listener {
    fn on_update(&mut self, var: usize);
}

struct Var {
    init_domain: HashSet<usize>,
    domain: HashSet<usize>,
}

impl Var {
    pub fn new(domain: HashSet<usize>) -> Self {
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

    pub fn add_var<I>(&mut self, domain: I) -> usize
    where
        I: IntoIterator<Item = usize>,
    {
        let var_id = self.vars.len();
        let var = Var::new(domain.into_iter().collect());
        self.vars.push(var);
        var_id
    }

    pub fn domain(&self, var: usize) -> &HashSet<usize> {
        &self.vars[var].domain
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

    #[test]
    fn test_add_var() {
        let mut solver = Solver::new();
        let var_id = solver.add_var([1, 2, 2]);
        assert_eq!(var_id, 0);
        assert_eq!(solver.vars.len(), 1);
        assert_eq!(solver.domain(var_id).len(), 2);
    }
}
