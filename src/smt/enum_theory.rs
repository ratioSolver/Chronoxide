use std::collections::{HashMap, HashSet};

pub(super) struct EnumTheory {
    pub(super) var_eq_const_proxies: HashMap<(usize, i32), usize>,
    pub(super) domains: HashMap<usize, HashSet<i32>>,
}

impl EnumTheory {
    pub(super) fn new() -> Self {
        Self { var_eq_const_proxies: HashMap::new(), domains: HashMap::new() }
    }

    pub(super) fn register_domain_value(&mut self, var: usize, val: i32) {
        self.domains.entry(var).or_default().insert(val);
    }
}
