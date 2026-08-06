use std::collections::{HashMap, HashSet};

pub(super) struct EnumTheory {
    pub(super) var_eq_const_proxies: HashMap<(usize, i32), usize>,
    pub(super) domains: Vec<HashSet<i32>>,
}

impl EnumTheory {
    pub(super) fn new() -> Self {
        Self { var_eq_const_proxies: HashMap::new(), domains: Vec::new() }
    }

    pub(super) fn mk_var(&mut self, domain: HashSet<i32>) -> usize {
        let var = self.domains.len();
        self.domains.push(domain);
        var
    }
}
