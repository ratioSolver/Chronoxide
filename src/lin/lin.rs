use std::{
    collections::{BTreeMap, HashSet},
    rc::Rc,
};

use crate::{InfRational, Lin};

pub trait Constraint {}

pub struct Var {
    val: InfRational,
    lbs: BTreeMap<InfRational, HashSet<Rc<dyn Constraint>>>,
    ubs: BTreeMap<InfRational, HashSet<Rc<dyn Constraint>>>,
    rows: HashSet<u32>,
}

impl Var {
    pub fn new() -> Self {
        Self {
            val: InfRational::from_integer(0),
            lbs: BTreeMap::new(),
            ubs: BTreeMap::new(),
            rows: HashSet::new(),
        }
    }

    pub fn get_value(&self) -> InfRational {
        self.val
    }

    pub fn get_lb(&self) -> Option<&InfRational> {
        self.lbs.keys().next_back()
    }

    pub fn get_ub(&self) -> Option<&InfRational> {
        self.ubs.keys().next()
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} [{}, {}]",
            self.val,
            match self.get_lb() {
                Some(lb) => lb.to_string(),
                None => "-∞".to_string(),
            },
            match self.get_ub() {
                Some(ub) => ub.to_string(),
                None => "∞".to_string(),
            }
        )
    }
}

pub struct Solver {
    vars: Vec<Var>,
    tableau: BTreeMap<u32, Lin>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            vars: Vec::new(),
            tableau: BTreeMap::new(),
        }
    }

    pub fn new_var(&mut self) -> usize {
        let var = Var::new();
        self.vars.push(var);
        self.vars.len() - 1
    }
}
