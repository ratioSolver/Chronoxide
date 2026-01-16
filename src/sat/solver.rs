use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::Lit;

pub trait Listener {
    fn on_update(&mut self, var: usize);
}

pub enum LBool {
    True,
    False,
    Undef,
}

impl LBool {
    pub fn is_true(&self) -> bool {
        matches!(self, LBool::True)
    }

    pub fn is_false(&self) -> bool {
        matches!(self, LBool::False)
    }

    pub fn is_undef(&self) -> bool {
        matches!(self, LBool::Undef)
    }
}

impl std::fmt::Display for LBool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            LBool::True => "True",
            LBool::False => "False",
            LBool::Undef => "Undef",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug)]
struct Clause {
    literals: Vec<Lit>,
}

impl Clause {
    pub fn new(lits: Vec<Lit>) -> Self {
        Clause { literals: lits }
    }

    pub fn lits(&self) -> &Vec<Lit> {
        &self.literals
    }
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let lits_str: Vec<String> = self.literals.iter().map(|lit| lit.to_string()).collect();
        write!(f, "{}", lits_str.join(" ∨ "))
    }
}

pub struct Solver {
    vars: Vec<LBool>,
    watches: Vec<Vec<usize>>,
    clauses: Vec<Clause>,
    listeners: HashMap<usize, Vec<Rc<RefCell<dyn Listener>>>>,
}

impl Solver {
    pub fn new() -> Self {
        Solver {
            vars: Vec::new(),
            watches: Vec::new(),
            clauses: Vec::new(),
            listeners: HashMap::new(),
        }
    }

    pub fn add_var(&mut self) -> usize {
        let var_id = self.vars.len();
        self.vars.push(LBool::Undef);
        self.watches.push(Vec::new());
        var_id
    }

    pub fn add_clause(&mut self, lits: Vec<Lit>) {
        let clause_id = self.clauses.len();
        let clause = Clause::new(lits);
        for lit in clause.lits() {
            self.watches[lit.var()].push(clause_id);
        }
        self.clauses.push(clause);
    }

    pub fn add_listener(&mut self, var: usize, listener: Rc<RefCell<dyn Listener>>) {
        self.listeners
            .entry(var)
            .or_insert_with(Vec::new)
            .push(listener);
    }
}
