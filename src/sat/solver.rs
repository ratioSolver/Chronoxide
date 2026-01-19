use crate::{Lit, utils::lit::LBool};
use std::collections::{HashMap, VecDeque};
type Callback = Box<dyn Fn(&Solver, usize)>;

struct Var {
    value: LBool,            // current value
    _reason: Option<usize>,  // clause that implied the value
    pos_clauses: Vec<usize>, // clauses where the variable appears positively
    neg_clauses: Vec<usize>, // clauses where the variable appears negatively
}

impl Var {
    pub fn new() -> Self {
        Var {
            value: LBool::Undef,
            _reason: None,
            pos_clauses: Vec::new(),
            neg_clauses: Vec::new(),
        }
    }
}

#[derive(Default)]
pub struct Solver {
    vars: Vec<Var>,
    clauses: Vec<Vec<Lit>>,
    prop_q: VecDeque<(usize, Option<usize>)>, // (var, reason clause)
    listeners: HashMap<usize, Vec<Callback>>,
}

impl Solver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_var(&mut self) -> usize {
        let var_id = self.vars.len();
        self.vars.push(Var::new());
        var_id
    }

    pub fn value(&self, var: usize) -> LBool {
        self.vars[var].value.clone()
    }

    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        let clause_id = self.clauses.len();
        for lit in lits {
            if lit.is_positive() {
                self.vars[lit.var()].pos_clauses.push(clause_id);
            } else {
                self.vars[lit.var()].neg_clauses.push(clause_id);
            }
        }
        self.clauses.push(lits.to_vec());
        true
    }

    pub fn assert(&mut self, lit: &Lit) -> bool {
        self.enqueue(lit, None);
        while let Some((var, reason)) = self.prop_q.pop_front() {
            let clauses = if self.value(var) == LBool::True {
                self.vars[var].pos_clauses.clone()
            } else {
                self.vars[var].neg_clauses.clone()
            };
            for clause_id in clauses {
                if reason != Some(clause_id) && !self.propagate(clause_id) {
                    return false;
                }
            }
        }
        true
    }

    fn propagate(&mut self, clause_id: usize) -> bool {
        let mut num_undef = 0;
        let mut last_undef = None;
        for &lit in &self.clauses[clause_id] {
            match self.value(lit.var()) {
                LBool::True => return true,
                LBool::Undef => {
                    num_undef += 1;
                    last_undef = Some(lit);
                }
                LBool::False => {}
            }
            if num_undef > 1 {
                return true;
            }
        }
        if num_undef == 1 {
            assert!(last_undef.is_some());
            return self.enqueue(&last_undef.unwrap(), Some(clause_id));
        }
        true
    }

    fn enqueue(&mut self, lit: &Lit, reason: Option<usize>) -> bool {
        match self.value(lit.var()) {
            LBool::Undef => {
                self.vars[lit.var()].value = if lit.is_positive() {
                    LBool::True
                } else {
                    LBool::False
                };
                self.prop_q.push_back((lit.var(), reason));
                self.notify(lit.var());
                true
            }
            val => {
                val == if lit.is_positive() {
                    LBool::True
                } else {
                    LBool::False
                }
            }
        }
    }

    fn notify(&self, var: usize) {
        if let Some(listeners) = self.listeners.get(&var) {
            for listener in listeners {
                listener(self, var);
            }
        }
    }

    pub fn add_listener<F>(&mut self, var: usize, listener: F)
    where
        F: Fn(&Solver, usize) + 'static,
    {
        self.listeners
            .entry(var)
            .or_default()
            .push(Box::new(listener));
    }
}
