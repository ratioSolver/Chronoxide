use std::collections::{HashMap, VecDeque};

use crate::Lit;

type Callback = Box<dyn Fn(&Solver, usize)>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LBool {
    True,
    False,
    Undef,
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

#[derive(Default)]
pub struct Solver {
    vars: Vec<(LBool, Vec<usize>, Vec<usize>)>, // (value, pos clauses, neg clauses)
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
        self.vars.push((LBool::Undef, Vec::new(), Vec::new()));
        var_id
    }

    pub fn value(&self, var: usize) -> LBool {
        self.vars[var].0.clone()
    }

    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        let clause_id = self.clauses.len();
        for lit in lits {
            if lit.is_positive() {
                self.vars[lit.var()].1.push(clause_id);
            } else {
                self.vars[lit.var()].2.push(clause_id);
            }
        }
        self.clauses.push(lits.to_vec());
        true
    }

    pub fn assert(&mut self, lit: &Lit) -> bool {
        self.enqueue(lit, None);
        while let Some((var, reason)) = self.prop_q.pop_front() {
            let clauses = if self.value(var) == LBool::True {
                self.vars[var].1.clone()
            } else {
                self.vars[var].2.clone()
            };
            for clause_id in clauses {
                if reason == Some(clause_id) {
                    continue;
                }
                let mut num_undef = 0;
                let mut last_undef: Option<Lit> = None;
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
                if num_undef == 1 && last_undef.is_some() {
                    return self.enqueue(&last_undef.unwrap(), Some(clause_id));
                } else {
                    return false;
                }
            }
        }
        true
    }

    fn enqueue(&mut self, lit: &Lit, reason: Option<usize>) -> bool {
        match self.value(lit.var()) {
            LBool::Undef => {
                self.vars[lit.var()].0 = if lit.is_positive() {
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
