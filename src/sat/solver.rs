use crate::{Lit, utils::lit::LBool};
use std::collections::{HashMap, VecDeque};
type Callback = Box<dyn Fn(&Solver, usize)>;

struct Var {
    value: LBool,            // current value
    reason: Option<usize>,   // clause that implied the value
    pos_clauses: Vec<usize>, // clauses where the variable appears positively
    neg_clauses: Vec<usize>, // clauses where the variable appears negatively
}

impl Var {
    fn new() -> Self {
        Var {
            value: LBool::Undef,
            reason: None,
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
        let mut current_level_vars = Vec::new();
        self.enqueue(lit, None);
        while let Some((var, reason)) = self.prop_q.pop_front() {
            current_level_vars.push(var); // Track order!
            let clauses = if self.value(var) == LBool::True {
                self.vars[var].neg_clauses.clone()
            } else {
                self.vars[var].pos_clauses.clone()
            };
            for clause_id in clauses {
                if reason != Some(clause_id) && !self.propagate(clause_id) {
                    self.analyze_conflict(clause_id, &current_level_vars);
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
            let val = self.value(lit.var());
            match val {
                LBool::Undef => {
                    num_undef += 1;
                    last_undef = Some(lit);
                }
                LBool::True => {
                    if lit.is_positive() {
                        return true;
                    }
                }
                LBool::False => {
                    if !lit.is_positive() {
                        return true;
                    }
                }
            }
            if num_undef > 1 {
                return true;
            }
        }
        if num_undef == 1 {
            assert!(last_undef.is_some());
            return self.enqueue(&last_undef.unwrap(), Some(clause_id));
        }
        false
    }

    fn enqueue(&mut self, lit: &Lit, reason: Option<usize>) -> bool {
        match self.value(lit.var()) {
            LBool::Undef => {
                self.vars[lit.var()].value = if lit.is_positive() {
                    LBool::True
                } else {
                    LBool::False
                };
                self.vars[lit.var()].reason = reason;
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

    fn analyze_conflict(&self, _clause_id: usize, _current_level_vars: &Vec<usize>) {}

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

impl std::fmt::Display for Solver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, var) in self.vars.iter().enumerate() {
            writeln!(f, "b{}: {:?}", i, var.value)?;
        }
        for clause in &self.clauses {
            let lits: Vec<String> = clause.iter().map(|l| l.to_string()).collect();
            writeln!(f, "{}", lits.join(" ∨ "))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Lit, utils::lit::LBool};

    #[test]
    fn test_add_var() {
        let mut solver = Solver::new();
        let v0 = solver.add_var();
        let v1 = solver.add_var();
        assert_eq!(v0, 0);
        assert_eq!(v1, 1);
        assert_eq!(solver.value(v0), LBool::Undef);
    }

    #[test]
    fn test_assignment_propagation() {
        let mut solver = Solver::new();
        let v0 = solver.add_var();
        let v1 = solver.add_var();

        // Clause: v0 or v1
        solver.add_clause(&[Lit::new(v0, true), Lit::new(v1, true)]);

        // Assert !v0
        let ret = solver.assert(&Lit::new(v0, false));
        assert!(ret, "Solver should be consistent");

        // v0 should be False
        assert_eq!(solver.value(v0), LBool::False);
        // v1 should be implied True
        assert_eq!(solver.value(v1), LBool::True);
    }

    #[test]
    fn test_chain_propagation() {
        let mut solver = Solver::new();
        let v0 = solver.add_var();
        let v1 = solver.add_var();
        let v2 = solver.add_var();

        // v0 -> v1 (equivalent to !v0 or v1)
        solver.add_clause(&[Lit::new(v0, false), Lit::new(v1, true)]);
        // v1 -> v2 (equivalent to !v1 or v2)
        solver.add_clause(&[Lit::new(v1, false), Lit::new(v2, true)]);

        // Assert v0
        solver.assert(&Lit::new(v0, true));

        assert_eq!(solver.value(v0), LBool::True);
        assert_eq!(solver.value(v1), LBool::True);
        assert_eq!(solver.value(v2), LBool::True);
    }

    #[test]
    fn test_listener() {
        let mut solver = Solver::new();
        let v0 = solver.add_var();

        solver.add_listener(v0, move |_solver, var| {
            assert_eq!(var, v0);
        });
    }
}
