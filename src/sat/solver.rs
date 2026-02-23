use crate::{Lit, utils::lit::LBool};
use std::collections::{HashMap, VecDeque};
type Callback = Box<dyn Fn(&Solver, usize)>;

#[derive(Default)]
struct Var {
    value: LBool,                   // current value
    current_level_vars: Vec<usize>, // variables assigned at the current decision level
    decision_var: Option<usize>,    // decision variable that led to this assignment
    reason: Option<usize>,          // clause that implied the value
    pos_clauses: Vec<usize>,        // clauses where the variable appears positively
    neg_clauses: Vec<usize>,        // clauses where the variable appears negatively
}

#[derive(Default)]
pub struct Solver {
    vars: Vec<Var>,
    clauses: Vec<Vec<Lit>>,
    prop_q: VecDeque<usize>,
    listeners: HashMap<usize, Vec<Callback>>,
}

impl Solver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_var(&mut self) -> usize {
        let var_id = self.vars.len();
        self.vars.push(Var::default());
        var_id
    }

    pub fn value(&self, var: usize) -> &LBool {
        &self.vars[var].value
    }

    pub fn lit_value(&self, lit: &Lit) -> LBool {
        match self.value(lit.var()) {
            LBool::Undef => LBool::Undef,
            val => {
                if (val == &LBool::True) == lit.is_positive() {
                    LBool::True
                } else {
                    LBool::False
                }
            }
        }
    }

    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        if lits.is_empty() {
            return false;
        }
        if lits.len() == 1 {
            return self.assert(lits[0]);
        }

        let clause_id = self.clauses.len();
        for lit in &lits[..2] {
            if lit.is_positive() {
                self.vars[lit.var()].pos_clauses.push(clause_id);
            } else {
                self.vars[lit.var()].neg_clauses.push(clause_id);
            }
        }
        self.clauses.push(lits.to_vec());
        true
    }

    pub fn assert(&mut self, lit: Lit) -> bool {
        self.enqueue(lit, None);
        while let Some(var) = self.prop_q.pop_front() {
            self.vars[lit.var()].current_level_vars.push(var);
            self.vars[var].decision_var = Some(lit.var());
            let clauses = if self.value(var) == &LBool::True { std::mem::take(&mut self.vars[var].neg_clauses) } else { std::mem::take(&mut self.vars[var].pos_clauses) };
            for clause_id in clauses {
                if !self.propagate(clause_id, var) {
                    let current_level_vars = std::mem::take(&mut self.vars[lit.var()].current_level_vars);
                    self.analyze_conflict(clause_id, current_level_vars);
                    return false;
                }
            }
        }
        true
    }

    pub fn retract(&mut self, var: usize) {
        assert!(var < self.vars.len(), "Variable index out of bounds");
        assert!(self.value(var) != &LBool::Undef, "Variable is already unassigned");
    }

    fn watch_lit(&mut self, lit: &Lit, clause_id: usize) {
        if lit.is_positive() {
            self.vars[lit.var()].pos_clauses.push(clause_id);
        } else {
            self.vars[lit.var()].neg_clauses.push(clause_id);
        }
    }

    fn propagate(&mut self, clause_id: usize, var: usize) -> bool {
        // Ensure the first literal is not the one that was just assigned
        if self.clauses[clause_id][0].var() == var {
            self.clauses[clause_id].swap(0, 1);
        }

        // Check if clause is already satisfied
        if self.lit_value(&self.clauses[clause_id][0]) == LBool::True {
            if self.clauses[clause_id][1].is_positive() {
                self.vars[self.clauses[clause_id][1].var()].pos_clauses.push(clause_id);
            } else {
                self.vars[self.clauses[clause_id][1].var()].neg_clauses.push(clause_id);
            }
            return true;
        }

        // Find the next unassigned literal
        for i in 2..self.clauses[clause_id].len() {
            if self.lit_value(&self.clauses[clause_id][i]) != LBool::False {
                // Move this literal to the second position
                self.clauses[clause_id].swap(1, i);
                // Update watchers
                if self.clauses[clause_id][1].is_positive() {
                    self.vars[self.clauses[clause_id][1].var()].pos_clauses.push(clause_id);
                } else {
                    self.vars[self.clauses[clause_id][1].var()].neg_clauses.push(clause_id);
                }
                return true;
            }
        }

        // If we reach here, all other literals are false, so we must propagate the first literal
        if self.value(var) == &LBool::True {
            self.vars[var].pos_clauses.push(clause_id);
        } else {
            self.vars[var].neg_clauses.push(clause_id);
        }
        self.enqueue(self.clauses[clause_id][0], Some(clause_id))
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        match self.value(lit.var()) {
            LBool::Undef => {
                self.vars[lit.var()].value = if lit.is_positive() { LBool::True } else { LBool::False };
                self.vars[lit.var()].reason = reason;
                self.prop_q.push_back(lit.var());
                self.notify(lit.var());
                true
            }
            LBool::True => lit.is_positive(),
            LBool::False => !lit.is_positive(),
        }
    }

    fn analyze_conflict(&self, clause_id: usize, mut current_level_vars: Vec<usize>) {}

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
        self.listeners.entry(var).or_default().push(Box::new(listener));
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
        assert_eq!(solver.value(v0), &LBool::Undef);
    }

    #[test]
    fn test_assignment_propagation() {
        let mut solver = Solver::new();
        let v0 = solver.add_var();
        let v1 = solver.add_var();

        // Clause: v0 or v1
        solver.add_clause(&[Lit::new(v0, true), Lit::new(v1, true)]);

        // Assert !v0
        let ret = solver.assert(Lit::new(v0, false));
        assert!(ret, "Solver should be consistent");

        // v0 should be False
        assert_eq!(solver.value(v0), &LBool::False);
        // v1 should be implied True
        assert_eq!(solver.value(v1), &LBool::True);
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
        solver.assert(Lit::new(v0, true));

        assert_eq!(solver.value(v0), &LBool::True);
        assert_eq!(solver.value(v1), &LBool::True);
        assert_eq!(solver.value(v2), &LBool::True);
    }

    #[test]
    fn test_listener() {
        let mut solver = Solver::new();
        let v0 = solver.add_var();

        solver.add_listener(v0, move |_solver, var| {
            assert_eq!(var, v0);
        });
    }

    #[test]
    fn test_2wl_correctness() {
        let mut solver = Solver::new();
        let v0 = solver.add_var();
        let v1 = solver.add_var();
        let v2 = solver.add_var();
        let v3 = solver.add_var();

        // Clause: v0 or v1 or v2 or v3
        solver.add_clause(&[Lit::new(v0, true), Lit::new(v1, true), Lit::new(v2, true), Lit::new(v3, true)]);

        // Initially, watchers are the first two literals: v0 and v1
        assert!(solver.vars[v0].pos_clauses.contains(&0));
        assert!(solver.vars[v1].pos_clauses.contains(&0));
        assert!(!solver.vars[v2].pos_clauses.contains(&0));
        assert!(!solver.vars[v3].pos_clauses.contains(&0));

        // Assign !v1. Watch on v1 should move to v2.
        solver.assert(Lit::new(v1, false));
        assert!(solver.vars[v0].pos_clauses.contains(&0));
        assert!(!solver.vars[v1].pos_clauses.contains(&0));
        assert!(solver.vars[v2].pos_clauses.contains(&0));
        assert!(!solver.vars[v3].pos_clauses.contains(&0));

        // Assign !v2. Watch on v2 should move to v3.
        solver.assert(Lit::new(v2, false));
        assert!(solver.vars[v0].pos_clauses.contains(&0));
        assert!(!solver.vars[v1].pos_clauses.contains(&0));
        assert!(!solver.vars[v2].pos_clauses.contains(&0));
        assert!(solver.vars[v3].pos_clauses.contains(&0));

        // Assign !v3. No more watchers available. Should propagate v0.
        solver.assert(Lit::new(v3, false));
        assert_eq!(solver.value(v0), &LBool::True);
    }

    #[test]
    fn test_2wl_lazy_update() {
        let mut solver = Solver::new();
        let v0 = solver.add_var();
        let v1 = solver.add_var();
        let v2 = solver.add_var();

        // Clause: v0 or v1 or v2
        solver.add_clause(&[Lit::new(v0, true), Lit::new(v1, true), Lit::new(v2, true)]);

        // Watchers: v0, v1
        assert!(solver.vars[v0].pos_clauses.contains(&0));
        assert!(solver.vars[v1].pos_clauses.contains(&0));

        // Satisfy the clause with v0
        solver.assert(Lit::new(v0, true));
        // Watchers shouldn't change eagerly
        assert!(solver.vars[v0].pos_clauses.contains(&0));
        assert!(solver.vars[v1].pos_clauses.contains(&0));

        // Now falsify v1. Since clause is satisfied by v0, watch on v1 should remain (or just be re-added).
        solver.assert(Lit::new(v1, false));
        assert!(solver.vars[v1].pos_clauses.contains(&0));
        // Watch shouldn't move to v2 because v0 is true.
        assert!(!solver.vars[v2].pos_clauses.contains(&0));
    }
}
