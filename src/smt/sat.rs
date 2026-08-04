use crate::smt::ast::BoolExpr;
use std::{
    collections::{HashSet, VecDeque},
    fmt, mem, ops,
};
use tracing::trace;

pub(super) struct SatSolver {
    assigns: Vec<Option<bool>>, // Current assignments of boolean variables (None = unassigned, Some(true/false) = assigned)
    clauses: Vec<Clause>,       // List of clauses in the solver
    watches: Vec<Vec<usize>>,   // Watch lists for each literal (positive and negative)
    reason: Vec<Option<usize>>, // Reason for each variable's assignment
    prop_q: VecDeque<Lit>,      // Queue of literals to propagate
    trail: Vec<Lit>,            // Trail of assigned literals for backtracking
    trail_lim: Vec<usize>,      // Indices in the trail where decisions were made
    level: Vec<Option<usize>>,  // Decision level for each variable
}

impl SatSolver {
    pub(super) fn new() -> Self {
        SatSolver {
            assigns: Vec::new(),
            clauses: Vec::new(),
            watches: Vec::new(),
            reason: Vec::new(),
            prop_q: VecDeque::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            level: Vec::new(),
        }
    }

    pub(super) fn mk_bool(&mut self) -> usize {
        let idx = self.assigns.len();
        self.assigns.push(None);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new()); // For the negated literal
        self.reason.push(None);
        self.level.push(None);
        idx
    }

    pub(super) fn decide(&mut self, lit: Lit) -> Result<(), (usize, Vec<Lit>)> {
        self.trail_lim.push(self.trail.len());
        self.enqueue(lit, None);
        self.propagate()
    }

    pub(super) fn propagate(&mut self) -> Result<(), (usize, Vec<Lit>)> {
        while let Some(lit) = self.prop_q.pop_front() {
            let falsified = !lit;
            let falsified_index = falsified.index();
            let watches = mem::take(&mut self.watches[falsified_index]);
            for i in 0..watches.len() {
                let clause_idx = watches[i];
                // Keep the first watched literal as the other watcher and the second as the falsified one.
                if self.clauses[clause_idx].lits[0] == falsified {
                    self.clauses[clause_idx].lits.swap(0, 1);
                }

                // Check if clause is already satisfied
                if self.lit_value(&self.clauses[clause_idx].lits[0]) == Some(true) {
                    self.watches[lit.index()].push(clause_idx);
                    continue;
                }

                // Find a replacement watcher that is not currently false.
                let mut found_replacement = false;
                for j in 2..self.clauses[clause_idx].lits.len() {
                    let next_lit = self.clauses[clause_idx].lits[j];
                    if self.lit_value(&next_lit) != Some(false) {
                        self.clauses[clause_idx].lits.swap(1, j);
                        self.watches[next_lit.index()].push(clause_idx);
                        found_replacement = true;
                        break;
                    }
                }

                if found_replacement {
                    continue;
                }

                // If we reach here, the clause is either unit or unsatisfied
                self.watches[falsified_index].push(clause_idx); // Re-add the clause to the watch list
                if !self.enqueue(self.clauses[clause_idx].lits[0], Some(clause_idx)) {
                    for c_i in watches.iter().skip(i + 1) {
                        self.watches[falsified_index].push(*c_i);
                    }
                    self.prop_q.clear();
                    return Err(self.analyze_conflict(clause_idx));
                }
            }
        }
        Ok(())
    }

    fn analyze_conflict(&mut self, mut clause_idx: usize) -> (usize, Vec<Lit>) {
        let mut seen: HashSet<usize> = HashSet::new();
        let mut counter: usize = 0;
        let mut p: Option<(Lit, Option<usize>)> = None;
        let mut learnt = Vec::new();
        learnt.push(Lit::new(0, false)); // Placeholder for the asserting literal
        let mut backtrack_level: usize = 0;

        loop {
            // 1. Process the current clause (either the conflict or a reason)
            for lit in &self.clauses[clause_idx].lits {
                // Skip the variable we are currently resolving away
                if Some(lit.var()) == p.map(|l| l.0.var()) {
                    continue;
                }

                if !seen.contains(&lit.var()) {
                    seen.insert(lit.var());
                    if self.level(lit.var()).expect("Variable should have a level") == self.decision_level() {
                        counter += 1;
                    } else {
                        // This literal comes from a previous decision level
                        learnt.push(*lit);
                        backtrack_level = backtrack_level.max(self.level(lit.var()).expect("Variable should have a level"));
                    }
                }
            }

            // 2. Find the next variable from the trail assigned at this level
            p = loop {
                let lit = *self.trail.last().expect("There should be a literal");
                let reason = self.reason[lit.var()];
                self.undo_one();
                if seen.contains(&lit.var()) {
                    break Some((lit, reason));
                }
            };
            counter -= 1;

            if counter == 0 {
                // 3. We have found the asserting literal
                learnt[0] = !p.expect("There should be a literal").0;
                break;
            }

            // 4. Update clause to the reason of the variable we just resolved away
            clause_idx = p.expect("There should be a literal").1.expect("There should be a reason");
        }

        return (backtrack_level, learnt);
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        trace!("Enqueue {}{}", lit, reason.map_or("".to_string(), |r| format!(" (reason: {})", r)));
        match self.lit_value(&lit) {
            None => {
                self.assigns[lit.var()] = if lit.sign() { Some(false) } else { Some(true) };
                self.level[lit.var()] = Some(self.decision_level());
                self.reason[lit.var()] = reason;
                self.trail.push(lit);
                self.prop_q.push_back(lit);
                true
            }
            Some(value) => value,
        }
    }

    pub(super) fn add_clause(&mut self, lits: impl IntoIterator<Item = Lit>) -> Result<(), Vec<Lit>> {
        let mut lits = lits.into_iter().collect::<Vec<_>>();
        match lits.len() {
            0 => return Err(lits),
            1 => {
                self.cancel_until(0);
                if !self.enqueue(lits[0], None) {
                    return Err(lits);
                }
            }
            _ => {
                let clause_index = self.clauses.len();
                lits.sort_by_key(|l| self.assigns.get(l.var()).copied().unwrap_or(None).is_some());
                let clause = Clause { lits: lits.clone() };
                trace!("Adding clause {}: {}", clause_index, clause);
                for lit in &clause.lits[0..2] {
                    self.watches[lit.index()].push(clause_index);
                }
                self.clauses.push(clause);
                if self.lit_value(&lits[0]).is_none() && self.lit_value(&lits[1]) == Some(false) && !self.enqueue(lits[0], Some(clause_index)) {
                    return Err(lits);
                }
            }
        }
        Ok(())
    }

    fn lit_value(&self, lit: &Lit) -> Option<bool> {
        let val = self.assigns.get(lit.var()).expect("Variable index out of bounds");
        if lit.sign() { val.map(|v| !v) } else { *val }
    }

    fn level(&self, var: usize) -> &Option<usize> {
        self.level.get(var).expect("Variable index out of bounds")
    }

    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    fn undo_one(&mut self) {
        if let Some(lit) = self.trail.pop() {
            trace!("Undoing assignment of {}", lit);
            self.assigns[lit.var()] = None;
            self.reason[lit.var()] = None;
            self.level[lit.var()] = None;
        }
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        trace!("Canceling until level {}", level);
        while self.decision_level() > level {
            let lim = self.trail_lim.pop().unwrap();
            while self.trail.len() > lim {
                self.undo_one();
            }
        }
    }
}

// Compact encoding: x = var*2 + sign_bit, where sign_bit=1 means negated (MiniSat convention).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Lit {
    x: usize,
}

impl Lit {
    pub(super) fn new(var: usize, sign: bool) -> Self {
        Lit { x: var * 2 + sign as usize }
    }

    /// Variable index.
    pub(super) fn var(self) -> usize {
        self.x >> 1
    }

    /// True if this is a negated literal.
    pub(super) fn sign(self) -> bool {
        self.x & 1 != 0
    }

    /// Compact integer index suitable for watch-list indexing (MiniSat's toInt).
    pub(super) fn index(self) -> usize {
        self.x
    }
}

impl ops::Not for Lit {
    type Output = Self;

    fn not(self) -> Self {
        Lit { x: self.x ^ 1 }
    }
}

impl From<&BoolExpr> for Lit {
    fn from(expr: &BoolExpr) -> Self {
        match expr {
            BoolExpr::Var(v) => Lit::new(*v, false),
            BoolExpr::Not(inner) => {
                if let BoolExpr::Var(v) = inner.as_ref() {
                    Lit::new(*v, true)
                } else {
                    panic!("Unsupported expression type for conversion to literal: {}", expr);
                }
            }
            _ => panic!("Unsupported expression type for conversion to literal: {}", expr),
        }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.sign() { write!(f, "¬b{}", self.var()) } else { write!(f, "b{}", self.var()) }
    }
}

struct Clause {
    lits: Vec<Lit>, // List of literals in the clause
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<String> = self.lits.iter().map(|l| l.to_string()).collect();
        write!(f, "({})", lits.join(" ∨ "))
    }
}

#[cfg(test)]
mod tests {
    use tracing::{Level, subscriber};

    use super::*;

    #[test]
    fn test_conflict_analysis() {
        let subscriber = tracing_subscriber::fmt().with_max_level(Level::TRACE).finish();
        subscriber::set_global_default(subscriber).expect("Failed to set global default subscriber");

        let mut sat = SatSolver::new();
        let b1 = sat.mk_bool();
        let b2 = sat.mk_bool();
        let b3 = sat.mk_bool();
        let b4 = sat.mk_bool();
        let b5 = sat.mk_bool();
        let b6 = sat.mk_bool();
        let b7 = sat.mk_bool();
        let b8 = sat.mk_bool();
        let b9 = sat.mk_bool();

        // [(b1 ∨ b2) ∧ (b1 ∨ b3 ∨ b7) ∧ (¬b2 ∨ ¬b3 ∨ b4) ∧ (¬b4 ∨ b5 ∨ b8) ∧ (¬b4 ∨ b6 ∨ b9) ∧ (¬b5 ∨ ¬b6)]
        sat.add_clause([Lit::new(b1, false), Lit::new(b2, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b1, false), Lit::new(b3, false), Lit::new(b7, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b2, true), Lit::new(b3, true), Lit::new(b4, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b4, true), Lit::new(b5, false), Lit::new(b8, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b4, true), Lit::new(b6, false), Lit::new(b9, false)]).expect("Should be able to add clause");
        sat.add_clause([Lit::new(b5, true), Lit::new(b6, true)]).expect("Should be able to add clause");

        // Decision: ¬b7
        sat.decide(Lit::new(b7, true)).expect("Should be able to decide ¬b7");
        // Decision: ¬b8
        sat.decide(Lit::new(b8, true)).expect("Should be able to decide ¬b8");
        // Decision: ¬b9
        sat.decide(Lit::new(b9, true)).expect("Should be able to decide ¬b9");
        // Decision: ¬b1
        let result = sat.decide(Lit::new(b1, true));
        assert!(result.is_err());
        let (bt_level, conflict_clause) = result.unwrap_err();
        assert_eq!(bt_level, 3);
        sat.cancel_until(bt_level);
        sat.add_clause(conflict_clause).expect("Should be able to add learnt clause");
    }
}
