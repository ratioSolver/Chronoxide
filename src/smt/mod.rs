pub mod ast;
mod lin;
mod lit;
mod rational;

use crate::smt::{ast::BoolExpr, lit::Lit};
use std::{
    borrow::Borrow,
    collections::{HashMap, VecDeque},
    fmt,
};
use tracing::trace;

pub struct SMT {
    sat_to_ast: Vec<Option<BoolExpr>>,    // Map from SAT variable index to its corresponding AST expression
    ast_to_sat: HashMap<BoolExpr, usize>, // Map from AST expression to its corresponding SAT variable index
    bools: Vec<Option<bool>>,             // Current assignment of each boolean variable (true, false, or unassigned)
    clauses: Vec<Clause>,                 // List of clauses in the solver
    watches: Vec<Vec<usize>>,             // Watch lists for each literal (positive and negative)
    reason: Vec<Option<usize>>,           // Reason for each variable's assignment
    prop_q: VecDeque<Lit>,                // Queue of literals to propagate
    trail: Vec<Lit>,                      // Trail of assigned literals for backtracking
    trail_lim: Vec<usize>,                // Indices in the trail where decisions were made
    level: Vec<Option<usize>>,            // Decision level for each variable
}

impl Default for SMT {
    fn default() -> Self {
        Self::new()
    }
}

impl SMT {
    pub fn new() -> Self {
        SMT {
            sat_to_ast: Vec::new(),
            ast_to_sat: HashMap::new(),
            bools: Vec::new(),
            clauses: Vec::new(),
            watches: Vec::new(),
            reason: Vec::new(),
            prop_q: VecDeque::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            level: Vec::new(),
        }
    }

    fn new_bool(&mut self) -> usize {
        let idx = self.bools.len();
        self.bools.push(None);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new()); // For the negated literal
        self.reason.push(None);
        self.level.push(None);
        idx
    }

    fn get_proxy(&mut self, expr: &BoolExpr) -> Option<usize> {
        self.ast_to_sat.get(expr).copied()
    }

    fn create_proxy(&mut self, expr: BoolExpr) -> usize {
        let proxy = self.new_bool();

        if proxy >= self.sat_to_ast.len() {
            self.sat_to_ast.resize(proxy + 1, None);
        }

        self.sat_to_ast[proxy] = Some(expr.clone());
        self.ast_to_sat.insert(expr, proxy);

        proxy
    }

    fn get_or_create_proxy(&mut self, expr: &BoolExpr) -> usize {
        if let Some(proxy) = self.get_proxy(expr) { proxy } else { self.create_proxy(expr.clone()) }
    }

    pub fn assert<T: Borrow<BoolExpr>>(&mut self, expr: T) -> bool {
        trace!("Asserting: {}", expr.borrow());
        match expr.borrow() {
            BoolExpr::True => true,
            BoolExpr::False => false,
            BoolExpr::Var(_) => {
                let proxy = self.get_or_create_proxy(expr.borrow());
                self.enqueue(Lit::new(proxy, false), None)
            }
            BoolExpr::Not(inner) => {
                let proxy = self.get_or_create_proxy(inner);
                self.enqueue(Lit::new(proxy, true), None)
            }
            _ => todo!(),
        }
    }

    fn mk_or(&mut self, or: Vec<BoolExpr>) -> BoolExpr {
        let mut lits = Vec::with_capacity(1 + or.len());
        for expr in &or {
            match expr {
                BoolExpr::True => return BoolExpr::True,
                BoolExpr::False => continue,
                BoolExpr::Not(inner) => {
                    let proxy = self.get_or_create_proxy(inner);
                    lits.push(Lit::new(proxy, true));
                }
                _ => todo!(),
            }
        }
        match lits.len() {
            0 => BoolExpr::False,
            1 => {
                if lits[0].sign() {
                    BoolExpr::Not(Box::new(BoolExpr::Var(lits[0].var())))
                } else {
                    BoolExpr::Var(lits[0].var())
                }
            }
            _ => {
                let or = BoolExpr::Or(lits.iter().map(|lit| if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(lit.var()))) } else { BoolExpr::Var(lit.var()) }).collect());
                if let Some(proxy) = self.get_proxy(&or) {
                    BoolExpr::Var(proxy)
                } else {
                    let proxy = self.create_proxy(or);
                    lits.push(Lit::new(proxy, false));
                    self.add_clause(lits).unwrap();
                    BoolExpr::Var(proxy)
                }
            }
        }
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        trace!("Enqueue {}{}", lit, reason.map_or("".to_string(), |r| format!(" (reason: {})", r)));
        match self.lit_value(&lit) {
            None => {
                self.bools[lit.var()] = if lit.sign() { Some(false) } else { Some(true) };
                self.level[lit.var()] = Some(self.decision_level());
                self.reason[lit.var()] = reason;
                self.trail.push(lit);
                self.prop_q.push_back(lit);
                true
            }
            Some(value) => {
                if value == !lit.sign() {
                    trace!("Conflict detected for literal {}", lit);
                    false
                } else {
                    true
                }
            }
        }
    }

    fn add_clause(&mut self, lits: impl IntoIterator<Item = Lit>) -> Result<(), Vec<Lit>> {
        let clause_index = self.clauses.len();
        let mut clause = Clause { lits: lits.into_iter().collect::<Vec<_>>() };
        trace!("Adding clause {}: {}", clause_index, clause);
        if clause.lits.is_empty() {
            return Err(clause.lits);
        } else if clause.lits.len() == 1 {
            self.cancel_until(0);
            if !self.enqueue(clause.lits[0], Some(clause_index)) {
                return Err(clause.lits);
            }
        } else {
            clause.lits.sort_by_key(|l| self.bools.get(l.var()).copied().unwrap_or(None) != None);
            for lit in &clause.lits[0..2] {
                self.watches[lit.index()].push(clause_index);
            }
            if self.lit_value(&clause.lits[0]) == None && self.lit_value(&clause.lits[1]) == Some(false) && !self.enqueue(clause.lits[0], Some(clause_index)) {
                return Err(clause.lits);
            }
            self.clauses.push(clause);
        }

        Ok(())
    }

    fn lit_value(&self, lit: &Lit) -> Option<bool> {
        if lit.sign() { self.bools[lit.var()].map(|v| !v) } else { self.bools[lit.var()] }
    }

    fn level(&self, var: usize) -> Option<usize> {
        self.level[var]
    }

    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    fn undo_one(&mut self) {
        if let Some(lit) = self.trail.pop() {
            trace!("Undoing assignment of {}", lit);
            self.bools[lit.var()] = None;
            self.reason[lit.var()] = None;
            self.level[lit.var()] = None;
        }
    }

    pub fn cancel_until(&mut self, level: usize) {
        trace!("Canceling until level {}", level);
        while self.decision_level() > level {
            let lim = self.trail_lim.pop().unwrap();
            while self.trail.len() > lim {
                self.undo_one();
            }
        }
    }
}

struct Clause {
    lits: Vec<Lit>, // List of literals in the clause
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<String> = self.lits.iter().map(|l| l.to_string()).collect();
        write!(f, "{}", lits.join(" ∨ "))
    }
}
