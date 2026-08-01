pub mod ast;
mod lin;
mod lit;
mod rational;

use crate::smt::{ast::BoolExpr, lit::Lit};
use std::{
    borrow::Borrow,
    collections::{HashMap, VecDeque},
};
use tracing::trace;
use tracing_subscriber::fmt::writer::EitherWriter::B;

pub struct SMT {
    sat_to_ast: Vec<Option<BoolExpr>>,    // Map from SAT variable index to its corresponding AST expression
    ast_to_sat: HashMap<BoolExpr, usize>, // Map from AST expression to its corresponding SAT variable index
    bools: Vec<Option<bool>>,             // Current assignment of each boolean variable (true, false, or unassigned)
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

    fn get_or_create_proxy(&mut self, expr: &BoolExpr) -> usize {
        if let Some(&sat_var) = self.ast_to_sat.get(&expr) {
            return sat_var;
        }

        let proxy = self.new_bool();

        if proxy >= self.sat_to_ast.len() {
            self.sat_to_ast.resize(proxy + 1, None);
        }

        self.sat_to_ast[proxy] = Some(expr.clone());
        self.ast_to_sat.insert(expr.clone(), proxy);

        proxy
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
        // let mut lits = Vec::with_capacity(1 + or.len());
        if or.is_empty() {
            BoolExpr::False
        } else if or.len() == 1 {
            or.into_iter().next().unwrap()
        } else {
            BoolExpr::Or(or)
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

    fn lit_value(&self, lit: &Lit) -> Option<bool> {
        if lit.sign() { self.bools[lit.var()].map(|v| !v) } else { self.bools[lit.var()] }
    }

    fn level(&self, var: usize) -> Option<usize> {
        self.level[var]
    }

    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }
}
