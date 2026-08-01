pub mod ast;
mod lin;
mod lit;
mod rational;

use crate::smt::{
    ast::{ArithExpr, BoolExpr},
    lin::Lin,
    lit::Lit,
    rational::{InfRational, Rational},
};
use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap, VecDeque},
    fmt,
};
use tracing::trace;

pub struct SMT {
    sat_to_ast: Vec<Option<BoolExpr>>,                            // Map from SAT variable index to its corresponding AST expression
    ast_to_sat: HashMap<BoolExpr, usize>,                         // Map from AST expression to its corresponding SAT variable index
    bools: Vec<Option<bool>>,                                     // Current assignment of each boolean variable (true, false, or unassigned)
    clauses: Vec<Clause>,                                         // List of clauses in the solver
    watches: Vec<Vec<usize>>,                                     // Watch lists for each literal (positive and negative)
    reason: Vec<Option<usize>>,                                   // Reason for each variable's assignment
    prop_q: VecDeque<Lit>,                                        // Queue of literals to propagate
    trail: Vec<Lit>,                                              // Trail of assigned literals for backtracking
    trail_lim: Vec<usize>,                                        // Indices in the trail where decisions were made
    level: Vec<Option<usize>>,                                    // Decision level for each variable
    ints: Vec<bool>,                                              // Distinguish between integer and real variables
    reals: Vec<Rational>,                                         // Current assignments of real variables
    lbs: Vec<Rational>,                                           // Current assignments of lower bounds
    ubs: Vec<Rational>,                                           // Current assignments of upper bounds
    lin_to_slack: HashMap<BTreeMap<usize, rug::Rational>, usize>, // Mapping from linear constraints to their corresponding slack variable
    tableau: BTreeMap<usize, BTreeMap<usize, rug::Rational>>,     // Tableau for linear constraints
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
            ints: Vec::new(),
            reals: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            lin_to_slack: HashMap::new(),
            tableau: BTreeMap::new(),
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

    fn new_int(&mut self) -> usize {
        let var_index = self.ints.len();
        self.ints.push(true);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        var_index
    }

    fn new_real(&mut self) -> usize {
        let var_index = self.reals.len();
        self.ints.push(false);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        var_index
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

    fn get_or_create_proxy<T: Borrow<BoolExpr>>(&mut self, expr: T) -> usize {
        if let Some(proxy) = self.get_proxy(expr.borrow()) { proxy } else { self.create_proxy(expr.borrow().clone()) }
    }

    pub fn assert<T: Borrow<BoolExpr>>(&mut self, expr: T) -> bool {
        trace!("Asserting: {}", expr.borrow());
        match self.mk_expr(expr.borrow()) {
            BoolExpr::True => true,
            BoolExpr::False => false,
            BoolExpr::Var(_) => {
                let proxy = self.get_proxy(expr.borrow()).expect("Proxy should exist after mk_expr");
                self.enqueue(Lit::new(proxy, false), None)
            }
            BoolExpr::Not(inner) => {
                let proxy = self.get_proxy(inner.as_ref()).expect("Proxy should exist after mk_expr");
                self.enqueue(Lit::new(proxy, true), None)
            }
            _ => todo!(),
        }
    }

    fn mk_expr(&mut self, expr: &BoolExpr) -> BoolExpr {
        match expr {
            BoolExpr::True => BoolExpr::True,
            BoolExpr::False => BoolExpr::False,
            BoolExpr::Var(_) => {
                let proxy = self.get_or_create_proxy(expr);
                if let Some(level) = self.level(proxy)
                    && *level == 0
                {
                    match self.bools.get(proxy).expect("Variable index out of bounds") {
                        Some(true) => BoolExpr::True,
                        Some(false) => BoolExpr::False,
                        None => BoolExpr::Var(proxy),
                    }
                } else {
                    BoolExpr::Var(proxy)
                }
            }
            BoolExpr::Not(inner) => {
                let inner_expr = self.mk_expr(inner.as_ref());
                match inner_expr {
                    BoolExpr::True => BoolExpr::False,
                    BoolExpr::False => BoolExpr::True,
                    BoolExpr::Var(var) => BoolExpr::Not(Box::new(BoolExpr::Var(var))),
                    BoolExpr::Not(inner_inner) => *inner_inner,
                    _ => unreachable!(),
                }
            }
            BoolExpr::And(and) => self.mk_and(and),
            BoolExpr::Or(or) => self.mk_or(or),
            BoolExpr::Le(e1, e2) => self.mk_le(e1, e2, false),
            BoolExpr::Lt(e1, e2) => self.mk_le(e1, e2, true),
            BoolExpr::Ge(e1, e2) => self.mk_ge(e1, e2, false),
            BoolExpr::Gt(e1, e2) => self.mk_ge(e1, e2, true),
            _ => todo!(),
        }
    }

    fn mk_and(&mut self, and: &Vec<BoolExpr>) -> BoolExpr {
        let mut lits = Vec::with_capacity(and.len());
        for expr in and {
            let expr = self.mk_expr(expr);
            match expr {
                BoolExpr::True => continue,
                BoolExpr::False => return BoolExpr::False,
                BoolExpr::Var(_) => lits.push(Lit::new(self.get_proxy(&expr).expect("Proxy should exist after mk_expr"), false)),
                BoolExpr::Not(inner) => lits.push(Lit::new(self.get_proxy(inner.as_ref()).expect("Proxy should exist after mk_expr"), true)),
                _ => unreachable!(),
            }
        }
        match lits.len() {
            0 => BoolExpr::True,
            1 => {
                if lits[0].sign() {
                    BoolExpr::Not(Box::new(BoolExpr::Var(lits[0].var())))
                } else {
                    BoolExpr::Var(lits[0].var())
                }
            }
            _ => {
                let and = BoolExpr::And(lits.iter().map(|lit| if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(lit.var()))) } else { BoolExpr::Var(lit.var()) }).collect());
                if let Some(proxy) = self.get_proxy(&and) {
                    BoolExpr::Var(proxy)
                } else {
                    let proxy = self.create_proxy(and);
                    for lit in &lits {
                        if self.add_clause([Lit::new(proxy, true), *lit]).is_err() {
                            return BoolExpr::False;
                        }
                    }
                    BoolExpr::Var(proxy)
                }
            }
        }
    }

    fn mk_or(&mut self, or: &Vec<BoolExpr>) -> BoolExpr {
        let mut lits = Vec::with_capacity(1 + or.len());
        for expr in or {
            let expr = self.mk_expr(expr);
            match expr {
                BoolExpr::True => return BoolExpr::True,
                BoolExpr::False => continue,
                BoolExpr::Var(_) => lits.push(Lit::new(self.get_proxy(&expr).expect("Proxy should exist after mk_expr"), false)),
                BoolExpr::Not(inner) => lits.push(Lit::new(self.get_proxy(inner.as_ref()).expect("Proxy should exist after mk_expr"), true)),
                _ => unreachable!(),
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
                    for lit in &lits {
                        if self.add_clause([Lit::new(proxy, false), !*lit]).is_err() {
                            return BoolExpr::False;
                        }
                    }
                    lits.push(Lit::new(proxy, true));
                    if self.add_clause(lits).is_err() {
                        return BoolExpr::False;
                    }
                    BoolExpr::Var(proxy)
                }
            }
        }
    }

    fn mk_le(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> BoolExpr {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(if strict { const_term.is_negative() } else { const_term.is_negative() || const_term.is_zero() }),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();

                let eps_val = if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                let bound = InfRational::new(-const_term.clone() / coeff, eps_val / coeff);
                BoolExpr::Var(self.get_or_create_proxy(if coeff.is_positive() { BoolExpr::Ub(var, bound) } else { BoolExpr::Lb(var, bound) }))
            }
            _ => {
                let slack = if let Some(&slack) = self.lin_to_slack.get(&vars) {
                    slack
                } else {
                    let slack = self.new_real();
                    self.tableau.insert(slack, vars.clone());
                    self.lin_to_slack.insert(vars, slack);
                    slack
                };

                let eps_val = if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                BoolExpr::Var(self.get_or_create_proxy(BoolExpr::Ub(slack, InfRational::new(-const_term, eps_val))))
            }
        }
    }

    fn mk_arith_eq(&mut self, e1: &ArithExpr, e2: &ArithExpr) -> BoolExpr {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(const_term.is_zero()),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(-const_term.clone() / coeff, rug::Rational::from(0));
                BoolExpr::Var(self.get_or_create_proxy(BoolExpr::ArithEq(var, bound)))
            }
            _ => {
                let slack = if let Some(&slack) = self.lin_to_slack.get(&vars) {
                    slack
                } else {
                    let slack = self.new_real();
                    self.tableau.insert(slack, vars.clone());
                    self.lin_to_slack.insert(vars, slack);
                    slack
                };

                BoolExpr::Var(self.get_or_create_proxy(BoolExpr::ArithEq(slack, InfRational::new(-const_term, rug::Rational::from(0)))))
            }
        }
    }

    fn mk_ge(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> BoolExpr {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(if strict { const_term.is_positive() } else { const_term.is_positive() || const_term.is_zero() }),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();

                let eps_val = if strict { rug::Rational::from(1) } else { rug::Rational::from(0) };
                let bound = InfRational::new(-const_term.clone() / coeff, eps_val / coeff);
                BoolExpr::Var(self.get_or_create_proxy(if coeff.is_positive() { BoolExpr::Lb(var, bound) } else { BoolExpr::Ub(var, bound) }))
            }
            _ => {
                let slack = if let Some(&slack) = self.lin_to_slack.get(&vars) {
                    slack
                } else {
                    let slack = self.new_real();
                    self.tableau.insert(slack, vars.clone());
                    self.lin_to_slack.insert(vars, slack);
                    slack
                };

                let eps_val = if strict { rug::Rational::from(1) } else { rug::Rational::from(0) };
                BoolExpr::Var(self.get_or_create_proxy(BoolExpr::Lb(slack, InfRational::new(-const_term, eps_val))))
            }
        }
    }

    fn diff(&self, e1: &ArithExpr, e2: &ArithExpr) -> (BTreeMap<usize, rug::Rational>, rug::Rational) {
        let diff = Lin::from(e1) - Lin::from(e2);
        let mut vars = BTreeMap::new();

        for (var, coeff) in diff.vars {
            if let Some(basic) = self.tableau.get(&var) {
                for (&sub_var, sub_coeff) in basic {
                    *vars.entry(sub_var).or_insert_with(|| rug::Rational::from(0)) += coeff.clone() * sub_coeff;
                }
            } else {
                *vars.entry(var).or_insert_with(|| rug::Rational::from(0)) += coeff;
            }
        }

        vars.retain(|_, c| *c != 0);
        (vars, diff.const_term)
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
            clause.lits.sort_by_key(|l| self.bools.get(l.var()).copied().unwrap_or(None).is_some());
            for lit in &clause.lits[0..2] {
                self.watches[lit.index()].push(clause_index);
            }
            if self.lit_value(&clause.lits[0]).is_none() && self.lit_value(&clause.lits[1]) == Some(false) && !self.enqueue(clause.lits[0], Some(clause_index)) {
                return Err(clause.lits);
            }
            self.clauses.push(clause);
        }

        Ok(())
    }

    fn lit_value(&self, lit: &Lit) -> Option<bool> {
        if lit.sign() { self.bools[lit.var()].map(|v| !v) } else { self.bools[lit.var()] }
    }

    fn level(&self, var: usize) -> &Option<usize> {
        self.level.get(var).expect("Variable index out of bounds")
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::ast::BoolExpr;

    #[test]
    fn test_ast_to_sat_constants() {
        let mut solver = SMT::new();

        assert_eq!(solver.mk_expr(&BoolExpr::True), BoolExpr::True);
        assert_eq!(solver.mk_expr(&BoolExpr::False), BoolExpr::False);

        assert_eq!(solver.mk_expr(&BoolExpr::Not(Box::new(BoolExpr::True))), BoolExpr::False);
        assert_eq!(solver.mk_expr(&BoolExpr::Not(Box::new(BoolExpr::False))), BoolExpr::True);
    }

    #[test]
    fn test_ast_to_sat_var_caching() {
        let mut solver = SMT::new();

        let not_expr = BoolExpr::Not(Box::new(BoolExpr::Var(0)));

        let res1 = solver.mk_expr(&not_expr);
        let res2 = solver.mk_expr(&not_expr);

        assert_eq!(res1, res2, "mk_expr should return the same proxy for the same expression");
    }

    #[test]
    fn test_ast_to_sat_and_reduction() {
        let mut solver = SMT::new();

        assert_eq!(solver.mk_expr(&BoolExpr::And(vec![])), BoolExpr::True);
        assert_eq!(solver.mk_expr(&BoolExpr::And(vec![BoolExpr::Var(0)])), BoolExpr::Var(0));
        assert_eq!(solver.mk_expr(&BoolExpr::And(vec![BoolExpr::Var(0), BoolExpr::False])), BoolExpr::False);
    }

    #[test]
    fn test_ast_to_sat_or_reduction() {
        let mut solver = SMT::new();

        assert_eq!(solver.mk_expr(&BoolExpr::Or(vec![])), BoolExpr::False);
        assert_eq!(solver.mk_expr(&BoolExpr::Or(vec![BoolExpr::Var(0)])), BoolExpr::Var(0));
        assert_eq!(solver.mk_expr(&BoolExpr::Or(vec![BoolExpr::Var(0), BoolExpr::True])), BoolExpr::True);
    }

    #[test]
    fn test_ast_to_sat_tseitin_and_proxy() {
        let mut solver = SMT::new();

        let and_expr = BoolExpr::And(vec![BoolExpr::Var(0), BoolExpr::Var(1)]);
        let res = solver.mk_expr(&and_expr);

        if let BoolExpr::Var(proxy_id) = res {
            assert!(proxy_id > 1, "Proxy ID should be greater than the original variable IDs");

            assert_eq!(solver.sat_to_ast[proxy_id], Some(and_expr.clone()));
            assert_eq!(solver.ast_to_sat.get(&and_expr), Some(&proxy_id));
            assert_eq!(solver.clauses.len(), 2, "Two clauses should be added for the AND Tseitin transformation");
        } else {
            panic!("The conversion of a multi-variable AND did not return a Var(proxy)");
        }
    }

    #[test]
    fn test_ast_to_sat_double_negation() {
        let mut solver = SMT::new();

        let not_v1 = BoolExpr::Not(Box::new(BoolExpr::Var(0)));
        let double_not = BoolExpr::Not(Box::new(not_v1));

        let res = solver.mk_expr(&double_not);
        assert_eq!(res, BoolExpr::Var(0), "The double negation is not simplified correctly");
    }
}
