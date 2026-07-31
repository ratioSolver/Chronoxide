pub mod ast;
mod lin;
mod lit;
mod rational;

use crate::smt::{
    ast::{ArithExpr, BoolExpr, Expr, LBool, to_cnf},
    lin::Lin,
    lit::Lit,
    rational::Rational,
};
use rug::Complete;
use std::{
    collections::{BTreeMap, HashMap, HashSet, VecDeque},
    fmt, mem,
};
use tracing::trace;

pub struct SMT {
    bools: Vec<LBool>,                                            // Current assignments of boolean variables
    clauses: Vec<Clause>,                                         // List of clauses in CNF
    watches: Vec<Vec<usize>>,                                     // Watch lists for each literal (index is 2*var + sign)
    reason: Vec<Option<usize>>,                                   // Reason for each variable's assignment
    prop_q: VecDeque<Lit>,                                        // Queue of literals to propagate
    trail: Vec<Lit>,                                              // Trail of assigned literals for backtracking
    trail_lim: Vec<usize>,                                        // Indices in the trail where decisions were made
    level: Vec<Option<usize>>,                                    // Decision level for each variable
    ints: Vec<bool>,                                              // Distinguish between integer and real variables
    reals: Vec<Rational>,                                         // Current assignments of real variables
    lbs: Vec<Rational>,                                           // Current assignments of lower bounds
    ubs: Vec<Rational>,                                           // Current assignments of upper bounds
    tableau: BTreeMap<usize, BTreeMap<usize, rug::Rational>>,     // Map from variable index to linear expressions
    sat_to_bound: Vec<Option<Bound>>,                             // Map from variable index to its bound (if any)
    bound_to_sat: HashMap<Bound, usize>,                          // Map from bound to its corresponding variable index
    lin_to_slack: HashMap<BTreeMap<usize, rug::Rational>, usize>, // Map from linear expressions to their corresponding slack variable index
}

impl Default for SMT {
    fn default() -> Self {
        Self::new()
    }
}

impl SMT {
    pub fn new() -> Self {
        SMT {
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
            tableau: BTreeMap::new(),
            sat_to_bound: Vec::new(),
            bound_to_sat: HashMap::new(),
            lin_to_slack: HashMap::new(),
        }
    }

    pub fn new_bool(&mut self) -> BoolExpr {
        let var_index = self.bools.len();
        self.bools.push(LBool::Undef);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new()); // For the negated literal
        self.reason.push(None);
        self.level.push(None);
        BoolExpr::Var(var_index)
    }

    pub fn new_int(&mut self) -> ArithExpr {
        let var_index = self.ints.len();
        self.ints.push(true);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        ArithExpr::Int(var_index)
    }

    pub fn new_real(&mut self) -> ArithExpr {
        let var_index = self.reals.len();
        self.ints.push(false);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        ArithExpr::Real(var_index)
    }

    pub fn eval(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Bool(b) => Expr::Bool(BoolExpr::Lit(self.eval_bool(b))),
            Expr::Arith(a) => {
                let (lb, val, ub) = self.eval_arith(a);
                Expr::Arith(ArithExpr::Val { lb, val, ub })
            }
        }
    }

    pub fn eval_bool(&self, expr: &BoolExpr) -> LBool {
        match expr {
            BoolExpr::Lit(l) => *l,
            BoolExpr::Var(v) => self.bools[*v],
            BoolExpr::Not(not) => !self.eval_bool(not),
            BoolExpr::And(and) => {
                let mut result = LBool::True;
                for sub_expr in and {
                    let sub_result = self.eval_bool(sub_expr);
                    match sub_result {
                        LBool::False => return LBool::False,
                        LBool::Undef => result = LBool::Undef,
                        LBool::True => {}
                    }
                }
                result
            }
            BoolExpr::Or(or) => {
                let mut result = LBool::False;
                for sub_expr in or {
                    let sub_result = self.eval_bool(sub_expr);
                    match sub_result {
                        LBool::True => return LBool::True,
                        LBool::Undef => result = LBool::Undef,
                        LBool::False => {}
                    }
                }
                result
            }
            BoolExpr::Lt(e1, e2) => {
                let (lb1, _, ub1) = self.eval_arith(e1);
                let (lb2, _, ub2) = self.eval_arith(e2);
                if ub1 < lb2 {
                    LBool::True
                } else if lb1 >= ub2 {
                    LBool::False
                } else {
                    LBool::Undef
                }
            }
            BoolExpr::Le(e1, e2) => {
                let (lb1, _, ub1) = self.eval_arith(e1);
                let (lb2, _, ub2) = self.eval_arith(e2);
                if ub1 <= lb2 {
                    LBool::True
                } else if lb1 > ub2 {
                    LBool::False
                } else {
                    LBool::Undef
                }
            }
            BoolExpr::Eq(e1, e2) => match (self.eval(e1), self.eval(e2)) {
                (Expr::Bool(a1), Expr::Bool(a2)) => match (self.eval_bool(&a1), self.eval_bool(&a2)) {
                    (LBool::True, LBool::True) => LBool::True,
                    (LBool::False, LBool::False) => LBool::True,
                    (LBool::Undef, _) | (_, LBool::Undef) => LBool::Undef,
                    _ => LBool::False,
                },
                (Expr::Arith(a1), Expr::Arith(a2)) => {
                    let (lb1, _, ub1) = self.eval_arith(&a1);
                    let (lb2, _, ub2) = self.eval_arith(&a2);
                    if ub1 < lb2 || lb1 > ub2 {
                        LBool::False
                    } else if lb1 == ub1 && lb2 == ub2 && lb1 == lb2 {
                        LBool::True
                    } else {
                        LBool::Undef
                    }
                }
                _ => LBool::False, // Different types cannot be equal
            },
            BoolExpr::Ge(e1, e2) => {
                let (lb1, _, ub1) = self.eval_arith(e1);
                let (lb2, _, ub2) = self.eval_arith(e2);
                if lb1 > ub2 {
                    LBool::True
                } else if ub1 < lb2 {
                    LBool::False
                } else {
                    LBool::Undef
                }
            }
            BoolExpr::Gt(e1, e2) => {
                let (lb1, _, ub1) = self.eval_arith(e1);
                let (lb2, _, ub2) = self.eval_arith(e2);
                if lb1 > ub2 {
                    LBool::True
                } else if ub1 <= lb2 {
                    LBool::False
                } else {
                    LBool::Undef
                }
            }
        }
    }

    pub fn eval_arith(&self, expr: &ArithExpr) -> (Rational, Rational, Rational) {
        match expr {
            ArithExpr::Lit(r) => (r.clone(), r.clone(), r.clone()),
            ArithExpr::Val { lb, val, ub } => (lb.clone(), val.clone(), ub.clone()),
            ArithExpr::Int(v) => (self.lbs[*v].clone(), self.reals[*v].clone(), self.ubs[*v].clone()),
            ArithExpr::Real(v) => (self.lbs[*v].clone(), self.reals[*v].clone(), self.ubs[*v].clone()),
            ArithExpr::Add(add) => {
                let mut lb = Rational::Finite(rug::Rational::from(0));
                let mut res = Rational::Finite(rug::Rational::from(0));
                let mut ub = Rational::Finite(rug::Rational::from(0));
                for sub_expr in add {
                    let (sub_lb, sub_res, sub_ub) = self.eval_arith(sub_expr);
                    lb += sub_lb;
                    res += sub_res;
                    ub += sub_ub;
                }
                (lb, res, ub)
            }
            ArithExpr::Sub(e1, e2) => {
                let (lb1, res1, ub1) = self.eval_arith(e1);
                let (lb2, res2, ub2) = self.eval_arith(e2);
                (lb1 - ub2, res1 - res2, ub1 - lb2)
            }
            ArithExpr::Mul(mul) => {
                let mut lb = Rational::Finite(rug::Rational::from(1));
                let mut res = Rational::Finite(rug::Rational::from(1));
                let mut ub = Rational::Finite(rug::Rational::from(1));
                for sub_expr in mul {
                    let (sub_lb, sub_res, sub_ub) = self.eval_arith(sub_expr);
                    lb *= sub_lb;
                    res *= sub_res;
                    ub *= sub_ub;
                }
                (lb, res, ub)
            }
            ArithExpr::Div(e1, e2) => {
                let (lb1, res1, ub1) = self.eval_arith(e1);
                let (lb2, res2, ub2) = self.eval_arith(e2);
                (lb1 / ub2, res1 / res2, ub1 / lb2)
            }
        }
    }

    pub fn assert(&mut self, expr: &BoolExpr) -> bool {
        match to_cnf(expr) {
            BoolExpr::Lit(l) => l == LBool::True, // If the literal is true, the assertion is satisfied
            BoolExpr::Var(v) => self.enqueue(Lit::new(v, false), None),
            BoolExpr::Not(not) => match not.as_ref() {
                BoolExpr::Var(v) => self.enqueue(Lit::new(*v, true), None),
                _ => panic!("Unsupported expression type for assertion: {}", expr),
            },
            BoolExpr::And(and) => {
                for sub_expr in and {
                    if !self.assert(&sub_expr) {
                        return false;
                    }
                }
                true
            }
            BoolExpr::Or(or) => {
                let mut lits = Vec::new();
                lits.reserve(or.len());
                for sub_expr in or {
                    match &sub_expr {
                        BoolExpr::Var(v) => lits.push(Lit::new(*v, false)),
                        BoolExpr::Not(not) => match not.as_ref() {
                            BoolExpr::Var(v) => lits.push(Lit::new(*v, true)),
                            _ => panic!("Unsupported expression type for assertion: {}", expr),
                        },
                        BoolExpr::Lt(e1, e2) | BoolExpr::Le(e1, e2) => {
                            let is_strict = matches!(sub_expr, BoolExpr::Lt(_, _));
                            let (vars, const_term) = self.canonize_inequality(e1.as_ref(), e2.as_ref());

                            match vars.len() {
                                0 => {
                                    if if is_strict { const_term.is_negative() } else { const_term.is_negative() || const_term.is_zero() } {
                                        return true;
                                    }
                                }
                                1 => {
                                    let (&var, coeff) = vars.iter().next().unwrap();

                                    let eps_val = if is_strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                                    let bound = InfRational::new(-const_term.clone() / coeff, eps_val / coeff);

                                    let bound = if coeff.is_positive() { Bound::Upper(var, bound) } else { Bound::Lower(var, bound) };
                                    lits.push(Lit::new(self.get_or_create_bound_proxy(bound), false));
                                }
                                _ => {
                                    let slack = if let Some(&slack) = self.lin_to_slack.get(&vars) {
                                        slack
                                    } else {
                                        let ArithExpr::Real(slack) = self.new_real() else { unreachable!() };
                                        self.tableau.insert(slack, vars.clone());
                                        self.lin_to_slack.insert(vars, slack);
                                        slack
                                    };

                                    let eps_val = if is_strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                                    let bound = Bound::Upper(slack, InfRational::new(-const_term, eps_val));

                                    lits.push(Lit::new(self.get_or_create_bound_proxy(bound), false));
                                }
                            }
                        }
                        _ => panic!("Unsupported expression type for assertion: {}", expr),
                    }
                }
                self.add_clause(lits).is_ok()
            }
            _ => panic!("Unsupported expression type for assertion: {}", expr),
        }
    }

    fn canonize_inequality(&self, e1: &ArithExpr, e2: &ArithExpr) -> (BTreeMap<usize, rug::Rational>, rug::Rational) {
        let diff = Lin::from(e1) - Lin::from(e2);
        let mut vars = BTreeMap::new();

        for (&var, coeff) in &diff.vars {
            if let Some(basic) = self.tableau.get(&var) {
                for (&sub_var, sub_coeff) in basic {
                    *vars.entry(sub_var).or_insert_with(|| rug::Rational::from(0)) += (coeff * sub_coeff).complete();
                }
            } else {
                *vars.entry(var).or_insert_with(|| rug::Rational::from(0)) += coeff.clone();
            }
        }

        vars.retain(|_, c| *c != 0);
        (vars, diff.const_term)
    }

    fn get_or_create_bound_proxy(&mut self, bound: Bound) -> usize {
        if let Some(&sat_var) = self.bound_to_sat.get(&bound) {
            return sat_var;
        }

        let BoolExpr::Var(sat_var) = self.new_bool() else { unreachable!() };

        if sat_var >= self.sat_to_bound.len() {
            self.sat_to_bound.resize(sat_var + 1, None);
        }

        self.sat_to_bound[sat_var] = Some(bound.clone());
        self.bound_to_sat.insert(bound, sat_var);

        sat_var
    }

    pub fn decide(&mut self, expr: &BoolExpr) -> Result<(), BoolExpr> {
        match expr {
            BoolExpr::Var(v) => self.decide_lit(Lit::new(*v, false)),
            BoolExpr::Not(not) => match not.as_ref() {
                BoolExpr::Var(v) => self.decide_lit(Lit::new(*v, true)),
                _ => panic!("Unsupported expression type for decision: {}", expr),
            },
            _ => panic!("Unsupported expression type for decision: {}", expr),
        }
    }

    fn decide_lit(&mut self, lit: Lit) -> Result<(), BoolExpr> {
        self.trail_lim.push(self.trail.len());
        self.enqueue(lit, None);
        self.propagate()
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
            clause.lits.sort_by_key(|l| self.bools.get(l.var()).copied().unwrap_or(LBool::Undef) != LBool::Undef);
            for lit in &clause.lits[0..2] {
                self.watches[lit.index()].push(clause_index);
            }
            if self.lit_value(&clause.lits[0]) == LBool::Undef && self.lit_value(&clause.lits[1]) == LBool::False && !self.enqueue(clause.lits[0], Some(clause_index)) {
                return Err(clause.lits);
            }
            self.clauses.push(clause);
        }

        Ok(())
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        trace!("Enqueue {}{}", lit, reason.map_or("".to_string(), |r| format!(" (reason: {})", r)));
        match self.lit_value(&lit) {
            LBool::Undef => {
                self.bools[lit.var()] = if lit.sign() { LBool::False } else { LBool::True };
                self.level[lit.var()] = Some(self.decision_level());
                self.reason[lit.var()] = reason;
                self.trail.push(lit);
                self.prop_q.push_back(lit);
                true
            }
            LBool::True => true,
            LBool::False => false,
        }
    }

    pub fn propagate(&mut self) -> Result<(), BoolExpr> {
        while let Some(lit) = self.prop_q.pop_front() {
            let falsified = !lit;
            let falsified_index = falsified.index();
            let watches = mem::take(&mut self.watches[falsified_index]);
            for i in 0..watches.len() {
                let mut clause_idx = watches[i];
                // Keep the first watched literal as the other watcher and the second as the falsified one.
                if self.clauses[clause_idx].lits[0] == falsified {
                    self.clauses[clause_idx].lits.swap(0, 1);
                }

                // Check if clause is already satisfied
                if self.lit_value(&self.clauses[clause_idx].lits[0]) == LBool::True {
                    self.watches[lit.index()].push(clause_idx);
                    continue;
                }

                // Find a replacement watcher that is not currently false.
                let mut found_replacement = false;
                for j in 2..self.clauses[clause_idx].lits.len() {
                    let next_lit = self.clauses[clause_idx].lits[j];
                    if self.lit_value(&next_lit) != LBool::False {
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

                    self.cancel_until(backtrack_level);
                    return Err(conflict_to_bool_expr(learnt));
                }
            }
        }
        Ok(())
    }

    fn undo_one(&mut self) {
        if let Some(lit) = self.trail.pop() {
            trace!("Undoing assignment of {}", lit);
            self.bools[lit.var()] = LBool::Undef;
            self.reason[lit.var()] = None;
            self.level[lit.var()] = None;
        }
    }

    fn lit_value(&self, lit: &Lit) -> LBool {
        if lit.sign() { !self.bools[lit.var()] } else { self.bools[lit.var()] }
    }

    fn level(&self, var: usize) -> Option<usize> {
        self.level[var]
    }

    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
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

fn lit_to_bool_expr(lit: Lit) -> BoolExpr {
    let var = BoolExpr::Var(lit.var());
    if lit.sign() { BoolExpr::Not(Box::new(var)) } else { var }
}

fn conflict_to_bool_expr(conflict: Vec<Lit>) -> BoolExpr {
    let mut terms = conflict.into_iter().map(lit_to_bool_expr);

    match (terms.next(), terms.next()) {
        (None, _) => BoolExpr::Lit(LBool::False),
        (Some(term), None) => term,
        (Some(first), Some(second)) => {
            let mut disj = vec![first, second];
            disj.extend(terms);
            BoolExpr::Or(disj)
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct InfRational {
    rat: rug::Rational,
    inf: rug::Rational,
}

impl InfRational {
    fn new(rat: rug::Rational, inf: rug::Rational) -> Self {
        InfRational { rat, inf }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Bound {
    Lower(usize, InfRational),
    Upper(usize, InfRational),
}

#[cfg(test)]
mod tests {
    use tracing::{Level, subscriber};

    use super::*;

    // --- Helpers ---

    fn var(v: usize) -> BoolExpr {
        BoolExpr::Var(v)
    }
    fn not(e: BoolExpr) -> BoolExpr {
        BoolExpr::Not(Box::new(e))
    }
    fn and(es: impl IntoIterator<Item = BoolExpr>) -> BoolExpr {
        BoolExpr::And(es.into_iter().collect())
    }
    fn or(es: impl IntoIterator<Item = BoolExpr>) -> BoolExpr {
        BoolExpr::Or(es.into_iter().collect())
    }
    fn lit_true() -> BoolExpr {
        BoolExpr::Lit(LBool::True)
    }
    fn lit_false() -> BoolExpr {
        BoolExpr::Lit(LBool::False)
    }
    fn aint(n: usize) -> Box<ArithExpr> {
        Box::new(ArithExpr::Int(n))
    }
    fn alit(n: i32) -> Box<ArithExpr> {
        Box::new(ArithExpr::Lit(Rational::Finite(rug::Rational::from(n))))
    }

    #[test]
    fn test_smt_creation() {
        let mut smt = SMT::new();
        smt.new_bool();
        smt.new_bool();
        smt.new_int();
        smt.new_real();
        assert_eq!(smt.bools.len(), 2);
        assert_eq!(smt.ints.len(), 2);
        assert_eq!(smt.reals.len(), 2);
    }

    #[test]
    fn test_eval_bool() {
        let mut smt = SMT::new();
        let b1 = smt.new_bool();
        let b2 = smt.new_bool();
        smt.assert(&b1);
        smt.assert(&not(b2.clone()));
        assert_eq!(smt.eval_bool(&b1), LBool::True);
        assert_eq!(smt.eval_bool(&b2), LBool::False);
    }

    #[test]
    fn test_add_clause() {
        let mut smt = SMT::new();
        let b1 = smt.new_bool();
        let b2 = smt.new_bool();
        let clause = or([b1.clone(), b2.clone()]);
        smt.assert(&clause);
        assert_eq!(smt.clauses.len(), 1);
    }

    #[test]
    fn test_propagate() {
        let mut smt = SMT::new();
        let b1 = smt.new_bool();
        let b2 = smt.new_bool();
        smt.assert(&or([b1.clone(), b2.clone()]));
        let decision_result = smt.decide(&not(b1.clone()));
        assert!(decision_result.is_ok());
        assert_eq!(smt.eval_bool(&b1), LBool::False);
        assert_eq!(smt.eval_bool(&b2), LBool::True);
    }

    #[test]
    fn test_conflict_analysis() {
        let subscriber = tracing_subscriber::fmt().with_max_level(Level::TRACE).finish();
        subscriber::set_global_default(subscriber).expect("Failed to set global default subscriber");

        let mut smt = SMT::new();
        let b1 = smt.new_bool();
        let b2 = smt.new_bool();
        let b3 = smt.new_bool();
        let b4 = smt.new_bool();
        let b5 = smt.new_bool();
        let b6 = smt.new_bool();
        let b7 = smt.new_bool();
        let b8 = smt.new_bool();
        let b9 = smt.new_bool();

        // [(b1 ∨ b2) ∧ (b1 ∨ b3 ∨ b7) ∧ (¬b2 ∨ ¬b3 ∨ b4) ∧ (¬b4 ∨ b5 ∨ b8) ∧ (¬b4 ∨ b6 ∨ b9) ∧ (¬b5 ∨ ¬b6)]
        smt.assert(&and([or([b1.clone(), b2.clone()]), or([b1.clone(), b3.clone(), b7.clone()]), or([not(b2.clone()), not(b3.clone()), b4.clone()]), or([not(b4.clone()), b5.clone(), b8.clone()]), or([not(b4.clone()), b6.clone(), b9.clone()]), or([not(b5.clone()), not(b6.clone())])]));

        // Decision: ¬b7
        let decision_result = smt.decide(&not(b7.clone()));
        assert!(decision_result.is_ok());

        // Decision: ¬b8
        let decision_result = smt.decide(&not(b8.clone()));
        assert!(decision_result.is_ok());

        // Decision: ¬b9
        let decision_result = smt.decide(&not(b9.clone()));
        assert!(decision_result.is_ok());

        // Decision: ¬b1
        let decision_result = smt.decide(&not(b1.clone()));
        assert!(decision_result.is_err());
        let conflict_expr = decision_result.err().unwrap();
        smt.assert(&conflict_expr);
        let prop_result = smt.propagate();
        assert!(prop_result.is_ok());
    }
}
