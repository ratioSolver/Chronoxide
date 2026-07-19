pub mod ast;
mod lin;
mod lit;
mod rational;

use crate::smt::{
    ast::{ArithExpr, BoolExpr, Expr, LBool},
    lin::Lin,
    lit::Lit,
    rational::Rational,
};
use std::{
    collections::{BTreeMap, VecDeque},
    fmt,
};
use tracing::trace;

pub struct SMT {
    bools: Vec<LBool>,             // Current assignments of boolean variables
    clauses: Vec<Clause>,          // List of clauses in CNF
    reason: Vec<Option<usize>>,    // Reason for each variable's assignment
    prop_q: VecDeque<Lit>,         // Queue of literals to propagate
    ints: Vec<bool>,               // Distinguish between integer and real variables
    reals: Vec<Rational>,          // Current assignments of real variables
    lbs: Vec<Rational>,            // Current assignments of lower bounds
    ubs: Vec<Rational>,            // Current assignments of upper bounds
    tableau: BTreeMap<usize, Lin>, // Map from variable index to linear expressions
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
            reason: Vec::new(),
            prop_q: VecDeque::new(),
            ints: Vec::new(),
            reals: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            tableau: BTreeMap::new(),
        }
    }

    pub fn new_bool(&mut self) -> BoolExpr {
        let var_index = self.bools.len();
        self.bools.push(LBool::Undef);
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
            BoolExpr::Lit(l) => l.clone(),
            BoolExpr::Var(v) => self.bools[*v].clone(),
            BoolExpr::Not(not) => match self.eval_bool(not) {
                LBool::True => LBool::False,
                LBool::False => LBool::True,
                LBool::Undef => LBool::Undef,
            },
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

    pub fn assert(&mut self, expr: &BoolExpr, propagate: bool) -> bool {
        match expr {
            BoolExpr::Var(_v) => self.enqueue(Lit::from(expr), None),
            BoolExpr::Not(not) => match not.as_ref() {
                BoolExpr::Var(_v) => self.enqueue(Lit::from(expr), None),
                _ => unimplemented!("Assertion for complex expressions is not implemented yet: {}", expr),
            },
            _ => unimplemented!("Assertion for complex expressions is not implemented yet: {}", expr),
        }
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        trace!("Enqueue {}{}", lit, reason.map_or("".to_string(), |r| format!(" (reason: {})", r)));
        match self.bools.get(lit.x) {
            Some(LBool::Undef) => {
                self.bools[lit.x] = if lit.sign { LBool::True } else { LBool::False };
                self.reason[lit.x] = reason;
                self.prop_q.push_back(lit);
                true
            }
            Some(LBool::True) if !lit.sign => false,
            Some(LBool::False) if lit.sign => false,
            _ => true, // Already assigned to the same value
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
