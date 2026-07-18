pub mod ast;

use crate::smt::ast::{ArithExpr, BoolExpr, Expr, LBool, Rational};
use std::collections::BTreeMap;

pub struct SMT {
    bools: Vec<LBool>,             // Current assignments of boolean variables
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
            Expr::Arith(a) => Expr::Arith(ArithExpr::Lit(self.eval_arith(a))),
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
                if self.eval_arith(e1) < self.eval_arith(e2) {
                    LBool::True
                } else {
                    LBool::False
                }
            }
            BoolExpr::Le(e1, e2) => {
                if self.eval_arith(e1) <= self.eval_arith(e2) {
                    LBool::True
                } else {
                    LBool::False
                }
            }
            BoolExpr::Eq(e1, e2) => match (self.eval(e1), self.eval(e2)) {
                (Expr::Bool(a1), Expr::Bool(a2)) => {
                    if self.eval_bool(&a1) == self.eval_bool(&a2) {
                        LBool::True
                    } else {
                        LBool::False
                    }
                }
                (Expr::Arith(a1), Expr::Arith(a2)) => {
                    if self.eval_arith(&a1) == self.eval_arith(&a2) {
                        LBool::True
                    } else {
                        LBool::False
                    }
                }
                _ => LBool::False, // Different types cannot be equal
            },
            BoolExpr::Ge(e1, e2) => {
                if self.eval_arith(e1) >= self.eval_arith(e2) {
                    LBool::True
                } else {
                    LBool::False
                }
            }
            BoolExpr::Gt(e1, e2) => {
                if self.eval_arith(e1) > self.eval_arith(e2) {
                    LBool::True
                } else {
                    LBool::False
                }
            }
        }
    }

    pub fn eval_arith(&self, expr: &ArithExpr) -> Rational {
        match expr {
            ArithExpr::Lit(r) => r.clone(),
            ArithExpr::Int(v) => self.reals[*v].clone(),
            ArithExpr::Real(v) => self.reals[*v].clone(),
            ArithExpr::Add(add) => {
                let mut sum = Rational::Finite(rug::Rational::from(0));
                for sub_expr in add {
                    sum += self.eval_arith(sub_expr);
                }
                sum
            }
            ArithExpr::Sub(e1, e2) => self.eval_arith(e1) - self.eval_arith(e2),
            ArithExpr::Mul(mul) => {
                let mut product = Rational::Finite(rug::Rational::from(1));
                for sub_expr in mul {
                    product *= self.eval_arith(sub_expr);
                }
                product
            }
            ArithExpr::Div(e1, e2) => self.eval_arith(e1) / self.eval_arith(e2),
        }
    }

    pub fn assert(&mut self, expr: &BoolExpr, propagate: bool) {
        match expr {
            BoolExpr::Var(_v) => self.enqueue(expr),
            BoolExpr::Not(not) => match not.as_ref() {
                BoolExpr::Var(_v) => self.enqueue(expr),
                _ => unimplemented!("Assertion for complex expressions is not implemented yet: {}", expr),
            },
            _ => unimplemented!("Assertion for complex expressions is not implemented yet: {}", expr),
        }
    }

    fn enqueue(&mut self, expr: &BoolExpr) {
        match expr {
            BoolExpr::Var(v) => self.bools[*v] = LBool::True, // Enqueue the variable to true
            BoolExpr::Not(not) => {
                if let BoolExpr::Var(v) = not.as_ref() {
                    self.bools[*v] = LBool::False; // Enqueue the negated variable to false
                } else {
                    panic!("Unsupported expression type for enqueueing: {}", expr);
                }
            }
            _ => panic!("Unsupported expression type for enqueueing: {}", expr),
        }
    }
}

struct Lin {
    vars: BTreeMap<usize, rug::Rational>, // Map from variable index to coefficient
    const_term: rug::Rational,            // Constant term in the linear expression
}
