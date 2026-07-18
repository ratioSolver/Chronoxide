pub mod ast;

use crate::semitone::ast::{ArithExpr, BoolExpr, LBool, Rational};

pub struct SeMiTONE {
    bools: Vec<LBool>,    // Current assignments of boolean variables
    ints: Vec<bool>,      // Distinguish between integer and real variables
    reals: Vec<Rational>, // Current assignments of real variables
    lbs: Vec<Rational>,   // Current assignments of lower bounds
    ubs: Vec<Rational>,   // Current assignments of upper bounds
}

impl Default for SeMiTONE {
    fn default() -> Self {
        Self::new()
    }
}

impl SeMiTONE {
    pub fn new() -> Self {
        SeMiTONE { bools: Vec::new(), ints: Vec::new(), reals: Vec::new(), lbs: Vec::new(), ubs: Vec::new() }
    }

    pub fn add_var(&mut self) -> BoolExpr {
        let var_index = self.bools.len();
        self.bools.push(LBool::Undef);
        BoolExpr::Var(var_index)
    }

    pub fn add_int_var(&mut self) -> ArithExpr {
        let var_index = self.ints.len();
        self.ints.push(true);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        ArithExpr::Int(var_index)
    }

    pub fn add_real_var(&mut self) -> ArithExpr {
        let var_index = self.reals.len();
        self.ints.push(false);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        ArithExpr::Real(var_index)
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
