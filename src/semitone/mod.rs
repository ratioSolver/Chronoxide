pub mod ast;
pub mod values;

use crate::semitone::{
    ast::{Bool, BoolExpr, Int, Real},
    values::{LBool, Rational},
};

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

    pub fn add_var(&mut self) -> Bool {
        let var_index = self.bools.len();
        self.bools.push(LBool::Undef);
        Bool::new(var_index)
    }

    pub fn add_int_var(&mut self) -> Int {
        let var_index = self.ints.len();
        self.ints.push(true);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        Int::new(var_index)
    }

    pub fn add_real_var(&mut self) -> Real {
        let var_index = self.reals.len();
        self.ints.push(false);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        Real::new(var_index)
    }

    pub fn assert(&mut self, expr: &dyn BoolExpr, propagate: bool) {
        if let Some(_var) = expr.as_var() {
            self.enqueue(expr); // Assign the variable to true
        } else if let Some(not) = expr.as_not()
            && let Some(_var) = not.as_var()
        {
            self.enqueue(expr); // Assign the negated variable to false
        } else {
            unimplemented!("Assertion for complex expressions is not implemented yet: {}", expr);
        }
    }

    fn enqueue(&mut self, expr: &dyn BoolExpr) {
        if let Some(var) = expr.as_var() {
            self.bools[**var] = LBool::True; // Enqueue the variable to true
        } else if let Some(not) = expr.as_not() {
            if let Some(var) = not.as_var() {
                self.bools[**var] = LBool::False; // Enqueue the negated variable to false
            }
        } else {
            panic!("Unsupported expression type for enqueueing: {}", expr);
        }
    }
}
