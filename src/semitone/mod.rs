use crate::semitone::ast::{Bool, BoolExpr, Int, Real};
use std::fmt;

pub mod ast;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
#[repr(u8)]
pub enum LBool {
    /// The variable is assigned to true.
    True,
    /// The variable is assigned to false.
    False,
    /// The variable is currently unassigned.
    #[default]
    Undef,
}

impl fmt::Display for LBool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LBool::True => write!(f, "true"),
            LBool::False => write!(f, "false"),
            LBool::Undef => write!(f, "undef"),
        }
    }
}

pub struct SeMiTONE {
    bools: Vec<LBool>, // Current assignments of variables
}

impl Default for SeMiTONE {
    fn default() -> Self {
        Self::new()
    }
}

impl SeMiTONE {
    pub fn new() -> Self {
        SeMiTONE { bools: Vec::new() }
    }

    pub fn add_var(&mut self) -> Bool {
        let var_index = self.bools.len();
        self.bools.push(LBool::Undef);
        Bool::new(var_index)
    }

    pub fn add_int_var(&mut self) -> Int {
        let var_index = self.bools.len();
        self.bools.push(LBool::Undef);
        Int::new(var_index)
    }

    pub fn add_real_var(&mut self) -> Real {
        let var_index = self.bools.len();
        self.bools.push(LBool::Undef);
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
