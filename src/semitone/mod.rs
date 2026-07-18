use std::fmt;

use crate::semitone::ast::{Bool, BoolVar};

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
    assigns: Vec<LBool>, // Current assignments of variables
}

impl Default for SeMiTONE {
    fn default() -> Self {
        Self::new()
    }
}

impl SeMiTONE {
    pub fn new() -> Self {
        SeMiTONE { assigns: Vec::new() }
    }

    pub fn add_var(&mut self) -> BoolVar {
        let var_index = self.assigns.len();
        self.assigns.push(LBool::Undef);
        BoolVar::new(var_index)
    }

    pub fn assert(&mut self, expr: &dyn Bool, propagate: bool) {
        if let Some(_var) = expr.as_var() {
            self.enqueue(expr); // Assign the variable to true
        } else if let Some(not) = expr.as_not()
            && let Some(_var) = not.as_var()
        {
            self.enqueue(expr); // Assign the negated variable to false
        } else {
            panic!("Unsupported expression type for assignment: {}", expr);
        }
    }

    fn enqueue(&mut self, expr: &dyn Bool) {
        if let Some(var) = expr.as_var() {
            self.assigns[**var] = LBool::True; // Enqueue the variable to true
        } else if let Some(not) = expr.as_not() {
            if let Some(var) = not.as_var() {
                self.assigns[**var] = LBool::False; // Enqueue the negated variable to false
            }
        } else {
            panic!("Unsupported expression type for enqueueing: {}", expr);
        }
    }
}
