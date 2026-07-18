use std::fmt;

use crate::semitone::ast::Bool;

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

    pub fn add_var(&mut self) -> usize {
        let var_index = self.assigns.len();
        self.assigns.push(LBool::Undef);
        var_index
    }

    pub fn assign(&mut self, expr: &dyn Bool) {
        if let Some(var) = expr.as_var() {
            self.assigns[**var] = LBool::True; // Assign the variable to true
        }
    }
}
