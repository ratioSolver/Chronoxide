use crate::smt::ast::BoolExpr;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Lit {
    pub(super) x: usize,   // Variable index
    pub(super) sign: bool, // true for positive literal, false for negated literal
}

impl From<&BoolExpr> for Lit {
    fn from(expr: &BoolExpr) -> Self {
        match expr {
            BoolExpr::Var(v) => Lit { x: *v, sign: true },
            BoolExpr::Not(not) => {
                if let BoolExpr::Var(v) = not.as_ref() {
                    Lit { x: *v, sign: false }
                } else {
                    panic!("Unsupported expression type for conversion to literal: {}", expr);
                }
            }
            _ => panic!("Unsupported expression type for conversion to literal: {}", expr),
        }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.x == 0 {
            match self.sign {
                true => write!(f, "⊤"),  // True literal
                false => write!(f, "⊥"), // False literal
            }
        } else {
            match self.sign {
                true => write!(f, "{}", self.x),
                false => write!(f, "¬{}", self.x),
            }
        }
    }
}

/// The literal that is always true.
pub(super) const TRUE_LIT: Lit = Lit { x: 0, sign: true };
/// The literal that is always false.
pub(super) const FALSE_LIT: Lit = Lit { x: 0, sign: false };
