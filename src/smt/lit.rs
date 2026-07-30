use crate::smt::ast::BoolExpr;
use std::{fmt, ops};

// Compact encoding: x = var*2 + sign_bit, where sign_bit=1 means negated (MiniSat convention).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Lit {
    x: usize,
}

impl Lit {
    pub(super) fn new(var: usize, sign: bool) -> Self {
        Lit { x: var * 2 + sign as usize }
    }

    /// Variable index.
    pub(super) fn var(self) -> usize {
        self.x >> 1
    }

    /// True if this is a negated literal.
    pub(super) fn sign(self) -> bool {
        self.x & 1 != 0
    }

    /// Compact integer index suitable for watch-list indexing (MiniSat's toInt).
    pub(super) fn index(self) -> usize {
        self.x
    }
}

impl ops::Not for Lit {
    type Output = Self;

    fn not(self) -> Self {
        Lit { x: self.x ^ 1 }
    }
}

impl From<&BoolExpr> for Lit {
    fn from(expr: &BoolExpr) -> Self {
        match expr {
            BoolExpr::Var(v) => Lit::new(*v, false),
            BoolExpr::Not(inner) => {
                if let BoolExpr::Var(v) = inner.as_ref() {
                    Lit::new(*v, true)
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
        if self.var() == 0 {
            if self.sign() { write!(f, "⊥") } else { write!(f, "⊤") }
        } else if self.sign() {
            write!(f, "¬b{}", self.var())
        } else {
            write!(f, "b{}", self.var())
        }
    }
}

/// The literal that is always true.
pub(super) const TRUE_LIT: Lit = Lit { x: 0 };
/// The literal that is always false.
pub(super) const FALSE_LIT: Lit = Lit { x: 1 };
