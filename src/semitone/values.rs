use std::fmt;

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rational {
    NegativeInf,
    Finite(rug::Rational),
    PositiveInf,
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rational::NegativeInf => write!(f, "-inf"),
            Rational::Finite(r) => write!(f, "{}", r),
            Rational::PositiveInf => write!(f, "+inf"),
        }
    }
}
