use std::{fmt, ops};

#[derive(Clone, Debug, PartialEq, PartialOrd, Ord, Eq)]
pub enum Rational {
    NegativeInf,
    Finite(rug::Rational),
    PositiveInf,
}

impl Default for Rational {
    fn default() -> Self {
        Rational::Finite(rug::Rational::from(0))
    }
}

impl ops::Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Rational::NegativeInf => Rational::PositiveInf,
            Rational::Finite(r) => Rational::Finite(-r),
            Rational::PositiveInf => Rational::NegativeInf,
        }
    }
}

impl ops::Add for Rational {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (Rational::NegativeInf, Rational::PositiveInf) | (Rational::PositiveInf, Rational::NegativeInf) => {
                panic!("undefined operation: -inf + +inf")
            }
            (Rational::NegativeInf, _) | (_, Rational::NegativeInf) => Rational::NegativeInf,
            (Rational::PositiveInf, _) | (_, Rational::PositiveInf) => Rational::PositiveInf,
            (Rational::Finite(r1), Rational::Finite(r2)) => Rational::Finite(r1 + r2),
        }
    }
}

impl ops::AddAssign for Rational {
    fn add_assign(&mut self, other: Self) {
        *self = std::mem::take(self) + other;
    }
}

impl ops::Sub for Rational {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self + (-other)
    }
}

impl ops::Mul for Rational {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        match (self, other) {
            (Rational::NegativeInf, Rational::Finite(r)) | (Rational::Finite(r), Rational::NegativeInf) => {
                if r > rug::Rational::from(0) {
                    Rational::NegativeInf
                } else if r < rug::Rational::from(0) {
                    Rational::PositiveInf
                } else {
                    panic!("undefined operation: -inf * 0")
                }
            }
            (Rational::PositiveInf, Rational::Finite(r)) | (Rational::Finite(r), Rational::PositiveInf) => {
                if r > rug::Rational::from(0) {
                    Rational::PositiveInf
                } else if r < rug::Rational::from(0) {
                    Rational::NegativeInf
                } else {
                    panic!("undefined operation: +inf * 0")
                }
            }
            (Rational::NegativeInf, Rational::NegativeInf) | (Rational::PositiveInf, Rational::PositiveInf) => Rational::PositiveInf,
            (Rational::NegativeInf, Rational::PositiveInf) | (Rational::PositiveInf, Rational::NegativeInf) => Rational::NegativeInf,
            (Rational::Finite(r1), Rational::Finite(r2)) => Rational::Finite(r1 * r2),
        }
    }
}

impl ops::MulAssign for Rational {
    fn mul_assign(&mut self, other: Self) {
        *self = std::mem::take(self) * other;
    }
}

impl ops::Div for Rational {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        match (self, other) {
            (Rational::NegativeInf, Rational::Finite(r)) => {
                if r > rug::Rational::from(0) {
                    Rational::NegativeInf
                } else if r < rug::Rational::from(0) {
                    Rational::PositiveInf
                } else {
                    panic!("undefined operation: -inf / 0")
                }
            }
            (Rational::PositiveInf, Rational::Finite(r)) => {
                if r > rug::Rational::from(0) {
                    Rational::PositiveInf
                } else if r < rug::Rational::from(0) {
                    Rational::NegativeInf
                } else {
                    panic!("undefined operation: +inf / 0")
                }
            }
            (Rational::Finite(_), Rational::NegativeInf) | (Rational::Finite(_), Rational::PositiveInf) => Rational::Finite(rug::Rational::from(0)),
            (Rational::NegativeInf, Rational::NegativeInf) | (Rational::PositiveInf, Rational::PositiveInf) | (Rational::NegativeInf, Rational::PositiveInf) | (Rational::PositiveInf, Rational::NegativeInf) => panic!("undefined operation: ±inf / ±inf"),
            (Rational::Finite(r1), Rational::Finite(r2)) => {
                if r2 == rug::Rational::from(0) {
                    if r1 > rug::Rational::from(0) {
                        Rational::PositiveInf
                    } else if r1 < rug::Rational::from(0) {
                        Rational::NegativeInf
                    } else {
                        panic!("undefined operation: 0 / 0")
                    }
                } else {
                    Rational::Finite(r1 / r2)
                }
            }
        }
    }
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
