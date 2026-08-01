use std::{fmt, ops};

#[derive(Clone, Debug, PartialEq, PartialOrd, Ord, Eq, Hash)]
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
                if r.is_positive() {
                    Rational::NegativeInf
                } else if r.is_negative() {
                    Rational::PositiveInf
                } else {
                    panic!("undefined operation: -inf * 0")
                }
            }
            (Rational::PositiveInf, Rational::Finite(r)) | (Rational::Finite(r), Rational::PositiveInf) => {
                if r.is_positive() {
                    Rational::PositiveInf
                } else if r.is_negative() {
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
                if r.is_positive() {
                    Rational::NegativeInf
                } else if r.is_negative() {
                    Rational::PositiveInf
                } else {
                    panic!("undefined operation: -inf / 0")
                }
            }
            (Rational::PositiveInf, Rational::Finite(r)) => {
                if r.is_positive() {
                    Rational::PositiveInf
                } else if r.is_negative() {
                    Rational::NegativeInf
                } else {
                    panic!("undefined operation: +inf / 0")
                }
            }
            (Rational::Finite(_), Rational::NegativeInf) | (Rational::Finite(_), Rational::PositiveInf) => Rational::Finite(rug::Rational::from(0)),
            (Rational::NegativeInf, Rational::NegativeInf) | (Rational::PositiveInf, Rational::PositiveInf) | (Rational::NegativeInf, Rational::PositiveInf) | (Rational::PositiveInf, Rational::NegativeInf) => panic!("undefined operation: ±inf / ±inf"),
            (Rational::Finite(r1), Rational::Finite(r2)) => {
                if r2.is_zero() {
                    if r1.is_positive() {
                        Rational::PositiveInf
                    } else if r1.is_negative() {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InfRational {
    rat: rug::Rational,
    inf: rug::Rational,
}

impl InfRational {
    pub fn new(rat: rug::Rational, inf: rug::Rational) -> Self {
        InfRational { rat, inf }
    }
}

impl fmt::Display for InfRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.inf.is_zero() {
            write!(f, "{}", self.rat)
        } else if self.inf.is_positive() {
            write!(f, "{} + {}ϵ", self.rat, self.inf)
        } else {
            write!(f, "{} - {}ϵ", self.rat, -self.inf.clone())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fin(n: i32, d: i32) -> Rational {
        Rational::Finite(rug::Rational::from((n, d)))
    }

    fn int(n: i32) -> Rational {
        Rational::Finite(rug::Rational::from(n))
    }

    // --- Default ---

    #[test]
    fn default_is_zero() {
        assert_eq!(Rational::default(), int(0));
    }

    // --- Display ---

    #[test]
    fn display_neg_inf() {
        assert_eq!(Rational::NegativeInf.to_string(), "-inf");
    }

    #[test]
    fn display_pos_inf() {
        assert_eq!(Rational::PositiveInf.to_string(), "+inf");
    }

    #[test]
    fn display_finite() {
        assert_eq!(int(3).to_string(), "3");
        assert_eq!(fin(1, 2).to_string(), "1/2");
    }

    // --- Ordering ---

    #[test]
    fn ordering_neg_inf_lt_finite_lt_pos_inf() {
        assert!(Rational::NegativeInf < int(0));
        assert!(int(0) < Rational::PositiveInf);
        assert!(Rational::NegativeInf < Rational::PositiveInf);
    }

    #[test]
    fn ordering_finite_values() {
        assert!(int(-1) < int(0));
        assert!(int(0) < int(1));
        assert!(fin(1, 3) < fin(1, 2));
    }

    #[test]
    fn ordering_equal() {
        assert_eq!(int(2), int(2));
        assert_eq!(fin(2, 4), fin(1, 2));
        assert_eq!(Rational::NegativeInf, Rational::NegativeInf);
        assert_eq!(Rational::PositiveInf, Rational::PositiveInf);
    }

    // --- Neg ---

    #[test]
    fn neg_neg_inf_is_pos_inf() {
        assert_eq!(-Rational::NegativeInf, Rational::PositiveInf);
    }

    #[test]
    fn neg_pos_inf_is_neg_inf() {
        assert_eq!(-Rational::PositiveInf, Rational::NegativeInf);
    }

    #[test]
    fn neg_finite() {
        assert_eq!(-int(3), int(-3));
        assert_eq!(-fin(1, 2), fin(-1, 2));
        assert_eq!(-int(0), int(0));
    }

    // --- Add ---

    #[test]
    fn add_finite_finite() {
        assert_eq!(int(2) + int(3), int(5));
        assert_eq!(fin(1, 2) + fin(1, 2), int(1));
        assert_eq!(int(-1) + int(1), int(0));
    }

    #[test]
    fn add_inf_absorbs() {
        assert_eq!(Rational::NegativeInf + int(999), Rational::NegativeInf);
        assert_eq!(int(999) + Rational::NegativeInf, Rational::NegativeInf);
        assert_eq!(Rational::PositiveInf + int(-999), Rational::PositiveInf);
        assert_eq!(int(-999) + Rational::PositiveInf, Rational::PositiveInf);
    }

    #[test]
    fn add_same_inf() {
        assert_eq!(Rational::NegativeInf + Rational::NegativeInf, Rational::NegativeInf);
        assert_eq!(Rational::PositiveInf + Rational::PositiveInf, Rational::PositiveInf);
    }

    #[test]
    #[should_panic(expected = "-inf + +inf")]
    fn add_neg_inf_pos_inf_panics() {
        let _ = Rational::NegativeInf + Rational::PositiveInf;
    }

    #[test]
    #[should_panic(expected = "-inf + +inf")]
    fn add_pos_inf_neg_inf_panics() {
        let _ = Rational::PositiveInf + Rational::NegativeInf;
    }

    // --- AddAssign ---

    #[test]
    fn add_assign_finite() {
        let mut a = int(1);
        a += int(2);
        assert_eq!(a, int(3));
    }

    #[test]
    fn add_assign_inf() {
        let mut a = int(5);
        a += Rational::PositiveInf;
        assert_eq!(a, Rational::PositiveInf);
    }

    // --- Sub ---

    #[test]
    fn sub_finite() {
        assert_eq!(int(5) - int(3), int(2));
        assert_eq!(int(0) - int(1), int(-1));
    }

    #[test]
    fn sub_inf() {
        assert_eq!(Rational::PositiveInf - int(100), Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf - int(100), Rational::NegativeInf);
        assert_eq!(int(0) - Rational::PositiveInf, Rational::NegativeInf);
        assert_eq!(int(0) - Rational::NegativeInf, Rational::PositiveInf);
    }

    // --- Mul ---

    #[test]
    fn mul_finite_finite() {
        assert_eq!(int(3) * int(4), int(12));
        assert_eq!(fin(1, 2) * int(2), int(1));
        assert_eq!(int(-2) * int(3), int(-6));
    }

    #[test]
    fn mul_inf_positive_finite() {
        assert_eq!(Rational::PositiveInf * int(5), Rational::PositiveInf);
        assert_eq!(int(5) * Rational::PositiveInf, Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf * int(5), Rational::NegativeInf);
        assert_eq!(int(5) * Rational::NegativeInf, Rational::NegativeInf);
    }

    #[test]
    fn mul_inf_negative_finite() {
        assert_eq!(Rational::PositiveInf * int(-5), Rational::NegativeInf);
        assert_eq!(int(-5) * Rational::PositiveInf, Rational::NegativeInf);
        assert_eq!(Rational::NegativeInf * int(-5), Rational::PositiveInf);
        assert_eq!(int(-5) * Rational::NegativeInf, Rational::PositiveInf);
    }

    #[test]
    fn mul_inf_inf() {
        assert_eq!(Rational::PositiveInf * Rational::PositiveInf, Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf * Rational::NegativeInf, Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf * Rational::PositiveInf, Rational::NegativeInf);
        assert_eq!(Rational::PositiveInf * Rational::NegativeInf, Rational::NegativeInf);
    }

    #[test]
    #[should_panic(expected = "+inf * 0")]
    fn mul_pos_inf_zero_panics() {
        let _ = Rational::PositiveInf * int(0);
    }

    #[test]
    #[should_panic(expected = "-inf * 0")]
    fn mul_neg_inf_zero_panics() {
        let _ = Rational::NegativeInf * int(0);
    }

    // --- MulAssign ---

    #[test]
    fn mul_assign_finite() {
        let mut a = int(3);
        a *= int(4);
        assert_eq!(a, int(12));
    }

    #[test]
    fn mul_assign_inf() {
        let mut a = Rational::PositiveInf;
        a *= int(2);
        assert_eq!(a, Rational::PositiveInf);
    }

    // --- Div ---

    #[test]
    fn div_finite_finite() {
        assert_eq!(int(6) / int(3), int(2));
        assert_eq!(int(1) / int(2), fin(1, 2));
        assert_eq!(int(-6) / int(2), int(-3));
    }

    #[test]
    fn div_finite_inf_is_zero() {
        assert_eq!(int(5) / Rational::PositiveInf, int(0));
        assert_eq!(int(-5) / Rational::NegativeInf, int(0));
        assert_eq!(int(0) / Rational::PositiveInf, int(0));
    }

    #[test]
    fn div_inf_by_positive_finite() {
        assert_eq!(Rational::PositiveInf / int(3), Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf / int(3), Rational::NegativeInf);
    }

    #[test]
    fn div_inf_by_negative_finite() {
        assert_eq!(Rational::PositiveInf / int(-3), Rational::NegativeInf);
        assert_eq!(Rational::NegativeInf / int(-3), Rational::PositiveInf);
    }

    #[test]
    fn div_positive_by_zero() {
        assert_eq!(int(5) / int(0), Rational::PositiveInf);
    }

    #[test]
    fn div_negative_by_zero() {
        assert_eq!(int(-5) / int(0), Rational::NegativeInf);
    }

    #[test]
    #[should_panic(expected = "0 / 0")]
    fn div_zero_by_zero_panics() {
        let _ = int(0) / int(0);
    }

    #[test]
    #[should_panic(expected = "+inf / 0")]
    fn div_pos_inf_by_zero_panics() {
        let _ = Rational::PositiveInf / int(0);
    }

    #[test]
    #[should_panic(expected = "-inf / 0")]
    fn div_neg_inf_by_zero_panics() {
        let _ = Rational::NegativeInf / int(0);
    }

    #[test]
    #[should_panic(expected = "±inf / ±inf")]
    fn div_inf_by_inf_panics() {
        let _ = Rational::PositiveInf / Rational::PositiveInf;
    }
}
