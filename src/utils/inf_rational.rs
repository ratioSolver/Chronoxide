use crate::utils::rational::Rational;
use std::{
    cmp::Ordering,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InfRational {
    rat: Rational,
    inf: Rational,
}

impl InfRational {
    pub fn new(rat: Rational, inf: Rational) -> Self {
        InfRational { rat, inf }
    }

    pub fn from_rational(rat: Rational) -> InfRational {
        InfRational {
            rat,
            inf: Rational::ZERO,
        }
    }

    pub fn from_integer(arg: i64) -> InfRational {
        InfRational {
            rat: Rational::from_integer(arg),
            inf: Rational::ZERO,
        }
    }

    pub const POSITIVE_INFINITY: Self = Self {
        rat: Rational::POSITIVE_INFINITY,
        inf: Rational::ZERO,
    };
    pub const NEGATIVE_INFINITY: Self = Self {
        rat: Rational::NEGATIVE_INFINITY,
        inf: Rational::ZERO,
    };
    pub const ZERO: Self = Self {
        rat: Rational::ZERO,
        inf: Rational::ZERO,
    };
}

impl From<Rational> for InfRational {
    fn from(arg: Rational) -> Self {
        InfRational::from_rational(arg)
    }
}

impl From<i64> for InfRational {
    fn from(arg: i64) -> Self {
        InfRational::from_integer(arg)
    }
}

impl PartialOrd for InfRational {
    fn partial_cmp(&self, other: &InfRational) -> Option<Ordering> {
        match self.rat.partial_cmp(&other.rat) {
            Some(Ordering::Equal) => self.inf.partial_cmp(&other.inf),
            ord => ord,
        }
    }
}

impl PartialEq<&Rational> for InfRational {
    fn eq(&self, other: &&Rational) -> bool {
        self.inf == 0 && self.rat == **other
    }
}

impl PartialOrd<&Rational> for InfRational {
    fn partial_cmp(&self, other: &&Rational) -> Option<Ordering> {
        match self.rat.partial_cmp(*other) {
            Some(Ordering::Equal) => self.inf.partial_cmp(&0),
            ord => ord,
        }
    }
}

impl PartialEq<i64> for InfRational {
    fn eq(&self, other: &i64) -> bool {
        self.inf == 0 && self.rat == *other
    }
}

impl PartialOrd<i64> for InfRational {
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        match self.rat.partial_cmp(other) {
            Some(Ordering::Equal) => self.inf.partial_cmp(&0),
            ord => ord,
        }
    }
}

impl AddAssign for InfRational {
    fn add_assign(&mut self, other: Self) {
        self.rat += other.rat;
        self.inf += other.inf;
    }
}

impl AddAssign<&InfRational> for InfRational {
    fn add_assign(&mut self, other: &InfRational) {
        self.rat += &other.rat;
        self.inf += &other.inf;
    }
}

impl AddAssign<&Rational> for InfRational {
    fn add_assign(&mut self, other: &Rational) {
        self.rat += other;
    }
}

impl AddAssign<i64> for InfRational {
    fn add_assign(&mut self, other: i64) {
        self.rat += other;
    }
}

impl Add<&InfRational> for InfRational {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = self;
        result += other;
        result
    }
}

impl Add<&InfRational> for &InfRational {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = *self;
        result += other;
        result
    }
}

impl Add<&Rational> for InfRational {
    type Output = InfRational;

    fn add(self, other: &Rational) -> InfRational {
        let mut result = self;
        result += other;
        result
    }
}

impl Add<&Rational> for &InfRational {
    type Output = InfRational;

    fn add(self, other: &Rational) -> InfRational {
        let mut result = *self;
        result += other;
        result
    }
}

impl Add<i64> for InfRational {
    type Output = InfRational;

    fn add(self, other: i64) -> InfRational {
        let mut result = self;
        result += other;
        result
    }
}

impl Add<i64> for &InfRational {
    type Output = InfRational;

    fn add(self, other: i64) -> InfRational {
        let mut result = *self;
        result += other;
        result
    }
}

impl Add<InfRational> for Rational {
    type Output = InfRational;

    fn add(self, other: InfRational) -> InfRational {
        let mut result = other;
        result += &self;
        result
    }
}

impl Add<InfRational> for &Rational {
    type Output = InfRational;

    fn add(self, other: InfRational) -> InfRational {
        let mut result = other;
        result += self;
        result
    }
}

impl Add<&InfRational> for Rational {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result += &self;
        result
    }
}

impl Add<&InfRational> for &Rational {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result += self;
        result
    }
}

impl Add<InfRational> for i64 {
    type Output = InfRational;

    fn add(self, other: InfRational) -> InfRational {
        let mut result = other;
        result += self;
        result
    }
}

impl Add<&InfRational> for i64 {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result += self;
        result
    }
}

impl SubAssign for InfRational {
    fn sub_assign(&mut self, other: Self) {
        self.rat -= other.rat;
        self.inf -= other.inf;
    }
}

impl SubAssign<&InfRational> for InfRational {
    fn sub_assign(&mut self, other: &InfRational) {
        self.rat -= &other.rat;
        self.inf -= &other.inf;
    }
}

impl SubAssign<&Rational> for InfRational {
    fn sub_assign(&mut self, other: &Rational) {
        self.rat -= other;
    }
}

impl SubAssign<i64> for InfRational {
    fn sub_assign(&mut self, other: i64) {
        self.rat -= other;
    }
}

impl Sub<&InfRational> for InfRational {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = self;
        result -= other;
        result
    }
}

impl Sub<&InfRational> for &InfRational {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = *self;
        result -= other;
        result
    }
}

impl Sub<&Rational> for InfRational {
    type Output = InfRational;

    fn sub(self, other: &Rational) -> InfRational {
        let mut result = self;
        result -= other;
        result
    }
}

impl Sub<&Rational> for &InfRational {
    type Output = InfRational;

    fn sub(self, other: &Rational) -> InfRational {
        let mut result = *self;
        result -= other;
        result
    }
}

impl Sub<i64> for InfRational {
    type Output = InfRational;

    fn sub(self, other: i64) -> InfRational {
        let mut result = self;
        result -= other;
        result
    }
}

impl Sub<i64> for &InfRational {
    type Output = InfRational;

    fn sub(self, other: i64) -> InfRational {
        let mut result = *self;
        result -= other;
        result
    }
}

impl Sub<InfRational> for Rational {
    type Output = InfRational;

    fn sub(self, other: InfRational) -> InfRational {
        let mut result = -other;
        result += &self;
        result
    }
}

impl Sub<InfRational> for &Rational {
    type Output = InfRational;

    fn sub(self, other: InfRational) -> InfRational {
        let mut result = -other;
        result += self;
        result
    }
}

impl Sub<&InfRational> for Rational {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = -(*other);
        result += &self;
        result
    }
}

impl Sub<&InfRational> for &Rational {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = -(*other);
        result += self;
        result
    }
}

impl Sub<InfRational> for i64 {
    type Output = InfRational;

    fn sub(self, other: InfRational) -> InfRational {
        let mut result = -other;
        result += self;
        result
    }
}

impl Sub<&InfRational> for i64 {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = -(*other);
        result += self;
        result
    }
}

impl MulAssign for InfRational {
    fn mul_assign(&mut self, other: Self) {
        self.rat *= other.rat;
        self.inf *= other.inf;
    }
}

impl MulAssign<&Rational> for InfRational {
    fn mul_assign(&mut self, other: &Rational) {
        self.rat *= other;
        self.inf *= other;
    }
}

impl MulAssign<i64> for InfRational {
    fn mul_assign(&mut self, other: i64) {
        self.rat *= other;
        self.inf *= other;
    }
}

impl Mul<&Rational> for InfRational {
    type Output = InfRational;

    fn mul(self, other: &Rational) -> InfRational {
        let mut result = self;
        result *= other;
        result
    }
}

impl Mul<&Rational> for &InfRational {
    type Output = InfRational;

    fn mul(self, other: &Rational) -> InfRational {
        let mut result = *self;
        result *= other;
        result
    }
}

impl Mul<i64> for InfRational {
    type Output = InfRational;

    fn mul(self, other: i64) -> InfRational {
        let mut result = self;
        result *= other;
        result
    }
}

impl Mul<i64> for &InfRational {
    type Output = InfRational;

    fn mul(self, other: i64) -> InfRational {
        let mut result = *self;
        result *= other;
        result
    }
}

impl Mul<InfRational> for Rational {
    type Output = InfRational;

    fn mul(self, other: InfRational) -> InfRational {
        let mut result = other;
        result *= &self;
        result
    }
}

impl Mul<InfRational> for &Rational {
    type Output = InfRational;

    fn mul(self, other: InfRational) -> InfRational {
        let mut result = other;
        result *= self;
        result
    }
}

impl Mul<&InfRational> for Rational {
    type Output = InfRational;

    fn mul(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result *= &self;
        result
    }
}

impl Mul<&InfRational> for &Rational {
    type Output = InfRational;

    fn mul(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result *= self;
        result
    }
}

impl Mul<InfRational> for i64 {
    type Output = InfRational;

    fn mul(self, other: InfRational) -> InfRational {
        let mut result = other;
        result *= self;
        result
    }
}

impl Mul<&InfRational> for i64 {
    type Output = InfRational;

    fn mul(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result *= self;
        result
    }
}

impl DivAssign for InfRational {
    fn div_assign(&mut self, other: Self) {
        self.rat /= other.rat;
        self.inf /= other.inf;
    }
}

impl DivAssign<&Rational> for InfRational {
    fn div_assign(&mut self, other: &Rational) {
        self.rat /= other;
        self.inf /= other;
    }
}

impl DivAssign<i64> for InfRational {
    fn div_assign(&mut self, other: i64) {
        self.rat /= other;
        self.inf /= other;
    }
}

impl Div<&Rational> for InfRational {
    type Output = InfRational;

    fn div(self, other: &Rational) -> InfRational {
        let mut result = self;
        result /= other;
        result
    }
}

impl Div<&Rational> for &InfRational {
    type Output = InfRational;

    fn div(self, other: &Rational) -> InfRational {
        let mut result = *self;
        result /= other;
        result
    }
}

impl Div<i64> for InfRational {
    type Output = InfRational;

    fn div(self, other: i64) -> InfRational {
        let mut result = self;
        result /= other;
        result
    }
}

impl Div<i64> for &InfRational {
    type Output = InfRational;

    fn div(self, other: i64) -> InfRational {
        let mut result = *self;
        result /= other;
        result
    }
}

impl Neg for InfRational {
    type Output = InfRational;

    fn neg(self) -> InfRational {
        InfRational {
            rat: -self.rat,
            inf: -self.inf,
        }
    }
}

impl std::fmt::Display for InfRational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.inf == 0 {
            write!(f, "{}", self.rat)
        } else if self.rat == 0 {
            write!(f, "{}ε", self.inf)
        } else {
            write!(f, "{} + {}ε", self.rat, self.inf)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let r1 = Rational::new(1, 2);
        let r2 = Rational::new(3, 4);
        let ir = InfRational::new(r1, r2);
        assert_eq!(ir.rat, r1);
        assert_eq!(ir.inf, r2);
    }

    #[test]
    fn test_equality() {
        let ir1 = InfRational::new(Rational::new(1, 2), Rational::new(3, 4));
        let ir2 = InfRational::new(Rational::new(2, 4), Rational::new(3, 4));
        assert_eq!(ir1, ir2);

        let ir3 = InfRational::new(Rational::new(1, 2), Rational::from_integer(0));
        let r = Rational::new(1, 2);
        assert_eq!(ir3, &r);

        // This fails to compile if PartialEq<i64> isn't implemented correctly or type inference fails
        // PartialEquals<i64> is implemented.
        let ir4 = InfRational::new(Rational::from_integer(5), Rational::from_integer(0));
        assert_eq!(ir4, 5);
    }

    #[test]
    fn test_ord() {
        let ir1 = InfRational::new(Rational::from_integer(0), Rational::from_integer(1)); // 1ε
        let ir2 = InfRational::new(Rational::from_integer(100), Rational::from_integer(0)); // 100

        // 1ε < 100
        assert!(ir1 < ir2);

        let ir3 = InfRational::new(Rational::from_integer(0), Rational::from_integer(-1)); // -1ε
        assert!(ir3 < ir2);
        assert!(ir3 < ir1);

        let ir4 = InfRational::new(Rational::from_integer(1), Rational::from_integer(1)); // 1 + 1ε
        // 1 + 1ε > 0 + 1ε
        assert!(ir4 > ir1);
    }

    #[test]
    fn test_ord_with_primitive_and_rational() {
        let pos_inf = InfRational::new(Rational::from_integer(0), Rational::from_integer(1));
        let neg_inf = InfRational::new(Rational::from_integer(0), Rational::from_integer(-1));
        let zero = 0;
        let rat_ten = Rational::from_integer(10);

        // 0 < 0 + 1ε
        assert!(pos_inf > zero);
        // 0 + 1ε < 10
        assert!(pos_inf < &rat_ten);

        // -1ε < 0
        assert!(neg_inf < zero);
        // -1ε < 10
        assert!(neg_inf < &rat_ten);
    }

    #[test]
    fn test_arithmetic() {
        let a = InfRational::new(Rational::from_integer(1), Rational::from_integer(2)); // 1 + 2ε
        let b = InfRational::new(Rational::from_integer(3), Rational::from_integer(4)); // 3 + 4ε

        // Add
        assert_eq!(
            a + &b,
            InfRational::new(Rational::from_integer(4), Rational::from_integer(6))
        );

        // Sub
        assert_eq!(
            b - &a,
            InfRational::new(Rational::from_integer(2), Rational::from_integer(2))
        );

        // Mul by scalar
        let scalar = Rational::from_integer(2);
        assert_eq!(
            a * &scalar,
            InfRational::new(Rational::from_integer(2), Rational::from_integer(4))
        );

        // Div by scalar
        assert_eq!(
            a / &scalar,
            InfRational::new(Rational::new(1, 2), Rational::from_integer(1))
        );
    }
}
