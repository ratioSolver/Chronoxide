use crate::utils::rational::Rational;

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

impl std::cmp::PartialOrd for InfRational {
    fn partial_cmp(&self, other: &InfRational) -> Option<std::cmp::Ordering> {
        match self.rat.partial_cmp(&other.rat) {
            Some(std::cmp::Ordering::Equal) => self.inf.partial_cmp(&other.inf),
            ord => ord,
        }
    }
}

impl std::cmp::PartialEq<&Rational> for InfRational {
    fn eq(&self, other: &&Rational) -> bool {
        self.inf == 0 && self.rat == **other
    }
}

impl std::cmp::PartialOrd<&Rational> for InfRational {
    fn partial_cmp(&self, other: &&Rational) -> Option<std::cmp::Ordering> {
        match self.rat.partial_cmp(*other) {
            Some(std::cmp::Ordering::Equal) => self.inf.partial_cmp(&0),
            ord => ord,
        }
    }
}

impl std::cmp::PartialEq<i64> for InfRational {
    fn eq(&self, other: &i64) -> bool {
        self.inf == 0 && self.rat == *other
    }
}

impl std::cmp::PartialOrd<i64> for InfRational {
    fn partial_cmp(&self, other: &i64) -> Option<std::cmp::Ordering> {
        match self.rat.partial_cmp(other) {
            Some(std::cmp::Ordering::Equal) => self.inf.partial_cmp(&0),
            ord => ord,
        }
    }
}

impl std::ops::AddAssign<&InfRational> for InfRational {
    fn add_assign(&mut self, other: &InfRational) {
        self.rat += &other.rat;
        self.inf += &other.inf;
    }
}

impl std::ops::AddAssign<&Rational> for InfRational {
    fn add_assign(&mut self, other: &Rational) {
        self.rat += other;
    }
}

impl std::ops::AddAssign<i64> for InfRational {
    fn add_assign(&mut self, other: i64) {
        self.rat += other;
    }
}

impl std::ops::Add<&InfRational> for InfRational {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = self;
        result += other;
        result
    }
}

impl std::ops::Add<&InfRational> for &InfRational {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = *self;
        result += other;
        result
    }
}

impl std::ops::Add<&Rational> for InfRational {
    type Output = InfRational;

    fn add(self, other: &Rational) -> InfRational {
        let mut result = self;
        result += other;
        result
    }
}

impl std::ops::Add<&Rational> for &InfRational {
    type Output = InfRational;

    fn add(self, other: &Rational) -> InfRational {
        let mut result = *self;
        result += other;
        result
    }
}

impl std::ops::Add<i64> for InfRational {
    type Output = InfRational;

    fn add(self, other: i64) -> InfRational {
        let mut result = self;
        result += other;
        result
    }
}

impl std::ops::Add<i64> for &InfRational {
    type Output = InfRational;

    fn add(self, other: i64) -> InfRational {
        let mut result = *self;
        result += other;
        result
    }
}

impl std::ops::Add<InfRational> for Rational {
    type Output = InfRational;

    fn add(self, other: InfRational) -> InfRational {
        let mut result = other;
        result += &self;
        result
    }
}

impl std::ops::Add<InfRational> for &Rational {
    type Output = InfRational;

    fn add(self, other: InfRational) -> InfRational {
        let mut result = other;
        result += self;
        result
    }
}

impl std::ops::Add<&InfRational> for Rational {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result += &self;
        result
    }
}

impl std::ops::Add<&InfRational> for &Rational {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result += self;
        result
    }
}

impl std::ops::Add<InfRational> for i64 {
    type Output = InfRational;

    fn add(self, other: InfRational) -> InfRational {
        let mut result = other;
        result += self;
        result
    }
}

impl std::ops::Add<&InfRational> for i64 {
    type Output = InfRational;

    fn add(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result += self;
        result
    }
}

impl std::ops::SubAssign<&InfRational> for InfRational {
    fn sub_assign(&mut self, other: &InfRational) {
        self.rat -= &other.rat;
        self.inf -= &other.inf;
    }
}

impl std::ops::SubAssign<&Rational> for InfRational {
    fn sub_assign(&mut self, other: &Rational) {
        self.rat -= other;
    }
}

impl std::ops::SubAssign<i64> for InfRational {
    fn sub_assign(&mut self, other: i64) {
        self.rat -= other;
    }
}

impl std::ops::Sub<&InfRational> for InfRational {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = self;
        result -= other;
        result
    }
}

impl std::ops::Sub<&InfRational> for &InfRational {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = *self;
        result -= other;
        result
    }
}

impl std::ops::Sub<&Rational> for InfRational {
    type Output = InfRational;

    fn sub(self, other: &Rational) -> InfRational {
        let mut result = self;
        result -= other;
        result
    }
}

impl std::ops::Sub<&Rational> for &InfRational {
    type Output = InfRational;

    fn sub(self, other: &Rational) -> InfRational {
        let mut result = *self;
        result -= other;
        result
    }
}

impl std::ops::Sub<i64> for InfRational {
    type Output = InfRational;

    fn sub(self, other: i64) -> InfRational {
        let mut result = self;
        result -= other;
        result
    }
}

impl std::ops::Sub<i64> for &InfRational {
    type Output = InfRational;

    fn sub(self, other: i64) -> InfRational {
        let mut result = *self;
        result -= other;
        result
    }
}

impl std::ops::Sub<InfRational> for Rational {
    type Output = InfRational;

    fn sub(self, other: InfRational) -> InfRational {
        let mut result = -other;
        result += &self;
        result
    }
}

impl std::ops::Sub<InfRational> for &Rational {
    type Output = InfRational;

    fn sub(self, other: InfRational) -> InfRational {
        let mut result = -other;
        result += self;
        result
    }
}

impl std::ops::Sub<&InfRational> for Rational {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = -(*other);
        result += &self;
        result
    }
}

impl std::ops::Sub<&InfRational> for &Rational {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = -(*other);
        result += self;
        result
    }
}

impl std::ops::Sub<InfRational> for i64 {
    type Output = InfRational;

    fn sub(self, other: InfRational) -> InfRational {
        let mut result = -other;
        result += self;
        result
    }
}

impl std::ops::Sub<&InfRational> for i64 {
    type Output = InfRational;

    fn sub(self, other: &InfRational) -> InfRational {
        let mut result = -(*other);
        result += self;
        result
    }
}

impl std::ops::MulAssign<&Rational> for InfRational {
    fn mul_assign(&mut self, other: &Rational) {
        self.rat *= other;
        self.inf *= other;
    }
}

impl std::ops::MulAssign<i64> for InfRational {
    fn mul_assign(&mut self, other: i64) {
        self.rat *= other;
        self.inf *= other;
    }
}

impl std::ops::Mul<&Rational> for InfRational {
    type Output = InfRational;

    fn mul(self, other: &Rational) -> InfRational {
        let mut result = self;
        result *= other;
        result
    }
}

impl std::ops::Mul<&Rational> for &InfRational {
    type Output = InfRational;

    fn mul(self, other: &Rational) -> InfRational {
        let mut result = *self;
        result *= other;
        result
    }
}

impl std::ops::Mul<i64> for InfRational {
    type Output = InfRational;

    fn mul(self, other: i64) -> InfRational {
        let mut result = self;
        result *= other;
        result
    }
}

impl std::ops::Mul<i64> for &InfRational {
    type Output = InfRational;

    fn mul(self, other: i64) -> InfRational {
        let mut result = *self;
        result *= other;
        result
    }
}

impl std::ops::Mul<InfRational> for Rational {
    type Output = InfRational;

    fn mul(self, other: InfRational) -> InfRational {
        let mut result = other;
        result *= &self;
        result
    }
}

impl std::ops::Mul<InfRational> for &Rational {
    type Output = InfRational;

    fn mul(self, other: InfRational) -> InfRational {
        let mut result = other;
        result *= self;
        result
    }
}

impl std::ops::Mul<&InfRational> for Rational {
    type Output = InfRational;

    fn mul(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result *= &self;
        result
    }
}

impl std::ops::Mul<&InfRational> for &Rational {
    type Output = InfRational;

    fn mul(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result *= self;
        result
    }
}

impl std::ops::Mul<InfRational> for i64 {
    type Output = InfRational;

    fn mul(self, other: InfRational) -> InfRational {
        let mut result = other;
        result *= self;
        result
    }
}

impl std::ops::Mul<&InfRational> for i64 {
    type Output = InfRational;

    fn mul(self, other: &InfRational) -> InfRational {
        let mut result = *other;
        result *= self;
        result
    }
}

impl std::ops::DivAssign<&Rational> for InfRational {
    fn div_assign(&mut self, other: &Rational) {
        self.rat /= other;
        self.inf /= other;
    }
}

impl std::ops::DivAssign<i64> for InfRational {
    fn div_assign(&mut self, other: i64) {
        self.rat /= other;
        self.inf /= other;
    }
}

impl std::ops::Div<&Rational> for InfRational {
    type Output = InfRational;

    fn div(self, other: &Rational) -> InfRational {
        let mut result = self;
        result /= other;
        result
    }
}

impl std::ops::Div<&Rational> for &InfRational {
    type Output = InfRational;

    fn div(self, other: &Rational) -> InfRational {
        let mut result = *self;
        result /= other;
        result
    }
}

impl std::ops::Div<i64> for InfRational {
    type Output = InfRational;

    fn div(self, other: i64) -> InfRational {
        let mut result = self;
        result /= other;
        result
    }
}

impl std::ops::Div<i64> for &InfRational {
    type Output = InfRational;

    fn div(self, other: i64) -> InfRational {
        let mut result = *self;
        result /= other;
        result
    }
}

impl std::ops::Neg for InfRational {
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

        let ir3 = InfRational::new(Rational::new(1, 2), Rational::new(0, 1));
        let r = Rational::new(1, 2);
        assert_eq!(ir3, &r);

        // This fails to compile if PartialEq<i64> isn't implemented correctly or type inference fails
        // PartialEquals<i64> is implemented.
        let ir4 = InfRational::new(Rational::new(5, 1), Rational::new(0, 1));
        assert_eq!(ir4, 5);
    }

    #[test]
    fn test_ord() {
        let ir1 = InfRational::new(Rational::new(0, 1), Rational::new(1, 1)); // 1ε
        let ir2 = InfRational::new(Rational::new(100, 1), Rational::new(0, 1)); // 100

        // 1ε < 100
        assert!(ir1 < ir2);

        let ir3 = InfRational::new(Rational::new(0, 1), Rational::new(-1, 1)); // -1ε
        assert!(ir3 < ir2);
        assert!(ir3 < ir1);

        let ir4 = InfRational::new(Rational::new(1, 1), Rational::new(1, 1)); // 1 + 1ε
        // 1 + 1ε > 0 + 1ε
        assert!(ir4 > ir1);
    }

    #[test]
    fn test_ord_with_primitive_and_rational() {
        let pos_inf = InfRational::new(Rational::new(0, 1), Rational::new(1, 1));
        let neg_inf = InfRational::new(Rational::new(0, 1), Rational::new(-1, 1));
        let zero = 0;
        let rat_ten = Rational::new(10, 1);

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
        let a = InfRational::new(Rational::new(1, 1), Rational::new(2, 1)); // 1 + 2ε
        let b = InfRational::new(Rational::new(3, 1), Rational::new(4, 1)); // 3 + 4ε

        // Add
        assert_eq!(
            a + &b,
            InfRational::new(Rational::new(4, 1), Rational::new(6, 1))
        );

        // Sub
        assert_eq!(
            b - &a,
            InfRational::new(Rational::new(2, 1), Rational::new(2, 1))
        );

        // Mul by scalar
        let scalar = Rational::new(2, 1);
        assert_eq!(
            a * &scalar,
            InfRational::new(Rational::new(2, 1), Rational::new(4, 1))
        );

        // Div by scalar
        assert_eq!(
            a / &scalar,
            InfRational::new(Rational::new(1, 2), Rational::new(1, 1))
        );
    }
}
