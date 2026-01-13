/// Represents a rational number defined by a numerator and a denominator.
///
/// The number is always stored in normalized form:
/// - The denominator is always non-negative.
/// - It is reduced to lowest terms.
/// - A denominator of 0 represents infinity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    /// Creates a new `Rational` number.
    ///
    /// # Arguments
    ///
    /// * `num` - The numerator.
    /// * `den` - The denominator.
    ///
    /// # Panics
    ///
    /// Panics if both `num` and `den` are zero.
    pub fn new(num: i64, den: i64) -> Self {
        assert!(num != 0 || den != 0);
        let mut rat = Rational { num, den };
        rat.normalize();
        rat
    }

    /// Normalizes the rational number by dividing numerator and denominator by their GCD.
    /// Also ensures that the denominator is non-negative.
    fn normalize(&mut self) {
        let gcd = gcd(self.num, self.den);
        self.num /= gcd;
        self.den /= gcd;
        if self.den < 0 {
            self.num = -self.num;
            self.den = -self.den;
        }
    }

    /// Creates a `Rational` number from an integer.
    pub fn from_integer(arg: i64) -> Rational {
        Rational::new(arg, 1)
    }

    pub const POSITIVE_INFINITY: Self = Self { num: 1, den: 0 };
    pub const NEGATIVE_INFINITY: Self = Self { num: -1, den: 0 };
    pub const ZERO: Self = Self { num: 0, den: 1 };
}

impl std::cmp::PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<std::cmp::Ordering> {
        (self.num * other.den).partial_cmp(&(other.num * self.den))
    }
}

impl std::cmp::PartialEq<i64> for Rational {
    fn eq(&self, other: &i64) -> bool {
        self.num == other * self.den
    }
}

impl std::cmp::PartialOrd<i64> for Rational {
    fn partial_cmp(&self, other: &i64) -> Option<std::cmp::Ordering> {
        (self.num).partial_cmp(&(other * self.den))
    }
}

impl std::ops::AddAssign<&Rational> for Rational {
    fn add_assign(&mut self, other: &Rational) {
        self.num = self.num * other.den + other.num * self.den;
        self.den = self.den * other.den;
        self.normalize();
    }
}

impl std::ops::AddAssign<i64> for Rational {
    fn add_assign(&mut self, other: i64) {
        self.num += other * self.den;
        self.normalize();
    }
}

impl std::ops::Add<&Rational> for Rational {
    type Output = Rational;

    fn add(self, other: &Rational) -> Rational {
        let mut result = self;
        result += other;
        result
    }
}

impl std::ops::Add<&Rational> for &Rational {
    type Output = Rational;

    fn add(self, other: &Rational) -> Rational {
        let mut result = *self;
        result += other;
        result
    }
}

impl std::ops::Add<i64> for Rational {
    type Output = Rational;

    fn add(self, other: i64) -> Rational {
        let mut result = self;
        result += other;
        result
    }
}

impl std::ops::Add<i64> for &Rational {
    type Output = Rational;

    fn add(self, other: i64) -> Rational {
        let mut result = *self;
        result += other;
        result
    }
}

impl std::ops::Add<&Rational> for i64 {
    type Output = Rational;

    fn add(self, other: &Rational) -> Rational {
        let mut result = other.clone();
        result += self;
        result
    }
}

impl std::ops::Add<Rational> for i64 {
    type Output = Rational;

    fn add(self, other: Rational) -> Rational {
        let mut result = other.clone();
        result += self;
        result
    }
}

impl std::ops::SubAssign<&Rational> for Rational {
    fn sub_assign(&mut self, other: &Rational) {
        self.num = self.num * other.den - other.num * self.den;
        self.den = self.den * other.den;
        self.normalize();
    }
}

impl std::ops::SubAssign<i64> for Rational {
    fn sub_assign(&mut self, other: i64) {
        self.num -= other * self.den;
        self.normalize();
    }
}

impl std::ops::Sub<&Rational> for Rational {
    type Output = Rational;

    fn sub(self, other: &Rational) -> Rational {
        let mut result = self;
        result -= other;
        result
    }
}

impl std::ops::Sub<&Rational> for &Rational {
    type Output = Rational;

    fn sub(self, other: &Rational) -> Rational {
        let mut result = *self;
        result -= other;
        result
    }
}

impl std::ops::Sub<i64> for Rational {
    type Output = Rational;

    fn sub(self, other: i64) -> Rational {
        let mut result = self;
        result -= other;
        result
    }
}

impl std::ops::Sub<i64> for &Rational {
    type Output = Rational;

    fn sub(self, other: i64) -> Rational {
        let mut result = *self;
        result -= other;
        result
    }
}

impl std::ops::Sub<&Rational> for i64 {
    type Output = Rational;

    fn sub(self, other: &Rational) -> Rational {
        let mut result = Rational::from_integer(self);
        result -= other;
        result
    }
}

impl std::ops::Sub<Rational> for i64 {
    type Output = Rational;

    fn sub(self, other: Rational) -> Rational {
        let mut result = Rational::from_integer(self);
        result -= &other;
        result
    }
}

impl std::ops::MulAssign<&Rational> for Rational {
    fn mul_assign(&mut self, other: &Rational) {
        self.num *= other.num;
        self.den *= other.den;
        self.normalize();
    }
}

impl std::ops::MulAssign<i64> for Rational {
    fn mul_assign(&mut self, other: i64) {
        self.num *= other;
        self.normalize();
    }
}

impl std::ops::Mul<&Rational> for Rational {
    type Output = Rational;

    fn mul(self, other: &Rational) -> Rational {
        let mut result = self;
        result *= other;
        result
    }
}

impl std::ops::Mul<&Rational> for &Rational {
    type Output = Rational;

    fn mul(self, other: &Rational) -> Rational {
        let mut result = *self;
        result *= other;
        result
    }
}

impl std::ops::Mul<i64> for Rational {
    type Output = Rational;

    fn mul(self, other: i64) -> Rational {
        let mut result = self;
        result *= other;
        result
    }
}

impl std::ops::Mul<i64> for &Rational {
    type Output = Rational;

    fn mul(self, other: i64) -> Rational {
        let mut result = *self;
        result *= other;
        result
    }
}

impl std::ops::Mul<&Rational> for i64 {
    type Output = Rational;

    fn mul(self, other: &Rational) -> Rational {
        let mut result = other.clone();
        result *= self;
        result
    }
}

impl std::ops::Mul<Rational> for i64 {
    type Output = Rational;

    fn mul(self, other: Rational) -> Rational {
        let mut result = other.clone();
        result *= self;
        result
    }
}

impl std::ops::DivAssign<&Rational> for Rational {
    fn div_assign(&mut self, other: &Rational) {
        self.num *= other.den;
        self.den *= other.num;
        self.normalize();
    }
}

impl std::ops::DivAssign<i64> for Rational {
    fn div_assign(&mut self, other: i64) {
        self.den *= other;
        self.normalize();
    }
}

impl std::ops::Div<&Rational> for Rational {
    type Output = Rational;

    fn div(self, other: &Rational) -> Rational {
        let mut result = self;
        result /= other;
        result
    }
}

impl std::ops::Div<&Rational> for &Rational {
    type Output = Rational;

    fn div(self, other: &Rational) -> Rational {
        let mut result = *self;
        result /= other;
        result
    }
}

impl std::ops::Div<i64> for Rational {
    type Output = Rational;

    fn div(self, other: i64) -> Rational {
        let mut result = self;
        result /= other;
        result
    }
}

impl std::ops::Div<i64> for &Rational {
    type Output = Rational;

    fn div(self, other: i64) -> Rational {
        let mut result = *self;
        result /= other;
        result
    }
}

impl std::ops::Div<&Rational> for i64 {
    type Output = Rational;

    fn div(self, other: &Rational) -> Rational {
        let mut result = Rational::from_integer(self);
        result /= other;
        result
    }
}

impl std::ops::Div<Rational> for i64 {
    type Output = Rational;

    fn div(self, other: Rational) -> Rational {
        let mut result = Rational::from_integer(self);
        result /= &other;
        result
    }
}

impl std::ops::Neg for Rational {
    type Output = Rational;

    fn neg(self) -> Rational {
        Rational::new(-self.num, self.den)
    }
}

impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.den {
            0 => write!(f, "{}", if self.num > 0 { "∞" } else { "-∞" }),
            1 => write!(f, "{}", self.num),
            _ => write!(f, "{}/{}", self.num, self.den),
        }
    }
}

/// Computes the greatest common divisor of two numbers.
fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_and_normalization() {
        assert_eq!(Rational::new(2, 4), Rational::new(1, 2));
        assert_eq!(Rational::new(-2, 4), Rational::new(-1, 2));
        assert_eq!(Rational::new(2, -4), Rational::new(-1, 2));
        assert_eq!(Rational::new(-2, -4), Rational::new(1, 2));
        assert_eq!(Rational::new(0, 5), Rational::ZERO);
        assert_eq!(Rational::new(5, 0), Rational::POSITIVE_INFINITY);
    }

    #[test]
    #[should_panic]
    fn test_invalid_creation() {
        Rational::new(0, 0);
    }

    #[test]
    fn test_add() {
        let a = Rational::new(1, 2);
        let b = Rational::new(1, 3);
        assert_eq!(a + &b, Rational::new(5, 6));
        assert_eq!(a + 1, Rational::new(3, 2));
        assert_eq!(&a + &b, Rational::new(5, 6));
        assert_eq!(&a + 1, Rational::new(3, 2));
        assert_eq!(1 + &a, Rational::new(3, 2));
        assert_eq!(1 + a, Rational::new(3, 2));
    }

    #[test]
    fn test_add_assign() {
        let mut a = Rational::new(1, 2);
        a += &Rational::new(1, 3);
        assert_eq!(a, Rational::new(5, 6));

        let mut b = Rational::new(1, 2);
        b += 1;
        assert_eq!(b, Rational::new(3, 2));
    }

    #[test]
    fn test_sub() {
        let a = Rational::new(1, 2);
        let b = Rational::new(1, 3);
        assert_eq!(a - &b, Rational::new(1, 6));
        assert_eq!(a - 1, Rational::new(-1, 2));
        assert_eq!(&a - &b, Rational::new(1, 6));
        assert_eq!(&a - 1, Rational::new(-1, 2));
        assert_eq!(1 - &a, Rational::new(1, 2));
        assert_eq!(1 - a, Rational::new(1, 2));
    }

    #[test]
    fn test_sub_assign() {
        let mut a = Rational::new(1, 2);
        a -= &Rational::new(1, 3);
        assert_eq!(a, Rational::new(1, 6));

        let mut b = Rational::new(1, 2);
        b -= 1;
        assert_eq!(b, Rational::new(-1, 2));
    }

    #[test]
    fn test_mul() {
        let a = Rational::new(1, 2);
        let b = Rational::new(2, 3);
        assert_eq!(a * &b, Rational::new(1, 3));
        assert_eq!(a * 2, Rational::new(1, 1));
        assert_eq!(&a * &b, Rational::new(1, 3));
        assert_eq!(&a * 2, Rational::new(1, 1));
        assert_eq!(2 * &a, Rational::new(1, 1));
        assert_eq!(2 * a, Rational::new(1, 1));
    }

    #[test]
    fn test_mul_assign() {
        let mut a = Rational::new(1, 2);
        a *= &Rational::new(2, 3);
        assert_eq!(a, Rational::new(1, 3));

        let mut b = Rational::new(1, 2);
        b *= 2;
        assert_eq!(b, Rational::new(1, 1));
    }

    #[test]
    fn test_div() {
        let a = Rational::new(1, 2);
        let b = Rational::new(2, 3);
        assert_eq!(a / &b, Rational::new(3, 4));
        assert_eq!(a / 2, Rational::new(1, 4));
        assert_eq!(&a / &b, Rational::new(3, 4));
        assert_eq!(&a / 2, Rational::new(1, 4));
        assert_eq!(2 / &a, Rational::new(4, 1));
        assert_eq!(2 / a, Rational::new(4, 1));
    }

    #[test]
    fn test_div_assign() {
        let mut a = Rational::new(1, 2);
        a /= &Rational::new(2, 3);
        assert_eq!(a, Rational::new(3, 4));

        let mut b = Rational::new(1, 2);
        b /= 2;
        assert_eq!(b, Rational::new(1, 4));
    }

    #[test]
    fn test_neg() {
        let a = Rational::new(1, 2);
        assert_eq!(-a, Rational::new(-1, 2));
        assert_eq!(-Rational::new(-1, 2), Rational::new(1, 2));
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Rational::new(1, 2)), "1/2");
        assert_eq!(format!("{}", Rational::new(2, 1)), "2");
        assert_eq!(format!("{}", Rational::new(0, 5)), "0");
        assert_eq!(format!("{}", Rational::new(-1, 2)), "-1/2");
    }

    #[test]
    fn test_comparison() {
        let a = Rational::new(1, 2);
        let b = Rational::new(1, 3);
        let c = Rational::new(1, 2);

        assert!(a > b);
        assert!(b < a);
        assert!(a >= b);
        assert!(b <= a);
        assert!(a >= c);
        assert!(a <= c);

        // Comparison with i64
        let d = Rational::new(4, 2); // 2
        assert!(d == 2);
        assert!(d <= 2);
        assert!(d >= 2);
        assert!(d < 3);
        assert!(d > 1);

        let e = Rational::new(1, 2);
        assert!(e < 1);
        assert!(e > 0);
    }
}
