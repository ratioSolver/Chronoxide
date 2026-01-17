use std::{
    cmp::Ordering,
    fmt::{Display, Formatter, Result},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

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
        let gcd = gcd(self.num, self.den).abs();
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

impl From<i64> for Rational {
    fn from(arg: i64) -> Self {
        Rational::from_integer(arg)
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        (self.num * other.den).partial_cmp(&(other.num * self.den))
    }
}

impl PartialOrd<i64> for Rational {
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        (self.num).partial_cmp(&(other * self.den))
    }
}

impl PartialOrd<i64> for &Rational {
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        (self.num).partial_cmp(&(other * self.den))
    }
}

impl PartialEq<i64> for Rational {
    fn eq(&self, other: &i64) -> bool {
        self.num == other * self.den
    }
}

impl PartialEq<i64> for &Rational {
    fn eq(&self, other: &i64) -> bool {
        self.num == other * self.den
    }
}

impl AddAssign for Rational {
    fn add_assign(&mut self, other: Self) {
        if self.den == 0 {
            if other.den == 0 && self.num != other.num {
                panic!("Indeterminate form: infinity + (-infinity)");
            }
            return;
        }
        if other.den == 0 {
            *self = other;
            return;
        }
        let g = gcd(self.den, other.den);
        let den = other.den / g;
        self.num = self.num * den + other.num * (self.den / g);
        self.den *= den;
        self.normalize();
    }
}

impl AddAssign<&Rational> for Rational {
    fn add_assign(&mut self, other: &Rational) {
        if self.den == 0 {
            if other.den == 0 && self.num != other.num {
                panic!("Indeterminate form: infinity + (-infinity)");
            }
            return;
        }
        if other.den == 0 {
            *self = *other;
            return;
        }
        let g = gcd(self.den, other.den);
        let den = other.den / g;
        self.num = self.num * den + other.num * (self.den / g);
        self.den *= den;
        self.normalize();
    }
}

impl AddAssign<i64> for Rational {
    fn add_assign(&mut self, other: i64) {
        self.num += other * self.den;
        self.normalize();
    }
}

impl SubAssign for Rational {
    fn sub_assign(&mut self, other: Self) {
        if self.den == 0 {
            if other.den == 0 && self.num == other.num {
                panic!("Indeterminate form: infinity - infinity");
            }
            return;
        }
        if other.den == 0 {
            *self = -other;
            return;
        }
        let g = gcd(self.den, other.den);
        let den = other.den / g;
        self.num = self.num * den - other.num * (self.den / g);
        self.den *= den;
        self.normalize();
    }
}

impl SubAssign<&Rational> for Rational {
    fn sub_assign(&mut self, other: &Rational) {
        if self.den == 0 {
            if other.den == 0 && self.num == other.num {
                panic!("Indeterminate form: infinity - infinity");
            }
            return;
        }
        if other.den == 0 {
            *self = -*other;
            return;
        }
        let g = gcd(self.den, other.den);
        let den = other.den / g;
        self.num = self.num * den - other.num * (self.den / g);
        self.den *= den;
        self.normalize();
    }
}

impl SubAssign<i64> for Rational {
    fn sub_assign(&mut self, other: i64) {
        self.num -= other * self.den;
        self.normalize();
    }
}

impl MulAssign for Rational {
    fn mul_assign(&mut self, other: Self) {
        if (self.num == 0 && other.den == 0) || (self.den == 0 && other.num == 0) {
            panic!("Indeterminate form: 0 * infinity");
        }
        let g1 = gcd(self.num, other.den).abs();
        let g2 = gcd(other.num, self.den).abs();
        self.num = (self.num / g1) * (other.num / g2);
        self.den = (self.den / g2) * (other.den / g1);
        self.normalize();
    }
}

impl MulAssign<&Rational> for Rational {
    fn mul_assign(&mut self, other: &Rational) {
        if (self.num == 0 && other.den == 0) || (self.den == 0 && other.num == 0) {
            panic!("Indeterminate form: 0 * infinity");
        }
        let g1 = gcd(self.num, other.den).abs();
        let g2 = gcd(other.num, self.den).abs();
        self.num = (self.num / g1) * (other.num / g2);
        self.den = (self.den / g2) * (other.den / g1);
        self.normalize();
    }
}

impl MulAssign<i64> for Rational {
    fn mul_assign(&mut self, other: i64) {
        if self.den == 0 && other == 0 {
            panic!("Indeterminate form: infinity * 0");
        }
        let g = gcd(other, self.den).abs();
        self.num *= other / g;
        self.den /= g;
        self.normalize();
    }
}

impl DivAssign for Rational {
    fn div_assign(&mut self, other: Self) {
        if self.num == 0 && other.num == 0 {
            panic!("Indeterminate form: 0 / 0");
        }
        if self.den == 0 && other.den == 0 {
            panic!("Indeterminate form: infinity / infinity");
        }
        let g1 = gcd(self.num, other.num).abs();
        let g2 = gcd(other.den, self.den).abs();
        self.num = (self.num / g1) * (other.den / g2);
        self.den = (self.den / g2) * (other.num / g1);
        self.normalize();
    }
}

impl DivAssign<&Rational> for Rational {
    fn div_assign(&mut self, other: &Rational) {
        if self.num == 0 && other.num == 0 {
            panic!("Indeterminate form: 0 / 0");
        }
        if self.den == 0 && other.den == 0 {
            panic!("Indeterminate form: infinity / infinity");
        }
        let g1 = gcd(self.num, other.num).abs();
        let g2 = gcd(other.den, self.den).abs();
        self.num = (self.num / g1) * (other.den / g2);
        self.den = (self.den / g2) * (other.num / g1);
        self.normalize();
    }
}

impl DivAssign<i64> for Rational {
    fn div_assign(&mut self, other: i64) {
        if self.num == 0 && other == 0 {
            panic!("Indeterminate form: 0 / 0");
        }
        let g = gcd(self.num, other).abs();
        self.num /= g;
        self.den *= other / g;
        self.normalize();
    }
}

macro_rules! impl_op {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        // Rational op Rational
        impl $trait<Rational> for Rational {
            type Output = Rational;
            fn $method(mut self, other: Rational) -> Rational {
                self.$assign_method(&other);
                self
            }
        }

        // Rational op &Rational
        impl $trait<&Rational> for Rational {
            type Output = Rational;
            fn $method(mut self, other: &Rational) -> Rational {
                self.$assign_method(other);
                self
            }
        }

        // &Rational op Rational
        impl $trait<Rational> for &Rational {
            type Output = Rational;
            fn $method(self, other: Rational) -> Rational {
                let mut res = *self;
                res.$assign_method(&other);
                res
            }
        }

        // &Rational op &Rational
        impl $trait<&Rational> for &Rational {
            type Output = Rational;
            fn $method(self, other: &Rational) -> Rational {
                let mut res = *self;
                res.$assign_method(other);
                res
            }
        }
    };
}

macro_rules! impl_op_scalar {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident) => {
        // Rational op i64
        impl $trait<i64> for Rational {
            type Output = Rational;
            fn $method(mut self, other: i64) -> Rational {
                self.$assign_method(other);
                self
            }
        }

        // &Rational op i64
        impl $trait<i64> for &Rational {
            type Output = Rational;
            fn $method(self, other: i64) -> Rational {
                let mut res = *self;
                res.$assign_method(other);
                res
            }
        }
    };
}

macro_rules! impl_rev_op {
    ($trait:ident, $method:ident) => {
        // i64 op Rational
        impl $trait<Rational> for i64 {
            type Output = Rational;
            fn $method(self, other: Rational) -> Rational {
                let mut res = Rational::from(self);
                res = res.$method(&other);
                res
            }
        }

        // i64 op &Rational
        impl $trait<&Rational> for i64 {
            type Output = Rational;
            fn $method(self, other: &Rational) -> Rational {
                let mut res = Rational::from(self);
                res = res.$method(other);
                res
            }
        }
    };
}

impl_op!(Add, add, AddAssign, add_assign);
impl_op!(Sub, sub, SubAssign, sub_assign);
impl_op!(Mul, mul, MulAssign, mul_assign);
impl_op!(Div, div, DivAssign, div_assign);

impl_op_scalar!(Add, add, AddAssign, add_assign);
impl_op_scalar!(Sub, sub, SubAssign, sub_assign);
impl_op_scalar!(Mul, mul, MulAssign, mul_assign);
impl_op_scalar!(Div, div, DivAssign, div_assign);

impl_rev_op!(Add, add);
impl_rev_op!(Sub, sub);
impl_rev_op!(Mul, mul);
impl_rev_op!(Div, div);

impl Neg for Rational {
    type Output = Rational;

    fn neg(self) -> Rational {
        Rational::new(-self.num, self.den)
    }
}

impl Display for Rational {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
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
        assert_eq!(a * 2, Rational::from_integer(1));
        assert_eq!(&a * &b, Rational::new(1, 3));
        assert_eq!(&a * 2, Rational::from_integer(1));
        assert_eq!(2 * &a, Rational::from_integer(1));
        assert_eq!(2 * a, Rational::from_integer(1));
    }

    #[test]
    fn test_mul_assign() {
        let mut a = Rational::new(1, 2);
        a *= &Rational::new(2, 3);
        assert_eq!(a, Rational::new(1, 3));

        let mut b = Rational::new(1, 2);
        b *= 2;
        assert_eq!(b, Rational::from_integer(1));
    }

    #[test]
    fn test_div() {
        let a = Rational::new(1, 2);
        let b = Rational::new(2, 3);
        assert_eq!(a / &b, Rational::new(3, 4));
        assert_eq!(a / 2, Rational::new(1, 4));
        assert_eq!(&a / &b, Rational::new(3, 4));
        assert_eq!(&a / 2, Rational::new(1, 4));
        assert_eq!(2 / &a, Rational::from_integer(4));
        assert_eq!(2 / a, Rational::from_integer(4));
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
        assert_eq!(format!("{}", Rational::from_integer(2)), "2");
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

    #[test]
    fn test_infinity_arithmetic() {
        let inf = Rational::POSITIVE_INFINITY;
        let neg_inf = Rational::NEGATIVE_INFINITY;
        let one = Rational::from_integer(1);

        // Addition involving infinity
        assert_eq!(inf + one, inf);
        assert_eq!(neg_inf + one, neg_inf);
        assert_eq!(one + inf, inf);
        assert_eq!(one + neg_inf, neg_inf);
        assert_eq!(inf + inf, inf);
        assert_eq!(neg_inf + neg_inf, neg_inf);

        // Subtraction involving infinity
        assert_eq!(inf - one, inf);
        assert_eq!(neg_inf - one, neg_inf);
        assert_eq!(one - inf, neg_inf);
        assert_eq!(one - neg_inf, inf);
        assert_eq!(inf - neg_inf, inf); // inf + inf
        assert_eq!(neg_inf - inf, neg_inf); // -inf - inf
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: infinity - infinity")]
    fn test_inf_minus_inf() {
        let _ = Rational::POSITIVE_INFINITY - Rational::POSITIVE_INFINITY;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: infinity + (-infinity)")]
    fn test_inf_plus_neg_inf() {
        let _ = Rational::POSITIVE_INFINITY + Rational::NEGATIVE_INFINITY;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: infinity + (-infinity)")]
    fn test_neg_inf_plus_inf() {
        let _ = Rational::NEGATIVE_INFINITY + Rational::POSITIVE_INFINITY;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: infinity - infinity")]
    fn test_neg_inf_minus_neg_inf() {
        let _ = Rational::NEGATIVE_INFINITY - Rational::NEGATIVE_INFINITY;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: 0 * infinity")]
    fn test_zero_mul_inf() {
        let _ = Rational::ZERO * Rational::POSITIVE_INFINITY;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: 0 * infinity")]
    fn test_inf_mul_zero() {
        let _ = Rational::POSITIVE_INFINITY * Rational::ZERO;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: 0 / 0")]
    fn test_zero_div_zero() {
        let _ = Rational::ZERO / Rational::ZERO;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: infinity / infinity")]
    fn test_inf_div_inf() {
        let _ = Rational::POSITIVE_INFINITY / Rational::POSITIVE_INFINITY;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: infinity * 0")]
    fn test_inf_mul_zero_scalar() {
        let mut a = Rational::POSITIVE_INFINITY;
        a *= 0;
    }

    #[test]
    #[should_panic(expected = "Indeterminate form: 0 / 0")]
    fn test_zero_div_zero_scalar() {
        let mut a = Rational::ZERO;
        a /= 0;
    }

    #[test]
    #[should_panic]
    fn test_nan_creation_via_mul() {
        // 0 * inf is undefined/NaN, currently panics
        let _ = Rational::ZERO * Rational::POSITIVE_INFINITY;
    }
}
