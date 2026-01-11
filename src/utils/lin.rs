use crate::utils::rational::Rational;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lin {
    vars: HashMap<u32, Rational>,
    known_term: Rational,
}

impl Lin {
    pub fn new(vars: HashMap<u32, Rational>, known_term: Rational) -> Self {
        Lin { vars, known_term }
    }
}

impl std::fmt::Display for Lin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for (var, coeff) in &self.vars {
            if !first && *coeff >= 0 {
                write!(f, "+")?;
            }
            write!(f, "{}*{}", coeff, var)?;
            first = false;
        }
        if !first && self.known_term >= 0 {
            write!(f, "+")?;
        }
        write!(f, "{}", self.known_term)
    }
}

impl std::ops::AddAssign<&Lin> for Lin {
    fn add_assign(&mut self, other: &Lin) {
        for (var, coeff) in &other.vars {
            *self.vars.entry(*var).or_insert(Rational::new(0, 1)) += coeff;
        }
        self.known_term += &other.known_term;
    }
}

impl std::ops::AddAssign<&Rational> for Lin {
    fn add_assign(&mut self, other: &Rational) {
        self.known_term += other;
    }
}

impl std::ops::Add<&Lin> for Lin {
    type Output = Lin;

    fn add(self, other: &Lin) -> Lin {
        let mut result = self;
        result += other;
        result
    }
}

impl std::ops::Add<&Rational> for Lin {
    type Output = Lin;

    fn add(self, other: &Rational) -> Lin {
        let mut result = self;
        result += other;
        result
    }
}

impl std::ops::SubAssign<&Lin> for Lin {
    fn sub_assign(&mut self, other: &Lin) {
        for (var, coeff) in &other.vars {
            *self.vars.entry(*var).or_insert(Rational::new(0, 1)) -= coeff;
        }
        self.known_term -= &other.known_term;
    }
}

impl std::ops::SubAssign<&Rational> for Lin {
    fn sub_assign(&mut self, other: &Rational) {
        self.known_term -= other;
    }
}

impl std::ops::Sub<&Lin> for Lin {
    type Output = Lin;

    fn sub(self, other: &Lin) -> Lin {
        let mut result = self;
        result -= other;
        result
    }
}

impl std::ops::Sub<&Rational> for Lin {
    type Output = Lin;

    fn sub(self, other: &Rational) -> Lin {
        let mut result = self;
        result -= other;
        result
    }
}

impl std::ops::MulAssign<&Rational> for Lin {
    fn mul_assign(&mut self, other: &Rational) {
        for coeff in self.vars.values_mut() {
            *coeff *= other;
        }
        self.known_term *= other;
    }
}

impl std::ops::Mul<&Rational> for Lin {
    type Output = Lin;

    fn mul(self, other: &Rational) -> Lin {
        let mut result = self;
        result *= other;
        result
    }
}

impl std::ops::DivAssign<&Rational> for Lin {
    fn div_assign(&mut self, other: &Rational) {
        for coeff in self.vars.values_mut() {
            *coeff /= other;
        }
        self.known_term /= other;
    }
}

impl std::ops::Div<&Rational> for Lin {
    type Output = Lin;

    fn div(self, other: &Rational) -> Lin {
        let mut result = self;
        result /= other;
        result
    }
}

impl std::ops::Neg for Lin {
    type Output = Lin;

    fn neg(self) -> Lin {
        let mut result = self;
        for coeff in result.vars.values_mut() {
            *coeff = -coeff.clone();
        }
        // Do the same for the known_term
        result.known_term = -result.known_term.clone();
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::rational::Rational;
    use std::collections::HashMap;

    #[test]
    fn test_new_and_display() {
        let mut vars = HashMap::new();
        vars.insert(1, Rational::new(1, 2));
        vars.insert(2, Rational::new(-3, 4));
        let known_term = Rational::new(5, 1);
        let lin = Lin::new(vars, known_term);

        // Display representation depends on map iteration order
        let s = format!("{}", lin);
        assert!(s.contains("1/2*1") || s.contains("-3/4*2"));
        assert!(s.contains("5"));
    }

    #[test]
    fn test_add_lin() {
        let mut vars1 = HashMap::new();
        vars1.insert(1, Rational::new(1, 1));
        let lin1 = Lin::new(vars1, Rational::new(2, 1));

        let mut vars2 = HashMap::new();
        vars2.insert(1, Rational::new(2, 1));
        vars2.insert(2, Rational::new(3, 1));
        let lin2 = Lin::new(vars2, Rational::new(4, 1));

        let sum = lin1 + &lin2;

        let mut expected_vars = HashMap::new();
        expected_vars.insert(1, Rational::new(3, 1));
        expected_vars.insert(2, Rational::new(3, 1));
        let expected = Lin::new(expected_vars, Rational::new(6, 1));

        assert_eq!(sum, expected);
    }

    #[test]
    fn test_add_rational() {
        let mut vars = HashMap::new();
        vars.insert(1, Rational::new(1, 1));
        let lin = Lin::new(vars.clone(), Rational::new(2, 1));
        let rat = Rational::new(3, 1);

        let sum = lin + &rat;
        let expected = Lin::new(vars, Rational::new(5, 1));

        assert_eq!(sum, expected);
    }

    #[test]
    fn test_sub_lin() {
        let mut vars1 = HashMap::new();
        vars1.insert(1, Rational::new(1, 1));
        let lin1 = Lin::new(vars1, Rational::new(2, 1));

        let mut vars2 = HashMap::new();
        vars2.insert(1, Rational::new(2, 1));
        vars2.insert(2, Rational::new(3, 1));
        let lin2 = Lin::new(vars2, Rational::new(4, 1));

        let diff = lin1 - &lin2;

        let mut expected_vars = HashMap::new();
        expected_vars.insert(1, Rational::new(-1, 1));
        expected_vars.insert(2, Rational::new(-3, 1));
        let expected = Lin::new(expected_vars, Rational::new(-2, 1));

        assert_eq!(diff, expected);
    }

    #[test]
    fn test_sub_rational() {
        let mut vars = HashMap::new();
        vars.insert(1, Rational::new(1, 1));
        let lin = Lin::new(vars.clone(), Rational::new(2, 1));
        let rat = Rational::new(3, 1);

        let diff = lin - &rat;
        let expected = Lin::new(vars, Rational::new(-1, 1));

        assert_eq!(diff, expected);
    }

    #[test]
    fn test_mul_rational() {
        let mut vars = HashMap::new();
        vars.insert(1, Rational::new(1, 2));
        let lin = Lin::new(vars, Rational::new(3, 4));
        let rat = Rational::new(2, 1);

        let product = lin * &rat;

        let mut expected_vars = HashMap::new();
        expected_vars.insert(1, Rational::new(1, 1));
        let expected = Lin::new(expected_vars, Rational::new(3, 2));

        assert_eq!(product, expected);
    }

    #[test]
    fn test_div_rational() {
        let mut vars = HashMap::new();
        vars.insert(1, Rational::new(1, 1));
        let lin = Lin::new(vars, Rational::new(3, 2));
        let rat = Rational::new(2, 1);

        let quotient = lin / &rat;

        let mut expected_vars = HashMap::new();
        expected_vars.insert(1, Rational::new(1, 2));
        let expected = Lin::new(expected_vars, Rational::new(3, 4));

        assert_eq!(quotient, expected);
    }

    #[test]
    fn test_neg() {
        let mut vars = HashMap::new();
        vars.insert(1, Rational::new(1, 2));
        let lin = Lin::new(vars, Rational::new(-3, 4));

        let neg_lin = -lin;

        let mut expected_vars = HashMap::new();
        expected_vars.insert(1, Rational::new(-1, 2));
        let expected = Lin::new(expected_vars, Rational::new(3, 4));

        assert_eq!(neg_lin, expected);
    }
}
