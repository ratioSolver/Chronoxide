use crate::smt::{ast::ArithExpr, rational::Rational};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, btree_map::Entry},
    fmt, ops,
};

pub(super) struct Lin {
    pub(super) vars: BTreeMap<usize, rug::Rational>, // Map from variable index to coefficient
    pub(super) const_term: rug::Rational,            // Constant term in the linear expression
}

impl From<&ArithExpr> for Lin {
    fn from(expr: &ArithExpr) -> Self {
        match expr {
            ArithExpr::Lit(r) => Lin {
                vars: BTreeMap::new(),
                const_term: match r {
                    Rational::Finite(fr) => fr.clone(),
                    Rational::NegativeInf | Rational::PositiveInf => panic!("Cannot convert infinite rational to linear expression"),
                },
            },
            ArithExpr::Val { val, .. } => Lin {
                vars: BTreeMap::new(),
                const_term: match val {
                    Rational::Finite(fr) => fr.clone(),
                    Rational::NegativeInf | Rational::PositiveInf => panic!("Cannot convert infinite rational to linear expression"),
                },
            },
            ArithExpr::Int(v) | ArithExpr::Real(v) => {
                let mut vars = BTreeMap::new();
                vars.insert(*v, rug::Rational::from(1));
                Lin { vars, const_term: rug::Rational::from(0) }
            }
            ArithExpr::Add(add) => {
                let mut lin = Lin { vars: BTreeMap::new(), const_term: rug::Rational::from(0) };
                for sub_expr in add {
                    lin += Lin::from(sub_expr);
                }
                lin
            }
            ArithExpr::Sub(e1, e2) => {
                let mut lin = Lin::from(e1.as_ref());
                lin -= Lin::from(e2.as_ref());
                lin
            }
            ArithExpr::Mul(mul) => {
                let mut lin = Lin { vars: BTreeMap::new(), const_term: rug::Rational::from(1) };
                for sub_expr in mul {
                    lin *= Lin::from(sub_expr);
                }
                lin
            }
            ArithExpr::Div(e1, e2) => {
                let mut lin = Lin::from(e1.as_ref());
                lin /= Lin::from(e2.as_ref());
                lin
            }
        }
    }
}

impl ops::Neg for Lin {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for coeff in self.vars.values_mut() {
            *coeff = -coeff.clone();
        }
        self.const_term = -self.const_term;
        self
    }
}

impl ops::AddAssign for Lin {
    fn add_assign(&mut self, other: Self) {
        for (var, coeff) in other.vars {
            match self.vars.entry(var) {
                Entry::Occupied(mut e) => {
                    *e.get_mut() += coeff;
                    if e.get().cmp0() == Ordering::Equal {
                        e.remove();
                    }
                }
                Entry::Vacant(e) => {
                    if coeff.cmp0() != Ordering::Equal {
                        e.insert(coeff);
                    }
                }
            }
        }
        self.const_term += other.const_term;
    }
}

impl ops::Add for Lin {
    type Output = Self;

    fn add(mut self, other: Self) -> Self::Output {
        self += other;
        self
    }
}

impl ops::SubAssign for Lin {
    fn sub_assign(&mut self, other: Self) {
        *self += -other;
    }
}

impl ops::Sub for Lin {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self + (-other)
    }
}

impl ops::MulAssign for Lin {
    fn mul_assign(&mut self, other: Self) {
        if !self.vars.is_empty() && !other.vars.is_empty() {
            panic!("Multiplication of two linear expressions with variables is not supported");
        }
        if !self.vars.is_empty() {
            // self has vars; other must be a pure constant (checked above)
            let factor = other.const_term;
            if factor.cmp0() == Ordering::Equal {
                self.vars.clear();
                self.const_term = rug::Rational::from(0);
            } else {
                for coeff in self.vars.values_mut() {
                    *coeff *= factor.clone();
                }
                self.const_term *= factor;
            }
        } else if !other.vars.is_empty() {
            // other has vars; self is a pure constant
            let self_const = self.const_term.clone();
            let other_const = other.const_term.clone();
            self.vars = other.vars;
            for coeff in self.vars.values_mut() {
                *coeff *= self_const.clone();
            }
            self.const_term = self_const * other_const;
        } else {
            // both are pure constants
            self.const_term *= other.const_term;
        }
    }
}

impl ops::Mul for Lin {
    type Output = Self;

    fn mul(mut self, other: Self) -> Self::Output {
        self *= other;
        self
    }
}

impl ops::DivAssign for Lin {
    fn div_assign(&mut self, other: Self) {
        if !other.vars.is_empty() {
            panic!("Division by a linear expression with variables is not supported");
        }
        if other.const_term.cmp0() == Ordering::Equal {
            panic!("Division by zero");
        }
        let divisor = other.const_term.clone();
        for coeff in self.vars.values_mut() {
            *coeff /= divisor.clone();
        }
        self.const_term /= divisor;
    }
}

impl ops::Div for Lin {
    type Output = Self;

    fn div(mut self, other: Self) -> Self::Output {
        self /= other;
        self
    }
}

impl fmt::Display for Lin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Sort terms to ensure deterministic formatting regardless of HashMap iteration order.
        let mut terms: Vec<(usize, &rug::Rational)> = self.vars.iter().map(|(var, coeff)| (*var, coeff)).collect();
        terms.sort_by_key(|(var, _)| *var);

        let mut first = true;
        for (var, coeff) in terms {
            if first {
                if coeff > &rug::Rational::from(0) {
                    if coeff == &rug::Rational::from(1) {
                        write!(f, "{}", var)?;
                    } else {
                        write!(f, "{}*{}", coeff, var)?;
                    }
                } else if coeff == &rug::Rational::from(-1) {
                    write!(f, "-{}", var)?;
                } else {
                    write!(f, "-{}*{}", -coeff.clone(), var)?;
                }
                first = false;
            } else if coeff > &rug::Rational::from(0) {
                if coeff == &rug::Rational::from(1) {
                    write!(f, " + {}", var)?;
                } else {
                    write!(f, " + {}*{}", coeff, var)?;
                }
            } else if coeff == &rug::Rational::from(-1) {
                write!(f, " - {}", var)?;
            } else {
                write!(f, " - {}*{}", -coeff.clone(), var)?;
            }
        }
        if first {
            write!(f, "{}", self.const_term)
        } else if !self.const_term.is_zero() {
            if self.const_term.is_positive() { write!(f, " + {}", self.const_term) } else { write!(f, " - {}", -self.const_term.clone()) }
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::{ast::ArithExpr, rational::Rational};

    fn r(n: i32, d: i32) -> rug::Rational {
        rug::Rational::from((n, d))
    }

    fn ri(n: i32) -> rug::Rational {
        rug::Rational::from(n)
    }

    fn lit(n: i32) -> ArithExpr {
        ArithExpr::Lit(Rational::Finite(ri(n)))
    }

    fn lit_frac(n: i32, d: i32) -> ArithExpr {
        ArithExpr::Lit(Rational::Finite(r(n, d)))
    }

    fn var(v: usize) -> Lin {
        let mut vars = BTreeMap::new();
        vars.insert(v, ri(1));
        Lin { vars, const_term: ri(0) }
    }

    fn constant(n: i32) -> Lin {
        Lin { vars: BTreeMap::new(), const_term: ri(n) }
    }

    fn coeff_of(lin: &Lin, v: usize) -> Option<rug::Rational> {
        lin.vars.get(&v).cloned()
    }

    // --- From<ArithExpr> ---

    #[test]
    fn from_lit_integer() {
        let lin = Lin::from(&lit(5));
        assert!(lin.vars.is_empty());
        assert_eq!(lin.const_term, ri(5));
    }

    #[test]
    fn from_lit_fraction() {
        let lin = Lin::from(&lit_frac(1, 3));
        assert!(lin.vars.is_empty());
        assert_eq!(lin.const_term, r(1, 3));
    }

    #[test]
    fn from_val() {
        let expr = ArithExpr::Val { lb: Rational::Finite(ri(0)), val: Rational::Finite(ri(7)), ub: Rational::Finite(ri(10)) };
        let lin = Lin::from(&expr);
        assert!(lin.vars.is_empty());
        assert_eq!(lin.const_term, ri(7));
    }

    #[test]
    fn from_int_variable() {
        let lin = Lin::from(&ArithExpr::Int(3));
        assert_eq!(lin.const_term, ri(0));
        assert_eq!(coeff_of(&lin, 3), Some(ri(1)));
        assert_eq!(lin.vars.len(), 1);
    }

    #[test]
    fn from_real_variable() {
        let lin = Lin::from(&ArithExpr::Real(7));
        assert_eq!(lin.const_term, ri(0));
        assert_eq!(coeff_of(&lin, 7), Some(ri(1)));
    }

    #[test]
    fn from_add_two_vars() {
        let lin = Lin::from(&ArithExpr::Add(vec![ArithExpr::Int(0), ArithExpr::Int(1)]));
        assert_eq!(coeff_of(&lin, 0), Some(ri(1)));
        assert_eq!(coeff_of(&lin, 1), Some(ri(1)));
        assert_eq!(lin.const_term, ri(0));
    }

    #[test]
    fn from_add_var_and_lit() {
        let lin = Lin::from(&ArithExpr::Add(vec![ArithExpr::Int(2), lit(3)]));
        assert_eq!(coeff_of(&lin, 2), Some(ri(1)));
        assert_eq!(lin.const_term, ri(3));
    }

    #[test]
    fn from_add_cancels_opposite_vars() {
        // x + (-x) should cancel
        let lin = Lin::from(&ArithExpr::Add(vec![ArithExpr::Int(0), ArithExpr::Sub(Box::new(lit(0)), Box::new(ArithExpr::Int(0)))]));
        assert!(lin.vars.is_empty());
        assert_eq!(lin.const_term, ri(0));
    }

    #[test]
    fn from_sub() {
        let lin = Lin::from(&ArithExpr::Sub(Box::new(ArithExpr::Int(0)), Box::new(lit(4))));
        assert_eq!(coeff_of(&lin, 0), Some(ri(1)));
        assert_eq!(lin.const_term, ri(-4));
    }

    #[test]
    fn from_mul_var_by_scalar() {
        // 3 * x0
        let lin = Lin::from(&ArithExpr::Mul(vec![lit(3), ArithExpr::Int(0)]));
        assert_eq!(coeff_of(&lin, 0), Some(ri(3)));
        assert_eq!(lin.const_term, ri(0));
    }

    #[test]
    fn from_mul_scalars() {
        let lin = Lin::from(&ArithExpr::Mul(vec![lit(3), lit(4)]));
        assert!(lin.vars.is_empty());
        assert_eq!(lin.const_term, ri(12));
    }

    #[test]
    fn from_div_var_by_scalar() {
        // x0 / 2
        let lin = Lin::from(&ArithExpr::Div(Box::new(ArithExpr::Int(0)), Box::new(lit(2))));
        assert_eq!(coeff_of(&lin, 0), Some(r(1, 2)));
        assert_eq!(lin.const_term, ri(0));
    }

    #[test]
    fn from_div_scalar_by_scalar() {
        let lin = Lin::from(&ArithExpr::Div(Box::new(lit(6)), Box::new(lit(4))));
        assert!(lin.vars.is_empty());
        assert_eq!(lin.const_term, r(3, 2));
    }

    #[test]
    #[should_panic(expected = "Cannot convert infinite rational")]
    fn from_lit_pos_inf_panics() {
        let _ = Lin::from(&ArithExpr::Lit(Rational::PositiveInf));
    }

    #[test]
    #[should_panic(expected = "Cannot convert infinite rational")]
    fn from_val_neg_inf_panics() {
        let _ = Lin::from(&ArithExpr::Val { lb: Rational::NegativeInf, val: Rational::NegativeInf, ub: Rational::PositiveInf });
    }

    #[test]
    #[should_panic(expected = "Multiplication of two linear expressions")]
    fn from_mul_two_vars_panics() {
        let _ = Lin::from(&ArithExpr::Mul(vec![ArithExpr::Int(0), ArithExpr::Int(1)]));
    }

    #[test]
    #[should_panic(expected = "Division by a linear expression with variables")]
    fn from_div_by_var_panics() {
        let _ = Lin::from(&ArithExpr::Div(Box::new(lit(1)), Box::new(ArithExpr::Int(0))));
    }

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn from_div_by_zero_panics() {
        let _ = Lin::from(&ArithExpr::Div(Box::new(ArithExpr::Int(0)), Box::new(lit(0))));
    }

    // --- Neg ---

    #[test]
    fn neg_constant() {
        assert_eq!((-constant(3)).const_term, ri(-3));
    }

    #[test]
    fn neg_var() {
        let lin = -var(0);
        assert_eq!(coeff_of(&lin, 0), Some(ri(-1)));
        assert_eq!(lin.const_term, ri(0));
    }

    #[test]
    fn neg_mixed() {
        let mut vars = BTreeMap::new();
        vars.insert(0usize, ri(2));
        let lin = Lin { vars, const_term: ri(-5) };
        let neg = -lin;
        assert_eq!(coeff_of(&neg, 0), Some(ri(-2)));
        assert_eq!(neg.const_term, ri(5));
    }

    // --- Add / AddAssign ---

    #[test]
    fn add_two_constants() {
        let result = constant(3) + constant(4);
        assert!(result.vars.is_empty());
        assert_eq!(result.const_term, ri(7));
    }

    #[test]
    fn add_same_var_accumulates_coefficient() {
        let result = var(0) + var(0);
        assert_eq!(coeff_of(&result, 0), Some(ri(2)));
    }

    #[test]
    fn add_opposite_vars_cancels() {
        let result = var(0) + (-var(0));
        assert!(result.vars.is_empty());
    }

    #[test]
    fn add_different_vars() {
        let result = var(0) + var(1);
        assert_eq!(coeff_of(&result, 0), Some(ri(1)));
        assert_eq!(coeff_of(&result, 1), Some(ri(1)));
    }

    #[test]
    fn add_assign_updates_in_place() {
        let mut a = var(0);
        a += constant(5);
        assert_eq!(coeff_of(&a, 0), Some(ri(1)));
        assert_eq!(a.const_term, ri(5));
    }

    // --- Sub / SubAssign ---

    #[test]
    fn sub_constants() {
        let result = constant(7) - constant(3);
        assert_eq!(result.const_term, ri(4));
    }

    #[test]
    fn sub_var_from_itself() {
        let result = var(0) - var(0);
        assert!(result.vars.is_empty());
        assert_eq!(result.const_term, ri(0));
    }

    #[test]
    fn sub_assign() {
        let mut a = constant(10);
        a -= constant(3);
        assert_eq!(a.const_term, ri(7));
    }

    // --- Mul / MulAssign ---

    #[test]
    fn mul_constant_by_constant() {
        let result = constant(3) * constant(4);
        assert!(result.vars.is_empty());
        assert_eq!(result.const_term, ri(12));
    }

    #[test]
    fn mul_var_by_scalar() {
        let result = var(0) * constant(3);
        assert_eq!(coeff_of(&result, 0), Some(ri(3)));
        assert_eq!(result.const_term, ri(0));
    }

    #[test]
    fn mul_scalar_by_var() {
        let result = constant(3) * var(0);
        assert_eq!(coeff_of(&result, 0), Some(ri(3)));
    }

    #[test]
    fn mul_by_zero_clears() {
        let result = var(0) * constant(0);
        assert!(result.vars.is_empty());
        assert_eq!(result.const_term, ri(0));
    }

    #[test]
    fn mul_assign_scales_var() {
        let mut a = var(2);
        a *= constant(5);
        assert_eq!(coeff_of(&a, 2), Some(ri(5)));
    }

    #[test]
    #[should_panic(expected = "Multiplication of two linear expressions with variables")]
    fn mul_two_vars_panics() {
        let _ = var(0) * var(1);
    }

    // --- Div / DivAssign ---

    #[test]
    fn div_constant_by_constant() {
        let result = constant(6) / constant(3);
        assert_eq!(result.const_term, ri(2));
    }

    #[test]
    fn div_var_by_scalar() {
        let result = var(0) / constant(4);
        assert_eq!(coeff_of(&result, 0), Some(r(1, 4)));
        assert_eq!(result.const_term, ri(0));
    }

    #[test]
    fn div_assign_scales_down() {
        let mut a = var(0);
        a /= constant(2);
        assert_eq!(coeff_of(&a, 0), Some(r(1, 2)));
    }

    #[test]
    #[should_panic(expected = "Division by a linear expression with variables")]
    fn div_by_var_panics() {
        let _ = constant(1) / var(0);
    }

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn div_by_zero_panics() {
        let _ = constant(1) / constant(0);
    }

    // --- Display ---

    #[test]
    fn display_zero_constant() {
        assert_eq!(constant(0).to_string(), "0");
    }

    #[test]
    fn display_positive_constant() {
        assert_eq!(constant(5).to_string(), "5");
    }

    #[test]
    fn display_negative_constant() {
        assert_eq!(constant(-3).to_string(), "-3");
    }

    #[test]
    fn display_single_var_coeff_one() {
        assert_eq!(var(2).to_string(), "2");
    }

    #[test]
    fn display_single_var_coeff_neg_one() {
        assert_eq!((-var(2)).to_string(), "-2");
    }

    #[test]
    fn display_var_with_positive_coeff() {
        let result = var(0) * constant(3);
        assert_eq!(result.to_string(), "3*0");
    }

    #[test]
    fn display_var_with_negative_coeff() {
        let result = var(0) * constant(-2);
        assert_eq!(result.to_string(), "-2*0");
    }

    #[test]
    fn display_var_plus_constant() {
        let result = var(0) + constant(4);
        assert_eq!(result.to_string(), "0 + 4");
    }

    #[test]
    fn display_var_minus_constant() {
        let result = var(0) + constant(-4);
        assert_eq!(result.to_string(), "0 - 4");
    }

    #[test]
    fn display_two_vars_ordered() {
        let result = var(1) + var(0);
        // BTreeMap gives deterministic order: var 0 before var 1
        assert_eq!(result.to_string(), "0 + 1");
    }

    #[test]
    fn display_fraction_constant() {
        let lin = Lin::from(&lit_frac(1, 3));
        assert_eq!(lin.to_string(), "1/3");
    }
}
