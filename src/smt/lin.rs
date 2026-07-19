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

impl From<ArithExpr> for Lin {
    fn from(expr: ArithExpr) -> Self {
        match expr {
            ArithExpr::Lit(r) => Lin {
                vars: BTreeMap::new(),
                const_term: match r {
                    Rational::Finite(fr) => fr,
                    Rational::NegativeInf | Rational::PositiveInf => panic!("Cannot convert infinite rational to linear expression"),
                },
            },
            ArithExpr::Val { val, .. } => Lin {
                vars: BTreeMap::new(),
                const_term: match val {
                    Rational::Finite(fr) => fr,
                    Rational::NegativeInf | Rational::PositiveInf => panic!("Cannot convert infinite rational to linear expression"),
                },
            },
            ArithExpr::Int(v) | ArithExpr::Real(v) => {
                let mut vars = BTreeMap::new();
                vars.insert(v, rug::Rational::from(1));
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
                let mut lin = Lin::from(*e1);
                lin -= Lin::from(*e2);
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
                let mut lin = Lin::from(*e1);
                lin /= Lin::from(*e2);
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
        if other.const_term.cmp0() == Ordering::Equal {
            self.vars.clear();
            self.const_term = rug::Rational::from(0);
            return;
        }
        if !self.vars.is_empty() {
            let factor = other.const_term.clone();
            for coeff in self.vars.values_mut() {
                *coeff *= factor.clone();
            }
            self.const_term *= factor;
        } else {
            let factor = self.const_term.clone();
            self.vars = other.vars;
            for coeff in self.vars.values_mut() {
                *coeff *= factor.clone();
            }
            self.const_term *= factor;
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
