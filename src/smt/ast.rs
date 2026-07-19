use crate::smt::rational::Rational;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Bool(BoolExpr),
    Arith(ArithExpr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    Lit(LBool),
    Var(usize),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Lt(Box<ArithExpr>, Box<ArithExpr>),
    Le(Box<ArithExpr>, Box<ArithExpr>),
    Eq(Box<Expr>, Box<Expr>),
    Ge(Box<ArithExpr>, Box<ArithExpr>),
    Gt(Box<ArithExpr>, Box<ArithExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArithExpr {
    Lit(Rational),
    Val { lb: Rational, val: Rational, ub: Rational }, // Represents a value with lower and upper bounds
    Int(usize),
    Real(usize),
    Add(Vec<ArithExpr>),
    Sub(Box<ArithExpr>, Box<ArithExpr>),
    Mul(Vec<ArithExpr>),
    Div(Box<ArithExpr>, Box<ArithExpr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::Arith(a) => write!(f, "{}", a),
        }
    }
}

impl fmt::Display for BoolExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BoolExpr::Lit(l) => write!(f, "{}", l),
            BoolExpr::Var(v) => write!(f, "b{}", v),
            BoolExpr::Not(e) => write!(f, "¬{}", e),
            BoolExpr::And(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" ∧ "))
            }
            BoolExpr::Or(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" ∨ "))
            }
            BoolExpr::Lt(a1, a2) => write!(f, "{} < {}", a1, a2),
            BoolExpr::Le(a1, a2) => write!(f, "{} ≤ {}", a1, a2),
            BoolExpr::Eq(e1, e2) => write!(f, "{} = {}", e1, e2),
            BoolExpr::Ge(a1, a2) => write!(f, "{} ≥ {}", a1, a2),
            BoolExpr::Gt(a1, a2) => write!(f, "{} > {}", a1, a2),
        }
    }
}

impl fmt::Display for ArithExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArithExpr::Lit(r) => write!(f, "{}", r),
            ArithExpr::Val { lb, val, ub } => write!(f, "{} ∈ [{} , {}]", val, lb, ub),
            ArithExpr::Int(n) => write!(f, "{}", n),
            ArithExpr::Real(n) => write!(f, "{}", n),
            ArithExpr::Add(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" + "))
            }
            ArithExpr::Sub(e1, e2) => write!(f, "({} - {})", e1, e2),
            ArithExpr::Mul(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" * "))
            }
            ArithExpr::Div(e1, e2) => write!(f, "({} / {})", e1, e2),
        }
    }
}
