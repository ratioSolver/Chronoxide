use std::{fmt, ops};

pub trait Expr: fmt::Display {}

pub trait BoolExpr: Expr {
    fn as_var(&self) -> Option<&Bool> {
        None
    }
    fn as_not(&self) -> Option<&Not> {
        None
    }
    fn as_and(&self) -> Option<&And> {
        None
    }
    fn as_or(&self) -> Option<&Or> {
        None
    }
}

pub struct Bool {
    var: usize,
}

impl Bool {
    pub(super) fn new(var: usize) -> Self {
        Bool { var }
    }
}

impl Expr for Bool {}

impl BoolExpr for Bool {
    fn as_var(&self) -> Option<&Bool> {
        Some(self)
    }
}

impl ops::Deref for Bool {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.var
    }
}

impl fmt::Display for Bool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.var)
    }
}

pub struct Not {
    expr: Box<dyn BoolExpr>,
}

impl Not {
    pub fn new(expr: Box<dyn BoolExpr>) -> Self {
        Not { expr }
    }
}

impl Expr for Not {}

impl BoolExpr for Not {
    fn as_not(&self) -> Option<&Not> {
        Some(self)
    }
}

impl fmt::Display for Not {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "¬{}", self.expr)
    }
}

pub struct And {
    exprs: Vec<Box<dyn BoolExpr>>,
}

impl And {
    pub fn new(exprs: impl IntoIterator<Item = Box<dyn BoolExpr>>) -> Self {
        let exprs: Vec<Box<dyn BoolExpr>> = exprs.into_iter().collect();
        assert!(!exprs.is_empty(), "And expression must have at least one operand");
        And { exprs }
    }
}

impl Expr for And {}

impl BoolExpr for And {
    fn as_and(&self) -> Option<&And> {
        Some(self)
    }
}

impl fmt::Display for And {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", self.exprs.iter().fold(String::new(), |acc, expr| { if acc.is_empty() { format!("{}", expr) } else { format!("{} ∧ {}", acc, expr) } }))
    }
}

pub struct Or {
    exprs: Vec<Box<dyn BoolExpr>>,
}

impl Or {
    pub fn new(exprs: impl IntoIterator<Item = Box<dyn BoolExpr>>) -> Self {
        let exprs: Vec<Box<dyn BoolExpr>> = exprs.into_iter().collect();
        assert!(!exprs.is_empty(), "Or expression must have at least one operand");
        Or { exprs }
    }
}

impl Expr for Or {}

impl BoolExpr for Or {
    fn as_or(&self) -> Option<&Or> {
        Some(self)
    }
}

impl fmt::Display for Or {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", self.exprs.iter().fold(String::new(), |acc, expr| { if acc.is_empty() { format!("{}", expr) } else { format!("{} ∨ {}", acc, expr) } }))
    }
}

pub trait ArithExpr: Expr {}

pub trait IntExpr: ArithExpr {}

pub struct Int {
    var: usize,
}

impl Int {
    pub(super) fn new(var: usize) -> Self {
        Int { var }
    }
}

impl Expr for Int {}

impl ArithExpr for Int {}

impl IntExpr for Int {}

impl ops::Deref for Int {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.var
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "i{}", self.var)
    }
}

pub trait RealExpr: ArithExpr {}

pub struct Real {
    var: usize,
}

impl Real {
    pub(super) fn new(var: usize) -> Self {
        Real { var }
    }
}

impl Expr for Real {}

impl ArithExpr for Real {}

impl RealExpr for Real {}

impl ops::Deref for Real {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.var
    }
}

impl fmt::Display for Real {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.var)
    }
}
