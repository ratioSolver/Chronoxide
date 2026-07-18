use std::{fmt, ops};

pub trait Node: fmt::Display {}

pub trait Bool: Node {
    fn as_var(&self) -> Option<&BoolVar> {
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

pub struct BoolVar {
    var: usize,
}

impl BoolVar {
    pub(super) fn new(var: usize) -> Self {
        BoolVar { var }
    }
}

impl Node for BoolVar {}

impl Bool for BoolVar {
    fn as_var(&self) -> Option<&BoolVar> {
        Some(self)
    }
}

impl ops::Deref for BoolVar {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.var
    }
}

impl fmt::Display for BoolVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.var)
    }
}

pub struct Not {
    expr: Box<dyn Bool>,
}

impl Not {
    pub fn new(expr: Box<dyn Bool>) -> Self {
        Not { expr }
    }
}

impl Node for Not {}

impl Bool for Not {
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
    exprs: Vec<Box<dyn Bool>>,
}

impl And {
    pub fn new(exprs: impl IntoIterator<Item = Box<dyn Bool>>) -> Self {
        let exprs: Vec<Box<dyn Bool>> = exprs.into_iter().collect();
        assert!(!exprs.is_empty(), "And expression must have at least one operand");
        And { exprs }
    }
}

impl Node for And {}

impl Bool for And {
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
    exprs: Vec<Box<dyn Bool>>,
}

impl Or {
    pub fn new(exprs: impl IntoIterator<Item = Box<dyn Bool>>) -> Self {
        let exprs: Vec<Box<dyn Bool>> = exprs.into_iter().collect();
        assert!(!exprs.is_empty(), "Or expression must have at least one operand");
        Or { exprs }
    }
}

impl Node for Or {}

impl Bool for Or {
    fn as_or(&self) -> Option<&Or> {
        Some(self)
    }
}

impl fmt::Display for Or {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", self.exprs.iter().fold(String::new(), |acc, expr| { if acc.is_empty() { format!("{}", expr) } else { format!("{} ∨ {}", acc, expr) } }))
    }
}
