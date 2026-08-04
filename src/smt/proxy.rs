use crate::smt::ast::BoolExpr;
use std::collections::HashMap;

pub(super) struct ProxyRegistry {
    sat_to_ast: Vec<Option<BoolExpr>>,    // Map from SAT variable index to its corresponding AST expression
    ast_to_sat: HashMap<BoolExpr, usize>, // Map from AST expression to its corresponding SAT variable index
}

impl ProxyRegistry {
    pub(super) fn new() -> Self {
        ProxyRegistry { sat_to_ast: Vec::new(), ast_to_sat: HashMap::new() }
    }
}
