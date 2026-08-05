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

    pub(super) fn get_proxy(&self, expr: &BoolExpr) -> Option<&usize> {
        self.ast_to_sat.get(expr)
    }

    pub(super) fn register_proxy(&mut self, expr: BoolExpr, sat_var: usize) {
        self.ast_to_sat.insert(expr.clone(), sat_var);
        if self.sat_to_ast.len() <= sat_var {
            self.sat_to_ast.resize(sat_var + 1, None);
        }
        self.sat_to_ast[sat_var] = Some(expr);
    }

    pub(super) fn get_ast(&self, lit: crate::smt::sat::Lit) -> Option<&BoolExpr> {
        let var = lit.var();
        if var < self.sat_to_ast.len() { self.sat_to_ast[var].as_ref() } else { None }
    }
}
