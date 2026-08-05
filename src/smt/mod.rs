pub mod ast;
mod lin;
mod lra;
mod proxy;
mod rational;
mod sat;

use std::collections::BTreeMap;

use crate::smt::{
    ast::{ArithExpr, BoolExpr},
    lin::Lin,
    lra::LraTheory,
    proxy::ProxyRegistry,
    rational::{InfRational, Rational},
    sat::SatSolver,
};

pub struct SmtSolver {
    registry: ProxyRegistry,
    sat: SatSolver,
    lra: LraTheory,
}

impl Default for SmtSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtSolver {
    pub fn new() -> Self {
        Self { registry: ProxyRegistry::new(), sat: SatSolver::new(), lra: LraTheory::new() }
    }

    fn mk_le(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> BoolExpr {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(if strict { const_term.is_negative() } else { const_term.is_negative() || const_term.is_zero() }),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();

                let eps_val = if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), eps_val / coeff);
                let bound = if coeff.is_positive() { BoolExpr::Ub(var, bound) } else { BoolExpr::Lb(var, bound) };
                if let Some(&sat_var) = self.registry.get_proxy(&bound) {
                    BoolExpr::Var(sat_var)
                } else {
                    let sat_var = self.sat.mk_var();
                    self.registry.register_proxy(bound, sat_var);
                    BoolExpr::Var(sat_var)
                }
            }
            _ => {
                let slack = if let Some(&slack) = self.lra.lin_to_slack.get(&vars) {
                    slack
                } else {
                    let slack = self.lra.mk_real();
                    self.lra.tableau.insert(slack, vars.clone());
                    self.lra.lin_to_slack.insert(vars, slack);
                    slack
                };

                let eps_val = if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                let bound = BoolExpr::Ub(slack, InfRational::new(Rational::Finite(-const_term), eps_val));
                if let Some(&sat_var) = self.registry.get_proxy(&bound) {
                    BoolExpr::Var(sat_var)
                } else {
                    let sat_var = self.sat.mk_var();
                    self.registry.register_proxy(bound, sat_var);
                    BoolExpr::Var(sat_var)
                }
            }
        }
    }

    fn diff(&self, e1: &ArithExpr, e2: &ArithExpr) -> (BTreeMap<usize, rug::Rational>, rug::Rational) {
        let diff = Lin::from(e1) - Lin::from(e2);
        let mut vars = BTreeMap::new();

        for (var, coeff) in diff.vars {
            if let Some(basic) = self.lra.tableau.get(&var) {
                for (&sub_var, sub_coeff) in basic {
                    *vars.entry(sub_var).or_insert_with(|| rug::Rational::from(0)) += coeff.clone() * sub_coeff;
                }
            } else {
                *vars.entry(var).or_insert_with(|| rug::Rational::from(0)) += coeff;
            }
        }

        vars.retain(|_, c| *c != 0);
        (vars, diff.const_term)
    }
}
