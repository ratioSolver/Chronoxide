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
    notified_len: usize,
}

impl Default for SmtSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtSolver {
    pub fn new() -> Self {
        Self {
            registry: ProxyRegistry::new(),
            sat: SatSolver::new(),
            lra: LraTheory::new(),
            notified_len: 0,
        }
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
                self.get_or_create_proxy(bound)
            }
            _ => {
                let slack = self.get_or_create_slack(vars);
                let eps_val = if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                let bound = BoolExpr::Ub(slack, InfRational::new(Rational::Finite(-const_term), eps_val));
                self.get_or_create_proxy(bound)
            }
        }
    }

    fn mk_arith_eq(&mut self, e1: &ArithExpr, e2: &ArithExpr) -> BoolExpr {
        if e1 == e2 {
            return BoolExpr::True;
        }
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(const_term.is_zero()),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), rug::Rational::from(0));
                self.get_or_create_proxy(BoolExpr::ArithEq(var, bound))
            }
            _ => {
                let slack = self.get_or_create_slack(vars);
                let bound = BoolExpr::ArithEq(slack, InfRational::new(Rational::Finite(-const_term), rug::Rational::from(0)));
                self.get_or_create_proxy(bound)
            }
        }
    }

    fn mk_ge(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> BoolExpr {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(if strict { const_term.is_positive() } else { const_term.is_positive() || const_term.is_zero() }),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();
                let eps_val = if strict { rug::Rational::from(1) } else { rug::Rational::from(0) };
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), eps_val / coeff);
                let bound = if coeff.is_positive() { BoolExpr::Lb(var, bound) } else { BoolExpr::Ub(var, bound) };
                self.get_or_create_proxy(bound)
            }
            _ => {
                let slack = self.get_or_create_slack(vars);
                let eps_val = if strict { rug::Rational::from(1) } else { rug::Rational::from(0) };
                let bound = BoolExpr::Lb(slack, InfRational::new(Rational::Finite(-const_term), eps_val));
                self.get_or_create_proxy(bound)
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

    fn get_or_create_slack(&mut self, vars: BTreeMap<usize, rug::Rational>) -> usize {
        if let Some(&slack) = self.lra.lin_to_slack.get(&vars) {
            slack
        } else {
            let slack = self.lra.mk_real();
            self.lra.tableau.insert(slack, vars.clone());

            for &var in vars.keys() {
                self.lra.t_watches[var].insert(slack);
            }

            self.lra.lin_to_slack.insert(vars, slack);
            slack
        }
    }

    fn get_or_create_proxy(&mut self, bound: BoolExpr) -> BoolExpr {
        if let Some(&sat_var) = self.registry.get_proxy(&bound) {
            BoolExpr::Var(sat_var)
        } else {
            let sat_var = self.sat.mk_var();
            self.registry.register_proxy(bound, sat_var);
            BoolExpr::Var(sat_var)
        }
    }

    pub fn propagate(&mut self) -> Result<(), Vec<BoolExpr>> {
        if let Err((bt_level, conflict_clause)) = self.sat.propagate() {
            self.sat.cancel_until(bt_level);
            self.lra.cancel_until(bt_level);
            self.notified_len = self.sat.trail.len();
            let conflict_clause = conflict_clause
                .into_iter()
                .map(|lit| {
                    let var = lit.var();
                    if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(var))) } else { BoolExpr::Var(var) }
                })
                .collect();
            return Err(conflict_clause);
        }

        while self.notified_len < self.sat.trail.len() {
            let lit = self.sat.trail[self.notified_len];
            if let Some(expr) = self.registry.get_ast(lit) {
                if let Err(lemma) = match expr {
                    BoolExpr::Ub(var, bound) => {
                        if !self.lra.set_ub(Some(lit), *var, bound.clone()) {
                            let mut lemma = Vec::with_capacity(2);
                            lemma.push(!lit);
                            if let Some(guard_lit) = self.lra.lbs[*var].0 {
                                lemma.push(!guard_lit);
                            }
                            Err(lemma)
                        } else {
                            Ok(())
                        }
                    }
                    BoolExpr::ArithEq(var, val) => {
                        if !self.lra.set_lb(Some(lit), *var, val.clone()) {
                            let mut lemma = Vec::with_capacity(2);
                            lemma.push(!lit);
                            if let Some(guard_lit) = self.lra.ubs[*var].0 {
                                lemma.push(!guard_lit);
                            }
                            Err(lemma)
                        } else if !self.lra.set_ub(Some(lit), *var, val.clone()) {
                            let mut lemma = Vec::with_capacity(2);
                            lemma.push(!lit);
                            if let Some(guard_lit) = self.lra.lbs[*var].0 {
                                lemma.push(!guard_lit);
                            }
                            Err(lemma)
                        } else {
                            Ok(())
                        }
                    }
                    BoolExpr::Lb(var, bound) => {
                        if !self.lra.set_lb(Some(lit), *var, bound.clone()) {
                            let mut lemma = Vec::with_capacity(2);
                            lemma.push(!lit);
                            if let Some(guard_lit) = self.lra.ubs[*var].0 {
                                lemma.push(!guard_lit);
                            }
                            Err(lemma)
                        } else {
                            Ok(())
                        }
                    }
                    _ => unreachable!("Unexpected BoolExpr in SAT trail: {:?}", expr),
                } {
                    let conflict_clause = lemma
                        .into_iter()
                        .map(|lit| {
                            let var = lit.var();
                            if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(var))) } else { BoolExpr::Var(var) }
                        })
                        .collect();
                    return Err(conflict_clause);
                }
            }
            self.notified_len += 1;
        }

        if let Err(conflict_clause) = self.lra.check() {
            let conflict_clause = conflict_clause
                .into_iter()
                .map(|lit| {
                    let var = lit.var();
                    if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(var))) } else { BoolExpr::Var(var) }
                })
                .collect();
            return Err(conflict_clause);
        }
        Ok(())
    }
}
