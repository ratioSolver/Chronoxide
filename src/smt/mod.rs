pub mod ast;
mod enum_theory;
mod lra_theory;
mod proxy;
mod rational;
mod sat_solver;

use crate::smt::{
    ast::{ArithExpr, BoolExpr, EnumExpr, Expr},
    enum_theory::EnumTheory,
    lra_theory::LraTheory,
    proxy::ProxyRegistry,
    rational::{InfRational, Rational},
    sat_solver::{Lit, SatSolver},
};
use rug::Assign;
use std::collections::BTreeMap;

pub struct SmtSolver {
    registry: ProxyRegistry,
    sat_solver: SatSolver,
    lra_theory: LraTheory,
    enum_theory: EnumTheory,
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
            sat_solver: SatSolver::new(),
            lra_theory: LraTheory::new(),
            enum_theory: EnumTheory::new(),
            notified_len: 0,
        }
    }

    pub fn assert(&mut self, expr: &BoolExpr) -> Result<(), Vec<BoolExpr>> {
        self.assert_internal(expr, true)?;
        self.propagate()
    }

    pub fn decide(&mut self, lit: Lit) -> Result<(), Vec<BoolExpr>> {
        self.sat_solver.push();
        self.lra_theory.push();
        self.sat_solver.enqueue_decision(lit);
        self.propagate()
    }

    fn assert_internal(&mut self, expr: &BoolExpr, polarity: bool) -> Result<(), Vec<BoolExpr>> {
        match (expr, polarity) {
            (BoolExpr::Not(inner), _) => self.assert_internal(inner, !polarity),
            (BoolExpr::And(args), true) | (BoolExpr::Or(args), false) => {
                for arg in args {
                    self.assert_internal(arg, polarity)?;
                }
                Ok(())
            }
            (BoolExpr::Or(args), true) | (BoolExpr::And(args), false) => {
                let mut clause = Vec::with_capacity(args.len());
                for arg in args {
                    let mut lit = self.encode_bool(arg);
                    if !polarity {
                        lit = !lit;
                    }
                    clause.push(lit);
                }

                if self.sat_solver.add_clause(clause).is_err() {
                    return Err(vec![BoolExpr::False]);
                }
                Ok(())
            }
            (BoolExpr::Lt(e1, e2), _) | (BoolExpr::Le(e1, e2), _) | (BoolExpr::Ge(e1, e2), _) | (BoolExpr::Gt(e1, e2), _) => {
                let (vars, const_term) = self.diff(e1, e2);
                if vars.is_empty() {
                    let is_sat = match expr {
                        BoolExpr::Lt(_, _) => const_term.is_negative(),
                        BoolExpr::Le(_, _) => const_term.is_negative() || const_term.is_zero(),
                        BoolExpr::Ge(_, _) => !const_term.is_negative(), // >= 0
                        BoolExpr::Gt(_, _) => const_term.is_positive(),
                        _ => unreachable!(),
                    };
                    let final_sat = if polarity { is_sat } else { !is_sat };
                    return if final_sat { Ok(()) } else { Err(vec![BoolExpr::False]) };
                }
                let (is_upper_bound, eps_val) = match (expr, polarity) {
                    // Lt (< 0)
                    (BoolExpr::Lt(_, _), true) => (true, rug::Rational::from(-1)),
                    (BoolExpr::Lt(_, _), false) => (false, rug::Rational::from(0)), // !(x < y) => x >= y

                    // Le (<= 0)
                    (BoolExpr::Le(_, _), true) => (true, rug::Rational::from(0)),
                    (BoolExpr::Le(_, _), false) => (false, rug::Rational::from(1)), // !(x <= y) => x > y

                    // Ge (>= 0)
                    (BoolExpr::Ge(_, _), true) => (false, rug::Rational::from(0)),
                    (BoolExpr::Ge(_, _), false) => (true, rug::Rational::from(-1)), // !(x >= y) => x < y

                    // Gt (> 0)
                    (BoolExpr::Gt(_, _), true) => (false, rug::Rational::from(1)),
                    (BoolExpr::Gt(_, _), false) => (true, rug::Rational::from(0)), // !(x > y) => x <= y

                    _ => unreachable!(),
                };
                if vars.len() == 1 {
                    let (&var, coeff) = vars.iter().next().unwrap();
                    let bound = InfRational::new(Rational::Finite((-const_term.clone()) / coeff), eps_val / coeff);
                    let expr = if is_upper_bound == coeff.is_positive() { BoolExpr::Ub(var, bound) } else { BoolExpr::Lb(var, bound) };
                    self.assert_internal(&expr, true)
                } else {
                    let slack = self.get_or_create_slack(vars);
                    let bound = InfRational::new(Rational::Finite(-const_term), eps_val);
                    let expr = if is_upper_bound { BoolExpr::Ub(slack, bound) } else { BoolExpr::Lb(slack, bound) };
                    self.assert_internal(&expr, true)
                }
            }
            (BoolExpr::Lb(var, bound), true) => {
                if !self.lra_theory.set_lb(None, *var, bound.clone()) {
                    return Err(vec![BoolExpr::False]);
                }
                Ok(())
            }
            (BoolExpr::Ub(var, bound), true) => {
                if !self.lra_theory.set_ub(None, *var, bound.clone()) {
                    return Err(vec![BoolExpr::False]);
                }
                Ok(())
            }
            (BoolExpr::ArithEq(var, val), true) => {
                if !self.lra_theory.set_lb(None, *var, val.clone()) || !self.lra_theory.set_ub(None, *var, val.clone()) {
                    return Err(vec![BoolExpr::False]);
                }
                Ok(())
            }
            (BoolExpr::Eq(e1, e2), _) => {
                if let (Expr::Arith(a1), Expr::Arith(a2)) = (&**e1, &**e2) {
                    let (vars, const_term) = self.diff(a1, a2);

                    if vars.is_empty() {
                        let is_sat = const_term.is_zero();
                        let final_sat = if polarity { is_sat } else { !is_sat };
                        return if final_sat { Ok(()) } else { Err(vec![BoolExpr::False]) };
                    }

                    if polarity {
                        if vars.len() == 1 {
                            let (&var, coeff) = vars.iter().next().unwrap();
                            let bound = InfRational::new(Rational::Finite((-const_term) / coeff), rug::Rational::from(0));
                            self.assert_internal(&BoolExpr::ArithEq(var, bound), true)
                        } else {
                            let slack = self.get_or_create_slack(vars);
                            let bound = InfRational::new(Rational::Finite(-const_term), rug::Rational::from(0));
                            self.assert_internal(&BoolExpr::ArithEq(slack, bound), true)
                        }
                    } else {
                        let lt_lit = self.mk_le(a1, a2, true);
                        let gt_lit = self.mk_ge(a1, a2, true);

                        if self.sat_solver.add_clause(vec![lt_lit, gt_lit]).is_err() {
                            return Err(vec![BoolExpr::False]);
                        }
                        Ok(())
                    }
                } else {
                    let mut lit = self.encode_eq(e1, e2);
                    if !polarity {
                        lit = !lit;
                    }
                    if self.sat_solver.add_clause(vec![lit]).is_err() {
                        return Err(vec![BoolExpr::False]);
                    }
                    Ok(())
                }
            }
            _ => {
                let mut lit = self.encode_bool(expr);
                if !polarity {
                    lit = !lit;
                }
                if self.sat_solver.add_clause(vec![lit]).is_err() {
                    return Err(vec![BoolExpr::False]);
                }
                Ok(())
            }
        }
    }

    fn encode_bool(&mut self, expr: &BoolExpr) -> Lit {
        match expr {
            BoolExpr::True => self.sat_solver.true_lit(),
            BoolExpr::False => !self.sat_solver.true_lit(),
            BoolExpr::Var(v) => Lit::new(*v, true),
            BoolExpr::Not(inner) => !self.encode_bool(inner),
            BoolExpr::And(terms) => {
                let mut lits = Vec::with_capacity(terms.len());
                for term in terms {
                    lits.push(self.encode_bool(term));
                }

                let proxy_var = self.sat_solver.mk_var();
                let proxy_lit = Lit::new(proxy_var, true);

                for &lit in &lits {
                    self.sat_solver.add_clause(vec![!proxy_lit, lit]).expect("Failed to add clause");
                }

                let mut big_clause: Vec<Lit> = lits.into_iter().map(|l| !l).collect();
                big_clause.push(proxy_lit);
                self.sat_solver.add_clause(big_clause).expect("Failed to add clause");

                proxy_lit
            }
            BoolExpr::Or(terms) => {
                let mut lits = Vec::with_capacity(terms.len());
                for term in terms {
                    lits.push(self.encode_bool(term));
                }

                let proxy_var = self.sat_solver.mk_var();
                let proxy_lit = Lit::new(proxy_var, true);

                for &lit in &lits {
                    self.sat_solver.add_clause(vec![!lit, proxy_lit]).expect("Failed to add clause");
                }

                let mut big_clause = lits;
                big_clause.push(!proxy_lit);
                self.sat_solver.add_clause(big_clause).expect("Failed to add clause");

                proxy_lit
            }
            BoolExpr::Lt(e1, e2) => self.mk_le(e1, e2, true),
            BoolExpr::Le(e1, e2) => self.mk_le(e1, e2, false),
            BoolExpr::Ge(e1, e2) => self.mk_ge(e1, e2, false),
            BoolExpr::Gt(e1, e2) => self.mk_ge(e1, e2, true),
            BoolExpr::Eq(e1, e2) => {
                self.encode_eq(e1, e2) // Vedi spiegazione sotto
            }
            BoolExpr::Lb(_, _) | BoolExpr::Ub(_, _) | BoolExpr::ArithEq(_, _) => self.get_or_create_proxy(expr.clone()),
        }
    }

    fn encode_eq(&mut self, expr1: &Expr, expr2: &Expr) -> Lit {
        match (expr1, expr2) {
            (Expr::Arith(a1), Expr::Arith(a2)) => self.mk_arith_eq(a1, a2),
            (Expr::Bool(b1), Expr::Bool(b2)) => {
                let l1 = self.encode_bool(b1);
                let l2 = self.encode_bool(b2);
                let proxy_var = self.sat_solver.mk_var();
                let p = Lit::new(proxy_var, true);

                self.sat_solver.add_clause(vec![!p, l1, !l2]).expect("Failed to add clause");
                self.sat_solver.add_clause(vec![!p, !l1, l2]).expect("Failed to add clause");
                self.sat_solver.add_clause(vec![p, l1, l2]).expect("Failed to add clause");
                self.sat_solver.add_clause(vec![p, !l1, !l2]).expect("Failed to add clause");

                p
            }
            (Expr::Enum(e1), Expr::Enum(e2)) => self.mk_enum_eq(e1, e2),
            _ => panic!("Type mismatch in Eq: cannot compare different domains.\nLeft: {:?}\nRight: {:?}", expr1, expr2),
        }
    }

    fn mk_enum_eq(&mut self, e1: &EnumExpr, e2: &EnumExpr) -> Lit {
        match (e1, e2) {
            (EnumExpr::Const(c1), EnumExpr::Const(c2)) => {
                if c1 == c2 {
                    self.sat_solver.true_lit()
                } else {
                    !self.sat_solver.true_lit()
                }
            }

            (EnumExpr::Var(v), EnumExpr::Const(c)) | (EnumExpr::Const(c), EnumExpr::Var(v)) => {
                let proxy_var = self.get_enum_proxy(*v, *c);
                Lit::new(proxy_var, true)
            }

            (EnumExpr::Var(v1), EnumExpr::Var(v2)) => {
                if v1 == v2 {
                    return self.sat_solver.true_lit();
                }

                let domain1 = self.enum_theory.domains.get(v1).cloned().unwrap_or_default();
                let domain2 = self.enum_theory.domains.get(v2).cloned().unwrap_or_default();

                let common_values: Vec<i32> = domain1.intersection(&domain2).copied().collect();

                if common_values.is_empty() {
                    return !self.sat_solver.true_lit();
                }

                let mut or_terms = Vec::with_capacity(common_values.len());
                for val in common_values {
                    let p1 = self.get_enum_proxy(*v1, val);
                    let p2 = self.get_enum_proxy(*v2, val);

                    or_terms.push(BoolExpr::And(vec![BoolExpr::Var(p1), BoolExpr::Var(p2)]));
                }

                let or_expr = BoolExpr::Or(or_terms);
                self.encode_bool(&or_expr)
            }
        }
    }

    fn get_enum_proxy(&mut self, var: usize, val: i32) -> usize {
        self.enum_theory.register_domain_value(var, val);

        if let Some(&proxy) = self.enum_theory.var_eq_const_proxies.get(&(var, val)) {
            proxy
        } else {
            let new_proxy = self.sat_solver.mk_var();
            self.enum_theory.var_eq_const_proxies.insert((var, val), new_proxy);
            new_proxy
        }
    }

    fn mk_le(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> Lit {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => {
                if if strict { const_term.is_negative() } else { const_term.is_negative() || const_term.is_zero() } {
                    self.sat_solver.true_lit()
                } else {
                    self.sat_solver.false_lit()
                }
            }
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) } / coeff);
                let bound = if coeff.is_positive() { BoolExpr::Ub(var, bound) } else { BoolExpr::Lb(var, bound) };
                self.get_or_create_proxy(bound)
            }
            _ => {
                let slack = self.get_or_create_slack(vars);
                let bound = BoolExpr::Ub(slack, InfRational::new(Rational::Finite(-const_term), if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) }));
                self.get_or_create_proxy(bound)
            }
        }
    }

    fn mk_arith_eq(&mut self, e1: &ArithExpr, e2: &ArithExpr) -> Lit {
        if e1 == e2 {
            return self.sat_solver.true_lit();
        }
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => {
                if const_term.is_zero() {
                    self.sat_solver.true_lit()
                } else {
                    self.sat_solver.false_lit()
                }
            }
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

    fn mk_ge(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> Lit {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => {
                if if strict { const_term.is_positive() } else { const_term.is_positive() || const_term.is_zero() } {
                    self.sat_solver.true_lit()
                } else {
                    self.sat_solver.false_lit()
                }
            }
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), if strict { rug::Rational::from(1) } else { rug::Rational::from(0) } / coeff);
                let bound = if coeff.is_positive() { BoolExpr::Lb(var, bound) } else { BoolExpr::Ub(var, bound) };
                self.get_or_create_proxy(bound)
            }
            _ => {
                let slack = self.get_or_create_slack(vars);
                let bound = BoolExpr::Lb(slack, InfRational::new(Rational::Finite(-const_term), if strict { rug::Rational::from(1) } else { rug::Rational::from(0) }));
                self.get_or_create_proxy(bound)
            }
        }
    }

    fn diff(&self, e1: &ArithExpr, e2: &ArithExpr) -> (BTreeMap<usize, rug::Rational>, rug::Rational) {
        let mut vars = BTreeMap::new();
        let mut const_term = rug::Rational::from(0);

        let pos_one = rug::Rational::from(1);
        let neg_one = rug::Rational::from(-1);

        let mut temp = rug::Rational::new();

        self.accumulate_expr(e1, &pos_one, &mut vars, &mut const_term, &mut temp);
        self.accumulate_expr(e2, &neg_one, &mut vars, &mut const_term, &mut temp);

        vars.retain(|_, c| *c != 0);

        (vars, const_term)
    }

    fn accumulate_expr(&self, expr: &ArithExpr, scale: &rug::Rational, vars: &mut BTreeMap<usize, rug::Rational>, const_term: &mut rug::Rational, temp: &mut rug::Rational) {
        match expr {
            ArithExpr::Const(c) => {
                temp.assign(c * scale);
                *const_term += &*temp;
            }
            ArithExpr::IntVar(var) | ArithExpr::RealVar(var) => {
                self.accumulate_var(*var, scale, vars, temp);
            }
            ArithExpr::Add(terms) => {
                for term in terms {
                    self.accumulate_expr(term, scale, vars, const_term, temp);
                }
            }
            ArithExpr::Mul(terms) => {
                if terms.len() != 2 {
                    panic!("Only binary multiplication is supported in linear arithmetic");
                }
                let (first, second) = (&terms[0], &terms[1]);

                // Ricorsione intelligente: accettiamo (Costante * SottoEspressione)
                match (first, second) {
                    (ArithExpr::Const(c), sub_expr) | (sub_expr, ArithExpr::Const(c)) => {
                        let mut new_scale = rug::Rational::new();
                        new_scale.assign(c * scale);
                        self.accumulate_expr(sub_expr, &new_scale, vars, const_term, temp);
                    }
                    _ => {
                        panic!("Non-linear arithmetic: multiplication between two non-constant expressions is not supported");
                    }
                }
            }
            ArithExpr::Div(numerator, denominator) => {
                // Il denominatore DEVE essere una costante per preservare la linearità
                if let ArithExpr::Const(c) = &**denominator {
                    if c.is_zero() {
                        panic!("Division by zero detected in AST");
                    }
                    let mut div_scale = rug::Rational::new();
                    div_scale.assign(scale / c);
                    self.accumulate_expr(numerator, &div_scale, vars, const_term, temp);
                } else {
                    panic!("Non-linear arithmetic: division by a non-constant expression is not supported");
                }
            }
            ArithExpr::Neg(sub_expr) => {
                let mut neg_scale = rug::Rational::new();
                neg_scale.assign(scale * -1);
                self.accumulate_expr(sub_expr, &neg_scale, vars, const_term, temp);
            }
        }
    }

    fn accumulate_var(&self, var: usize, scale: &rug::Rational, vars: &mut BTreeMap<usize, rug::Rational>, temp: &mut rug::Rational) {
        if let Some(basic_row) = self.lra_theory.tableau.get(&var) {
            for (&sub_var, sub_coeff) in basic_row {
                let entry = vars.entry(sub_var).or_insert_with(|| rug::Rational::from(0));
                temp.assign(sub_coeff * scale);
                *entry += &*temp;
            }
        } else {
            *vars.entry(var).or_insert_with(|| rug::Rational::from(0)) += scale;
        }
    }

    fn get_or_create_slack(&mut self, vars: BTreeMap<usize, rug::Rational>) -> usize {
        if let Some(&slack) = self.lra_theory.lin_to_slack.get(&vars) {
            slack
        } else {
            let slack = self.lra_theory.mk_real();
            self.lra_theory.tableau.insert(slack, vars.clone());

            for &var in vars.keys() {
                self.lra_theory.t_watches[var].insert(slack);
            }

            self.lra_theory.lin_to_slack.insert(vars, slack);
            slack
        }
    }

    fn get_or_create_proxy(&mut self, bound: BoolExpr) -> Lit {
        if let Some(&sat_var) = self.registry.get_proxy(&bound) {
            Lit::new(sat_var, false)
        } else {
            let sat_var = self.sat_solver.mk_var();
            self.registry.register_proxy(bound, sat_var);
            Lit::new(sat_var, false)
        }
    }

    pub fn propagate(&mut self) -> Result<(), Vec<BoolExpr>> {
        if let Err((bt_level, conflict_clause)) = self.sat_solver.propagate() {
            self.sat_solver.cancel_until(bt_level);
            self.lra_theory.cancel_until(bt_level);
            self.notified_len = self.sat_solver.trail.len();
            let conflict_clause = conflict_clause
                .into_iter()
                .map(|lit| {
                    let var = lit.var();
                    if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(var))) } else { BoolExpr::Var(var) }
                })
                .collect();
            return Err(conflict_clause);
        }

        while self.notified_len < self.sat_solver.trail.len() {
            let lit = self.sat_solver.trail[self.notified_len];
            if let Some(expr) = self.registry.get_ast(lit)
                && let Err(lemma) = match expr {
                    BoolExpr::Ub(var, bound) => {
                        if !self.lra_theory.set_ub(Some(lit), *var, bound.clone()) {
                            let mut lemma = Vec::with_capacity(2);
                            lemma.push(!lit);
                            if let Some(guard_lit) = self.lra_theory.lbs[*var].0 {
                                lemma.push(!guard_lit);
                            }
                            Err(lemma)
                        } else {
                            Ok(())
                        }
                    }
                    BoolExpr::ArithEq(var, val) => {
                        if !self.lra_theory.set_lb(Some(lit), *var, val.clone()) {
                            let mut lemma = Vec::with_capacity(2);
                            lemma.push(!lit);
                            if let Some(guard_lit) = self.lra_theory.ubs[*var].0 {
                                lemma.push(!guard_lit);
                            }
                            Err(lemma)
                        } else if !self.lra_theory.set_ub(Some(lit), *var, val.clone()) {
                            let mut lemma = Vec::with_capacity(2);
                            lemma.push(!lit);
                            if let Some(guard_lit) = self.lra_theory.lbs[*var].0 {
                                lemma.push(!guard_lit);
                            }
                            Err(lemma)
                        } else {
                            Ok(())
                        }
                    }
                    BoolExpr::Lb(var, bound) => {
                        if !self.lra_theory.set_lb(Some(lit), *var, bound.clone()) {
                            let mut lemma = Vec::with_capacity(2);
                            lemma.push(!lit);
                            if let Some(guard_lit) = self.lra_theory.ubs[*var].0 {
                                lemma.push(!guard_lit);
                            }
                            Err(lemma)
                        } else {
                            Ok(())
                        }
                    }
                    _ => unreachable!("Unexpected BoolExpr in SAT trail: {:?}", expr),
                }
            {
                let conflict_clause = lemma
                    .into_iter()
                    .map(|lit| {
                        let var = lit.var();
                        if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(var))) } else { BoolExpr::Var(var) }
                    })
                    .collect();
                return Err(conflict_clause);
            }
            self.notified_len += 1;
        }

        if let Err(conflict_clause) = self.lra_theory.check() {
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
