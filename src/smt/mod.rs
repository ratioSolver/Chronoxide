pub mod ast;
mod enum_theory;
mod lra_theory;
mod proxy;
mod rational;
mod sat_solver;

use crate::smt::{
    ast::{ArithExpr, BoolExpr, EnumExpr, Expr},
    enum_theory::EnumTheory,
    lra_theory::{LraTheory, SparseRow},
    proxy::{ProxyRegistry, TheoryConstraint},
    rational::{InfRational, Rational},
    sat_solver::{Lit, SatSolver},
};
use rug::Assign;

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

    pub fn new_bool(&mut self) -> BoolExpr {
        BoolExpr::Var(self.sat_solver.mk_var())
    }

    pub fn new_int(&mut self) -> ArithExpr {
        ArithExpr::IntVar(self.lra_theory.mk_int())
    }

    pub fn new_real(&mut self) -> ArithExpr {
        ArithExpr::RealVar(self.lra_theory.mk_real())
    }

    pub fn new_enum(&mut self, domain: impl IntoIterator<Item = i32>) -> EnumExpr {
        EnumExpr::Var(self.enum_theory.mk_var(domain.into_iter().collect()))
    }

    pub fn assert(&mut self, expr: &BoolExpr) -> Result<(), Vec<BoolExpr>> {
        if !self.assert_internal(expr, true) {
            return Err(vec![BoolExpr::False]);
        }
        self.propagate()
    }

    fn assert_internal(&mut self, expr: &BoolExpr, polarity: bool) -> bool {
        match (expr, polarity) {
            (BoolExpr::Not(inner), _) => self.assert_internal(inner, !polarity),
            (BoolExpr::And(args), true) | (BoolExpr::Or(args), false) => {
                for arg in args {
                    if !self.assert_internal(arg, polarity) {
                        return false;
                    }
                }
                true
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
                self.sat_solver.add_clause(clause).is_ok()
            }
            (BoolExpr::Lt(e1, e2), _) | (BoolExpr::Le(e1, e2), _) | (BoolExpr::Ge(e1, e2), _) | (BoolExpr::Gt(e1, e2), _) => {
                let (vars, const_term) = self.diff(e1, e2);
                if vars.is_empty() {
                    let is_sat = match expr {
                        BoolExpr::Lt(_, _) => const_term.is_negative(),
                        BoolExpr::Le(_, _) => const_term.is_negative() || const_term.is_zero(),
                        BoolExpr::Ge(_, _) => !const_term.is_negative(),
                        BoolExpr::Gt(_, _) => const_term.is_positive(),
                        _ => unreachable!(),
                    };
                    return if polarity { is_sat } else { !is_sat };
                }

                let (is_upper_bound, eps_val) = match (expr, polarity) {
                    (BoolExpr::Lt(_, _), true) => (true, rug::Rational::from(-1)),
                    (BoolExpr::Lt(_, _), false) => (false, rug::Rational::from(0)),
                    (BoolExpr::Le(_, _), true) => (true, rug::Rational::from(0)),
                    (BoolExpr::Le(_, _), false) => (false, rug::Rational::from(1)),
                    (BoolExpr::Ge(_, _), true) => (false, rug::Rational::from(0)),
                    (BoolExpr::Ge(_, _), false) => (true, rug::Rational::from(-1)),
                    (BoolExpr::Gt(_, _), true) => (false, rug::Rational::from(1)),
                    (BoolExpr::Gt(_, _), false) => (true, rug::Rational::from(0)),
                    _ => unreachable!(),
                };

                let bound = InfRational::new(Rational::Finite(-const_term.clone()), eps_val);

                if vars.len() == 1 {
                    let (var, coeff) = vars.iter().next().unwrap();
                    let final_bound = bound / coeff.clone();
                    if is_upper_bound == coeff.is_positive() { self.lra_theory.set_ub(None, *var, final_bound).is_ok() } else { self.lra_theory.set_lb(None, *var, final_bound).is_ok() }
                } else {
                    let slack = self.get_or_create_slack(vars);
                    if is_upper_bound { self.lra_theory.set_ub(None, slack, bound).is_ok() } else { self.lra_theory.set_lb(None, slack, bound).is_ok() }
                }
            }
            (BoolExpr::Eq(e1, e2), _) => {
                if let (Expr::Arith(a1), Expr::Arith(a2)) = (&**e1, &**e2) {
                    let (vars, const_term) = self.diff(a1, a2);

                    if vars.is_empty() {
                        let is_sat = const_term.is_zero();
                        return if polarity { is_sat } else { !is_sat };
                    }

                    if polarity {
                        let bound = InfRational::new(Rational::Finite(-const_term.clone()), rug::Rational::from(0));

                        if vars.len() == 1 {
                            let (var, coeff) = vars.iter().next().unwrap();
                            let final_bound = bound / coeff.clone();
                            self.lra_theory.set_lb(None, *var, final_bound.clone()).is_ok() && self.lra_theory.set_ub(None, *var, final_bound).is_ok()
                        } else {
                            let slack = self.get_or_create_slack(vars);
                            self.lra_theory.set_lb(None, slack, bound.clone()).is_ok() && self.lra_theory.set_ub(None, slack, bound).is_ok()
                        }
                    } else {
                        let lt_lit = self.mk_le(a1, a2, true);
                        let gt_lit = self.mk_ge(a1, a2, true);
                        self.sat_solver.add_clause(vec![lt_lit, gt_lit]).is_ok()
                    }
                } else {
                    let mut lit = self.encode_eq(e1, e2);
                    if !polarity {
                        lit = !lit;
                    }
                    self.sat_solver.add_clause(vec![lit]).is_ok()
                }
            }
            _ => {
                let mut lit = self.encode_bool(expr);
                if !polarity {
                    lit = !lit;
                }
                self.sat_solver.add_clause(vec![lit]).is_ok()
            }
        }
    }

    fn encode_bool(&mut self, expr: &BoolExpr) -> Lit {
        match expr {
            BoolExpr::True => self.sat_solver.true_lit(),
            BoolExpr::False => !self.sat_solver.true_lit(),
            BoolExpr::Var(v) => Lit::new(*v, false),
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
            BoolExpr::Eq(e1, e2) => self.encode_eq(e1, e2),
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
                    self.sat_solver.false_lit()
                }
            }
            (EnumExpr::Var(v), EnumExpr::Const(c)) | (EnumExpr::Const(c), EnumExpr::Var(v)) => self.get_or_create_proxy(TheoryConstraint::EnumEq(*v, *c)),
            (EnumExpr::Var(v1), EnumExpr::Var(v2)) => {
                if v1 == v2 {
                    return self.sat_solver.true_lit();
                }

                let domain1 = self.enum_theory.initial_domains[*v1].clone();
                let domain2 = self.enum_theory.initial_domains[*v2].clone();
                let common: Vec<i32> = domain1.intersection(&domain2).copied().collect();

                if common.is_empty() {
                    return self.sat_solver.false_lit();
                }

                let mut lits = Vec::with_capacity(common.len());
                for val in common {
                    let p1 = self.get_or_create_proxy(TheoryConstraint::EnumEq(*v1, val));
                    let p2 = self.get_or_create_proxy(TheoryConstraint::EnumEq(*v2, val));

                    let and_proxy_var = self.sat_solver.mk_var();
                    let and_proxy = Lit::new(and_proxy_var, false);

                    self.sat_solver.add_clause(vec![!and_proxy, p1]).unwrap();
                    self.sat_solver.add_clause(vec![!and_proxy, p2]).unwrap();
                    self.sat_solver.add_clause(vec![!p1, !p2, and_proxy]).unwrap();

                    lits.push(and_proxy);
                }

                let or_proxy_var = self.sat_solver.mk_var();
                let or_proxy = Lit::new(or_proxy_var, false);

                for &lit in &lits {
                    self.sat_solver.add_clause(vec![!lit, or_proxy]).unwrap();
                }

                let mut big_clause = lits;
                big_clause.push(!or_proxy);
                self.sat_solver.add_clause(big_clause).unwrap();

                or_proxy
            }
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
                let (var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) } / coeff);
                let bound = if coeff.is_positive() { TheoryConstraint::LraUb(*var, bound) } else { TheoryConstraint::LraLb(*var, bound) };
                self.get_or_create_proxy(bound)
            }
            _ => {
                let slack = self.get_or_create_slack(vars);
                let bound = TheoryConstraint::LraUb(slack, InfRational::new(Rational::Finite(-const_term), if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) }));
                self.get_or_create_proxy(bound)
            }
        }
    }

    fn mk_arith_eq(&mut self, e1: &ArithExpr, e2: &ArithExpr) -> Lit {
        if e1 == e2 {
            return self.sat_solver.true_lit();
        }

        let le_lit = self.mk_le(e1, e2, false);
        let ge_lit = self.mk_ge(e1, e2, false);

        let proxy_var = self.sat_solver.mk_var();
        let p = Lit::new(proxy_var, false);

        // p -> (x <= y)
        self.sat_solver.add_clause(vec![!p, le_lit]).expect("Failed to add clause");
        // p -> (x >= y)
        self.sat_solver.add_clause(vec![!p, ge_lit]).expect("Failed to add clause");
        // (x <= y) ∧ (x >= y) -> p
        self.sat_solver.add_clause(vec![!le_lit, !ge_lit, p]).expect("Failed to add clause");

        p
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
                let (var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(Rational::Finite(-const_term.clone() / coeff), if strict { rug::Rational::from(1) } else { rug::Rational::from(0) } / coeff);
                let bound = if coeff.is_positive() { TheoryConstraint::LraLb(*var, bound) } else { TheoryConstraint::LraUb(*var, bound) };
                self.get_or_create_proxy(bound)
            }
            _ => {
                let slack = self.get_or_create_slack(vars);
                let bound = TheoryConstraint::LraLb(slack, InfRational::new(Rational::Finite(-const_term), if strict { rug::Rational::from(1) } else { rug::Rational::from(0) }));
                self.get_or_create_proxy(bound)
            }
        }
    }

    fn diff(&self, e1: &ArithExpr, e2: &ArithExpr) -> (SparseRow, rug::Rational) {
        let mut vars = SparseRow::new();
        let mut const_term = rug::Rational::from(0);

        let pos_one = rug::Rational::from(1);
        let neg_one = rug::Rational::from(-1);

        let mut temp = rug::Rational::new();

        self.accumulate_expr(e1, &pos_one, &mut vars, &mut const_term, &mut temp);
        self.accumulate_expr(e2, &neg_one, &mut vars, &mut const_term, &mut temp);

        vars.retain(|_, c| *c != 0);

        (vars, const_term)
    }

    fn accumulate_expr(&self, expr: &ArithExpr, scale: &rug::Rational, vars: &mut SparseRow, const_term: &mut rug::Rational, temp: &mut rug::Rational) {
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

    fn accumulate_var(&self, var: usize, scale: &rug::Rational, vars: &mut SparseRow, temp: &mut rug::Rational) {
        if let Some(basic_row) = self.lra_theory.tableau.get(&var) {
            for (sub_var, sub_coeff) in basic_row.iter() {
                temp.assign(sub_coeff * scale);
                vars.add_coeff(*sub_var, temp);
            }
        } else {
            vars.add_coeff(var, scale);
        }
    }

    fn get_or_create_slack(&mut self, vars: SparseRow) -> usize {
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

    fn get_or_create_proxy(&mut self, constraint: TheoryConstraint) -> Lit {
        if let Some(&sat_var) = self.registry.get_proxy(&constraint) {
            sat_var
        } else {
            let sat_var = self.sat_solver.mk_var();
            self.registry.register(constraint, Lit::new(sat_var, false));
            Lit::new(sat_var, false)
        }
    }

    fn build_conflict(lemma: Vec<Lit>) -> Vec<BoolExpr> {
        lemma
            .into_iter()
            .map(|lit| {
                let var = BoolExpr::Var(lit.var());
                if lit.sign() { BoolExpr::Not(Box::new(var)) } else { var }
            })
            .collect()
    }

    pub fn decide(&mut self, lit: Lit) -> Result<(), Vec<BoolExpr>> {
        self.sat_solver.push();
        self.lra_theory.push();
        self.enum_theory.push();
        self.sat_solver.enqueue_decision(lit);
        self.propagate()
    }

    pub fn propagate(&mut self) -> Result<(), Vec<BoolExpr>> {
        if let Err((bt_level, conflict)) = self.sat_solver.propagate() {
            self.sat_solver.cancel_until(bt_level);
            self.lra_theory.cancel_until(bt_level);
            self.enum_theory.cancel_until(bt_level);
            self.notified_len = self.sat_solver.trail.len();
            return Err(Self::build_conflict(conflict));
        }

        while self.notified_len < self.sat_solver.trail.len() {
            let lit = self.sat_solver.trail[self.notified_len];

            if let Some(constraint) = self.registry.get_constraint(lit).or_else(|| self.registry.get_constraint(!lit)) {
                let theory_result = match (constraint, lit.sign()) {
                    (TheoryConstraint::LraUb(var, bound), false) => self.lra_theory.set_ub(Some(lit), *var, bound.clone()),
                    (TheoryConstraint::LraLb(var, bound), true) => self.lra_theory.set_ub(Some(lit), *var, InfRational::new(bound.rational_part().clone(), if bound.infinitesimal_part().is_positive() { rug::Rational::from(0) } else { rug::Rational::from(-1) })),
                    (TheoryConstraint::LraLb(var, bound), false) => self.lra_theory.set_lb(Some(lit), *var, bound.clone()),
                    (TheoryConstraint::LraUb(var, bound), true) => self.lra_theory.set_lb(Some(lit), *var, InfRational::new(bound.rational_part().clone(), if bound.infinitesimal_part().is_negative() { rug::Rational::from(0) } else { rug::Rational::from(1) })),
                    (TheoryConstraint::EnumEq(var, val), false) => self.enum_theory.set_eq(Some(lit), *var, *val, true),
                    (TheoryConstraint::EnumEq(var, val), true) => self.enum_theory.set_eq(Some(lit), *var, *val, false),
                };

                if let Err(lemma) = theory_result {
                    return Err(Self::build_conflict(lemma));
                }
            }
            self.notified_len += 1;
        }

        if let Err(conflict) = self.lra_theory.check() {
            return Err(Self::build_conflict(conflict));
        }
        Ok(())
    }

    /// Explores the search space to find a valid model or prove UNSAT.
    pub fn check_sat(&mut self) -> bool {
        // 1. Initial root-level propagation
        if self.propagate().is_err() {
            return false; // Immediate UNSAT at level 0
        }

        loop {
            // 2. Find the next unassigned boolean variable
            let mut unassigned_var = None;
            for i in 0..self.sat_solver.assigns.len() {
                if self.sat_solver.value(i).is_none() {
                    unassigned_var = Some(i);
                    break;
                }
            }

            if let Some(var) = unassigned_var {
                // 3. Guess a polarity (e.g., false)
                let lit = Lit::new(var, false);

                // 4. Decide and propagate (SAT + Theory)
                if let Err(lemma) = self.decide(lit) {
                    // We hit a conflict! If we are at the root level, the problem is UNSAT.
                    if self.sat_solver.decision_level() == 0 {
                        return false;
                    }

                    // For simplicity and robustness in this loop, we perform a restart to level 0.
                    // (A production solver would compute the asserting level and jump back to it).
                    self.sat_solver.cancel_until(0);
                    self.lra_theory.cancel_until(0);
                    self.notified_len = self.sat_solver.trail.len();

                    // 5. Learn the theory conflict as a new SAT clause
                    let mut learned_clause = Vec::with_capacity(lemma.len());
                    for expr in lemma {
                        // Re-encode the AST lemma into SAT literals
                        learned_clause.push(self.encode_bool(&expr));
                    }

                    // Add the learned clause. If adding it triggers an immediate conflict, it's UNSAT.
                    if self.sat_solver.add_clause(learned_clause).is_err() {
                        return false;
                    }
                }
            } else {
                // All variables are assigned and no conflicts were found.
                return true; // SAT
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::ast::{add, and, cst_arith, cst_enum, eq_arith, eq_enum, gt, lt, mul, or};
    use tracing::{Level, subscriber};

    #[test]
    fn test_pure_sat_resolution() {
        let mut solver = SmtSolver::new();

        let a = solver.new_bool();
        let b = solver.new_bool();
        let c = solver.new_bool();

        // (A ∨ B) ∧ (¬B ∨ C) ∧ (¬B ∨ ¬C) ∧ (¬A)
        // With ¬A, clause (A ∨ B) forces B; then B forces both C and ¬C.
        let expr = and([or([a.clone(), b.clone()]), or([!b.clone(), c.clone()]), or([!b, !c]), !a]);

        let result = solver.assert(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_early_bounding_unsat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        // x > 10 ∧ x < 5
        let expr = and([gt(x.clone(), cst_arith(10)), lt(x, cst_arith(5))]);

        let result = solver.assert(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_equality_mutually_exclusive() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        // x == 5 ∧ x > 6
        let expr = and([eq_arith(x.clone(), cst_arith(5)), gt(x, cst_arith(6))]);

        let result = solver.assert(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_simplex_system_unsat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();
        let y = solver.new_real();

        // x + y == 10
        let eq_expr = eq_arith(add([x.clone(), y.clone()]), cst_arith(10));
        // x > 6
        let gt_x = gt(x.clone(), cst_arith(6));
        // y > 6
        let gt_y = gt(y.clone(), cst_arith(6));

        let expr = and([eq_expr, gt_x, gt_y]);

        let result = solver.assert(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_simplex_system_sat() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();
        let y = solver.new_real();
        let z = solver.new_real();

        // 2x - y + z == 10
        let exp1 = add([mul([cst_arith(2), x.clone()]), mul([cst_arith(-1), y.clone()]), z.clone()]);
        let eq1 = eq_arith(exp1, cst_arith(10));

        // x > 0, y > 0, z > 0
        let bnd = and([gt(x.clone(), cst_arith(0)), gt(y.clone(), cst_arith(0)), gt(z.clone(), cst_arith(0))]);

        let result = solver.assert(&and([eq1, bnd]));
        assert!(result.is_ok());

        // Triggers the search loop to assign values to the slack variables
        assert!(solver.check_sat(), "The system has valid real solutions and should be SAT");
    }

    #[test]
    fn test_dpllt_backtracking_over_theory() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();

        // (x < 0 ∨ x > 10) ∧ (x > 5) ∧ (x < 15)
        let expr = and([or([lt(x.clone(), cst_arith(0)), gt(x.clone(), cst_arith(10))]), gt(x.clone(), cst_arith(5)), lt(x.clone(), cst_arith(15))]);

        let result = solver.assert(&expr);
        assert!(result.is_ok());

        // check_sat will guess (x < 0), the theory will reject it against (x > 5),
        // the solver will learn the lemma, backtrack, and pick (x > 10) instead.
        assert!(solver.check_sat(), "Solver must backtrack from the x < 0 branch and find the SAT path");
    }

    #[test]
    fn test_dpllt_negated_equality_branching() {
        let mut solver = SmtSolver::new();
        let x = solver.new_real();
        let y = solver.new_real();

        let not_eq = !eq_arith(x.clone(), y.clone());

        let force_lt = and([lt(x.clone(), cst_arith(10)), gt(y.clone(), cst_arith(20))]);

        let expr = and([not_eq, force_lt]);

        let result = solver.assert(&expr);
        assert!(result.is_ok());

        // The solver will branch on the disjunction, fail one path due to LRA bounds,
        // and backtrack to validate the other.
        assert!(solver.check_sat(), "Solver must resolve negated equality branching correctly");
    }

    #[test]
    fn test_enum_basic_sat() {
        let mut solver = SmtSolver::new();
        let e = solver.new_enum(vec![1, 2, 3]);

        let expr = eq_enum(e, cst_enum(2));

        assert!(solver.assert(&expr).is_ok());
        assert!(solver.check_sat(), "The solver should find a valid assignment for the enum variable");
    }

    #[test]
    fn test_enum_out_of_domain_unsat() {
        let mut solver = SmtSolver::new();
        let e = solver.new_enum(vec![1, 2]);

        let expr = eq_enum(e, cst_enum(3));

        let result = solver.assert(&expr);
        assert!(result.is_err(), "The solver should detect that the enum variable cannot take a value outside its domain");
    }

    #[test]
    fn test_enum_exhaustive_denial_integration() {
        let mut solver = SmtSolver::new();
        let e = solver.new_enum(vec![1, 2]);

        // (e != 1) AND (e != 2)
        let expr = and(vec![!(eq_enum(e.clone(), cst_enum(1))), !(eq_enum(e, cst_enum(2)))]);

        assert!(solver.assert(&expr).is_err());
    }

    #[test]
    fn test_enum_var_to_var_equality() {
        let subscriber = tracing_subscriber::fmt().with_max_level(Level::TRACE).finish();
        subscriber::set_global_default(subscriber).expect("Failed to set global default subscriber");

        let mut solver = SmtSolver::new();
        let e1 = solver.new_enum(vec![1, 2, 3]);
        let e2 = solver.new_enum(vec![3, 4, 5]);

        let eq_expr = eq_enum(e1.clone(), e2.clone());

        assert!(solver.assert(&eq_expr).is_ok());
        assert!(solver.check_sat(), "Solver should find a valid assignment for e1 and e2 where they are equal (SAT)");

        let not_3 = !(eq_enum(e1.clone(), cst_enum(3)));
        assert!(solver.assert(&not_3).is_err());
    }

    #[test]
    fn test_enum_dpllt_branching() {
        let mut solver = SmtSolver::new();
        let e = solver.new_enum(vec![1, 2, 3]);

        let expr = and([or([eq_enum(e.clone(), cst_enum(1)), eq_enum(e.clone(), cst_enum(2))]), !(eq_enum(e.clone(), cst_enum(1)))]);

        assert!(solver.assert(&expr).is_ok());

        assert!(solver.check_sat(), "Solver should backtrack and explore e == 2 (SAT)");
    }
}
