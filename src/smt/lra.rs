use crate::smt::{
    Lin,
    ast::{ArithExpr, BoolExpr},
    rational::{InfRational, Rational},
};
use std::collections::{BTreeMap, HashMap};

pub(super) struct LRA {
    ints: Vec<bool>,                                              // Distinguish between integer and real variables
    reals: Vec<Rational>,                                         // Current assignments of real variables
    lbs: Vec<Rational>,                                           // Current assignments of lower bounds
    ubs: Vec<Rational>,                                           // Current assignments of upper bounds
    lin_to_slack: HashMap<BTreeMap<usize, rug::Rational>, usize>, // Mapping from linear constraints to their corresponding slack variable
    tableau: BTreeMap<usize, BTreeMap<usize, rug::Rational>>,     // Tableau for linear constraints
    bound_trail: Vec<BoolExpr>,                                   // Trail of bound updates for backtracking
    trail_lim: Vec<usize>,                                        // Indices in the trail where decisions were made
}

impl LRA {
    pub(super) fn new() -> Self {
        LRA {
            ints: Vec::new(),
            reals: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            lin_to_slack: HashMap::new(),
            tableau: BTreeMap::new(),
            bound_trail: Vec::new(),
            trail_lim: Vec::new(),
        }
    }

    pub(super) fn mk_int(&mut self) -> usize {
        let var_index = self.ints.len();
        self.ints.push(true);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        var_index
    }

    pub(super) fn mk_real(&mut self) -> usize {
        let var_index = self.reals.len();
        self.ints.push(false);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        var_index
    }

    pub(super) fn eval_arith(&self, expr: &ArithExpr) -> (Rational, Rational, Rational) {
        match expr {
            ArithExpr::Const(r) => (r.clone(), r.clone(), r.clone()),
            ArithExpr::IntVar(v) => (self.lbs[*v].clone(), self.reals[*v].clone(), self.ubs[*v].clone()),
            ArithExpr::RealVar(v) => (self.lbs[*v].clone(), self.reals[*v].clone(), self.ubs[*v].clone()),
            ArithExpr::Add(add) => {
                let mut lb = Rational::Finite(rug::Rational::from(0));
                let mut res = Rational::Finite(rug::Rational::from(0));
                let mut ub = Rational::Finite(rug::Rational::from(0));
                for sub_expr in add {
                    let (sub_lb, sub_res, sub_ub) = self.eval_arith(sub_expr);
                    lb += sub_lb;
                    res += sub_res;
                    ub += sub_ub;
                }
                (lb, res, ub)
            }
            ArithExpr::Sub(e1, e2) => {
                let (lb1, res1, ub1) = self.eval_arith(e1);
                let (lb2, res2, ub2) = self.eval_arith(e2);
                (lb1 - ub2, res1 - res2, ub1 - lb2)
            }
            ArithExpr::Mul(mul) => {
                let mut lb = Rational::Finite(rug::Rational::from(1));
                let mut res = Rational::Finite(rug::Rational::from(1));
                let mut ub = Rational::Finite(rug::Rational::from(1));
                for sub_expr in mul {
                    let (sub_lb, sub_res, sub_ub) = self.eval_arith(sub_expr);
                    lb *= sub_lb;
                    res *= sub_res;
                    ub *= sub_ub;
                }
                (lb, res, ub)
            }
            ArithExpr::Div(e1, e2) => {
                let (lb1, res1, ub1) = self.eval_arith(e1);
                let (lb2, res2, ub2) = self.eval_arith(e2);
                (lb1 / ub2, res1 / res2, ub1 / lb2)
            }
        }
    }

    pub(super) fn mk_le(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> BoolExpr {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(if strict { const_term.is_negative() } else { const_term.is_negative() || const_term.is_zero() }),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();

                let eps_val = if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                let bound = InfRational::new(-const_term.clone() / coeff, eps_val / coeff);
                BoolExpr::Var(self.get_or_create_proxy(if coeff.is_positive() { BoolExpr::Ub(var, bound) } else { BoolExpr::Lb(var, bound) }))
            }
            _ => {
                let slack = if let Some(&slack) = self.lin_to_slack.get(&vars) {
                    slack
                } else {
                    let slack = self.mk_real();
                    self.tableau.insert(slack, vars.clone());
                    self.lin_to_slack.insert(vars, slack);
                    slack
                };

                let eps_val = if strict { rug::Rational::from(-1) } else { rug::Rational::from(0) };
                BoolExpr::Var(self.get_or_create_proxy(BoolExpr::Ub(slack, InfRational::new(-const_term, eps_val))))
            }
        }
    }

    pub(super) fn mk_arith_eq(&mut self, e1: &ArithExpr, e2: &ArithExpr) -> BoolExpr {
        if e1 == e2 {
            return BoolExpr::True;
        }
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(const_term.is_zero()),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();
                let bound = InfRational::new(-const_term.clone() / coeff, rug::Rational::from(0));
                BoolExpr::Var(self.get_or_create_proxy(BoolExpr::ArithEq(var, bound)))
            }
            _ => {
                let slack = if let Some(&slack) = self.lin_to_slack.get(&vars) {
                    slack
                } else {
                    let slack = self.mk_real();
                    self.tableau.insert(slack, vars.clone());
                    self.lin_to_slack.insert(vars, slack);
                    slack
                };

                BoolExpr::Var(self.get_or_create_proxy(BoolExpr::ArithEq(slack, InfRational::new(-const_term, rug::Rational::from(0)))))
            }
        }
    }

    pub(super) fn mk_ge(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> BoolExpr {
        let (vars, const_term) = self.diff(e1, e2);

        match vars.len() {
            0 => BoolExpr::from(if strict { const_term.is_positive() } else { const_term.is_positive() || const_term.is_zero() }),
            1 => {
                let (&var, coeff) = vars.iter().next().unwrap();

                let eps_val = if strict { rug::Rational::from(1) } else { rug::Rational::from(0) };
                let bound = InfRational::new(-const_term.clone() / coeff, eps_val / coeff);
                BoolExpr::Var(self.get_or_create_proxy(if coeff.is_positive() { BoolExpr::Lb(var, bound) } else { BoolExpr::Ub(var, bound) }))
            }
            _ => {
                let slack = if let Some(&slack) = self.lin_to_slack.get(&vars) {
                    slack
                } else {
                    let slack = self.mk_real();
                    self.tableau.insert(slack, vars.clone());
                    self.lin_to_slack.insert(vars, slack);
                    slack
                };

                let eps_val = if strict { rug::Rational::from(1) } else { rug::Rational::from(0) };
                BoolExpr::Var(self.get_or_create_proxy(BoolExpr::Lb(slack, InfRational::new(-const_term, eps_val))))
            }
        }
    }

    fn diff(&self, e1: &ArithExpr, e2: &ArithExpr) -> (BTreeMap<usize, rug::Rational>, rug::Rational) {
        let diff = Lin::from(e1) - Lin::from(e2);
        let mut vars = BTreeMap::new();

        for (var, coeff) in diff.vars {
            if let Some(basic) = self.tableau.get(&var) {
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
