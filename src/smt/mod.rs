pub mod ast;
mod lin;
mod lit;
mod rational;

use crate::smt::{
    ast::{ArithExpr, BoolExpr, EnumExpr, Expr},
    lin::Lin,
    lit::Lit,
    rational::{InfRational, Rational},
};
use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap, HashSet, VecDeque},
    fmt, mem,
};
use tracing::trace;

pub struct SMT {
    sat_to_ast: Vec<Option<BoolExpr>>,                            // Map from SAT variable index to its corresponding AST expression
    ast_to_sat: HashMap<BoolExpr, usize>,                         // Map from AST expression to its corresponding SAT variable index
    bools: Vec<Option<bool>>,                                     // Current assignment of each boolean variable (true, false, or unassigned)
    clauses: Vec<Clause>,                                         // List of clauses in the solver
    watches: Vec<Vec<usize>>,                                     // Watch lists for each literal (positive and negative)
    reason: Vec<Option<usize>>,                                   // Reason for each variable's assignment
    prop_q: VecDeque<Lit>,                                        // Queue of literals to propagate
    trail: Vec<Lit>,                                              // Trail of assigned literals for backtracking
    trail_lim: Vec<usize>,                                        // Indices in the trail where decisions were made
    level: Vec<Option<usize>>,                                    // Decision level for each variable
    ints: Vec<bool>,                                              // Distinguish between integer and real variables
    reals: Vec<Rational>,                                         // Current assignments of real variables
    lbs: Vec<Rational>,                                           // Current assignments of lower bounds
    ubs: Vec<Rational>,                                           // Current assignments of upper bounds
    lin_to_slack: HashMap<BTreeMap<usize, rug::Rational>, usize>, // Mapping from linear constraints to their corresponding slack variable
    tableau: BTreeMap<usize, BTreeMap<usize, rug::Rational>>,     // Tableau for linear constraints
    enums: Vec<HashMap<i32, usize>>,                              // Enum variables
}

impl Default for SMT {
    fn default() -> Self {
        Self::new()
    }
}

impl SMT {
    pub fn new() -> Self {
        SMT {
            sat_to_ast: Vec::new(),
            ast_to_sat: HashMap::new(),
            bools: Vec::new(),
            clauses: Vec::new(),
            watches: Vec::new(),
            reason: Vec::new(),
            prop_q: VecDeque::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            level: Vec::new(),
            ints: Vec::new(),
            reals: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            lin_to_slack: HashMap::new(),
            tableau: BTreeMap::new(),
            enums: Vec::new(),
        }
    }

    pub fn new_bool(&mut self) -> BoolExpr {
        let expr = BoolExpr::Var(self.bools.len());
        self.create_proxy(expr.clone());
        expr
    }

    pub fn new_int(&mut self) -> ArithExpr {
        let var_index = self.mk_int();
        ArithExpr::IntVar(var_index)
    }

    pub fn new_real(&mut self) -> ArithExpr {
        let var_index = self.mk_real();
        ArithExpr::RealVar(var_index)
    }

    pub fn new_enum(&mut self, values: impl IntoIterator<Item = i32>) -> EnumExpr {
        let var_index = self.enums.len();
        let mut var_domain = HashMap::new();
        for val in values {
            var_domain.insert(val, self.mk_bool());
        }
        self.enums.push(var_domain);
        EnumExpr::Var(var_index)
    }

    pub fn eval(&self, expr: &Expr) -> Option<Expr> {
        match expr {
            Expr::Bool(b) => match self.eval_bool(b) {
                Some(BoolExpr::True) => Some(Expr::Bool(BoolExpr::True)),
                Some(BoolExpr::False) => Some(Expr::Bool(BoolExpr::False)),
                None => None,
                _ => unreachable!(),
            },
            Expr::Enum(e) => match e {
                EnumExpr::Var(var_index) => {
                    let var_domain = &self.enums[*var_index];
                    for (val, bool_var) in var_domain {
                        if let Some(true) = self.bools.get(*bool_var).copied().unwrap_or(None) {
                            return Some(Expr::Enum(EnumExpr::Const(*val)));
                        }
                    }
                    None
                }
                EnumExpr::Const(val) => Some(Expr::Enum(EnumExpr::Const(*val))),
            },
            Expr::Arith(a) => {
                let (_lb, val, _ub) = self.eval_arith(a);
                Some(Expr::Arith(ArithExpr::Const(val))) // Return the evaluated value as a literal
            }
        }
    }

    pub fn eval_bool(&self, expr: &BoolExpr) -> Option<BoolExpr> {
        match expr {
            BoolExpr::True => Some(BoolExpr::True),
            BoolExpr::False => Some(BoolExpr::False),
            BoolExpr::Var(v) => match self.bools.get(*v).copied().unwrap_or(None) {
                Some(true) => Some(BoolExpr::True),
                Some(false) => Some(BoolExpr::False),
                None => Some(BoolExpr::Var(*v)),
            },
            BoolExpr::Not(not) => {
                let sub_result = self.eval_bool(not);
                match sub_result {
                    Some(BoolExpr::True) => Some(BoolExpr::False),
                    Some(BoolExpr::False) => Some(BoolExpr::True),
                    None => None,
                    _ => unreachable!(),
                }
            }
            BoolExpr::And(and) => {
                for sub_expr in and {
                    let sub_result = self.eval_bool(sub_expr);
                    match sub_result {
                        Some(BoolExpr::False) => return Some(BoolExpr::False),
                        None => return None,
                        _ => {}
                    }
                }
                Some(BoolExpr::True)
            }
            BoolExpr::Or(or) => {
                for sub_expr in or {
                    let sub_result = self.eval_bool(sub_expr);
                    match sub_result {
                        Some(BoolExpr::True) => return Some(BoolExpr::True),
                        None => return None,
                        _ => {}
                    }
                }
                Some(BoolExpr::False)
            }
            BoolExpr::Lt(e1, e2) => {
                let (lb1, _, ub1) = self.eval_arith(e1);
                let (lb2, _, ub2) = self.eval_arith(e2);
                if ub1 < lb2 {
                    Some(BoolExpr::True)
                } else if lb1 >= ub2 {
                    Some(BoolExpr::False)
                } else {
                    None
                }
            }
            BoolExpr::Le(e1, e2) => {
                let (lb1, _, ub1) = self.eval_arith(e1);
                let (lb2, _, ub2) = self.eval_arith(e2);
                if ub1 <= lb2 {
                    Some(BoolExpr::True)
                } else if lb1 > ub2 {
                    Some(BoolExpr::False)
                } else {
                    None
                }
            }
            BoolExpr::Eq(e1, e2) => match (self.eval(e1), self.eval(e2)) {
                (Some(Expr::Bool(a1)), Some(Expr::Bool(a2))) => match (self.eval_bool(&a1), self.eval_bool(&a2)) {
                    (Some(BoolExpr::True), Some(BoolExpr::True)) => Some(BoolExpr::True),
                    (Some(BoolExpr::False), Some(BoolExpr::False)) => Some(BoolExpr::True),
                    (None, _) | (_, None) => None,
                    _ => Some(BoolExpr::False),
                },
                (Some(Expr::Enum(a1)), Some(Expr::Enum(a2))) => {
                    if a1 == a2 {
                        Some(BoolExpr::True)
                    } else {
                        Some(BoolExpr::False)
                    }
                }
                (Some(Expr::Arith(a1)), Some(Expr::Arith(a2))) => {
                    let (lb1, _, ub1) = self.eval_arith(&a1);
                    let (lb2, _, ub2) = self.eval_arith(&a2);
                    if ub1 < lb2 || lb1 > ub2 {
                        Some(BoolExpr::False)
                    } else if lb1 == ub1 && lb2 == ub2 && lb1 == lb2 {
                        Some(BoolExpr::True)
                    } else {
                        None
                    }
                }
                _ => Some(BoolExpr::False), // Different types cannot be equal
            },
            BoolExpr::Ge(e1, e2) => {
                let (lb1, _, ub1) = self.eval_arith(e1);
                let (lb2, _, ub2) = self.eval_arith(e2);
                if lb1 > ub2 {
                    Some(BoolExpr::True)
                } else if ub1 < lb2 {
                    Some(BoolExpr::False)
                } else {
                    None
                }
            }
            BoolExpr::Gt(e1, e2) => {
                let (lb1, _, ub1) = self.eval_arith(e1);
                let (lb2, _, ub2) = self.eval_arith(e2);
                if lb1 > ub2 {
                    Some(BoolExpr::True)
                } else if ub1 <= lb2 {
                    Some(BoolExpr::False)
                } else {
                    None
                }
            }
            BoolExpr::Lb(var, inf_rational) => {
                let (lb, _, ub) = self.eval_arith(&ArithExpr::RealVar(*var));
                if ub < Rational::Finite(inf_rational.rat.clone()) || (ub == Rational::Finite(inf_rational.rat.clone()) && inf_rational.inf > rug::Rational::from(0)) {
                    Some(BoolExpr::False)
                } else if lb >= Rational::Finite(inf_rational.rat.clone()) && (inf_rational.inf <= rug::Rational::from(0)) {
                    Some(BoolExpr::True)
                } else {
                    None
                }
            }
            BoolExpr::ArithEq(var, inf_rational) => {
                let (lb, _, ub) = self.eval_arith(&ArithExpr::RealVar(*var));
                if ub < Rational::Finite(inf_rational.rat.clone()) || lb > Rational::Finite(inf_rational.rat.clone()) {
                    Some(BoolExpr::False)
                } else if lb == ub && lb == Rational::Finite(inf_rational.rat.clone()) {
                    Some(BoolExpr::True)
                } else {
                    None
                }
            }
            BoolExpr::Ub(var, inf_rational) => {
                let (lb, _, ub) = self.eval_arith(&ArithExpr::RealVar(*var));
                if lb > Rational::Finite(inf_rational.rat.clone()) || (lb == Rational::Finite(inf_rational.rat.clone()) && inf_rational.inf < rug::Rational::from(0)) {
                    Some(BoolExpr::False)
                } else if ub <= Rational::Finite(inf_rational.rat.clone()) && (inf_rational.inf >= rug::Rational::from(0)) {
                    Some(BoolExpr::True)
                } else {
                    None
                }
            }
        }
    }

    pub fn eval_arith(&self, expr: &ArithExpr) -> (Rational, Rational, Rational) {
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

    fn mk_bool(&mut self) -> usize {
        let idx = self.bools.len();
        self.bools.push(None);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new()); // For the negated literal
        self.reason.push(None);
        self.level.push(None);
        idx
    }

    fn mk_int(&mut self) -> usize {
        let var_index = self.ints.len();
        self.ints.push(true);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        var_index
    }

    fn mk_real(&mut self) -> usize {
        let var_index = self.reals.len();
        self.ints.push(false);
        self.reals.push(Rational::Finite(rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        var_index
    }

    fn get_proxy(&mut self, expr: &BoolExpr) -> Option<usize> {
        self.ast_to_sat.get(expr).copied()
    }

    fn create_proxy(&mut self, expr: BoolExpr) -> usize {
        let proxy = self.mk_bool();

        if proxy >= self.sat_to_ast.len() {
            self.sat_to_ast.resize(proxy + 1, None);
        }

        self.sat_to_ast[proxy] = Some(expr.clone());
        self.ast_to_sat.insert(expr, proxy);

        proxy
    }

    fn get_or_create_proxy<T: Borrow<BoolExpr>>(&mut self, expr: T) -> usize {
        if let Some(proxy) = self.get_proxy(expr.borrow()) { proxy } else { self.create_proxy(expr.borrow().clone()) }
    }

    pub fn decide(&mut self, expr: &BoolExpr) -> Result<(), BoolExpr> {
        match expr {
            BoolExpr::Var(v) => self.decide_lit(Lit::new(*v, false)),
            BoolExpr::Not(not) => match not.as_ref() {
                BoolExpr::Var(v) => self.decide_lit(Lit::new(*v, true)),
                _ => panic!("Unsupported expression type for decision: {}", expr),
            },
            _ => panic!("Unsupported expression type for decision: {}", expr),
        }
    }

    fn decide_lit(&mut self, lit: Lit) -> Result<(), BoolExpr> {
        self.trail_lim.push(self.trail.len());
        self.enqueue(lit, None);
        self.propagate()
    }

    pub fn assert<T: Borrow<BoolExpr>>(&mut self, expr: T) -> bool {
        trace!("Asserting: {}", expr.borrow());
        match expr.borrow() {
            BoolExpr::True => return true,
            BoolExpr::False => return false,
            BoolExpr::Var(var) => return self.enqueue(Lit::new(*var, false), None),
            BoolExpr::Not(inner) => {
                if let BoolExpr::Var(var) = inner.as_ref() {
                    return self.enqueue(Lit::new(*var, true), None);
                }
            }
            BoolExpr::And(and) => {
                for sub_expr in and {
                    if !self.assert(sub_expr) {
                        return false;
                    }
                }
                return true;
            }
            BoolExpr::Or(or) => {
                let mut lits = Vec::with_capacity(or.len());
                for sub_expr in or {
                    match self.mk_expr(sub_expr) {
                        BoolExpr::True => return true,
                        BoolExpr::False => continue,
                        BoolExpr::Var(var) => lits.push(Lit::new(var, false)),
                        BoolExpr::Not(inner) => {
                            let proxy = self.get_proxy(inner.as_ref()).expect("Proxy should exist after mk_expr");
                            lits.push(Lit::new(proxy, true));
                        }
                        _ => unreachable!(),
                    }
                }
                if lits.is_empty() {
                    return false;
                }
                self.add_clause(lits).expect("Adding clause should not fail");
                return true;
            }
            _ => {}
        }
        match self.mk_expr(expr.borrow()) {
            BoolExpr::True => true,
            BoolExpr::False => false,
            BoolExpr::Var(var) => self.enqueue(Lit::new(var, false), None),
            BoolExpr::Not(inner) => {
                let proxy = self.get_proxy(inner.as_ref()).expect("Proxy should exist after mk_expr");
                self.enqueue(Lit::new(proxy, true), None)
            }
            _ => unreachable!(),
        }
    }

    fn mk_expr(&mut self, expr: &BoolExpr) -> BoolExpr {
        match expr {
            BoolExpr::True => BoolExpr::True,
            BoolExpr::False => BoolExpr::False,
            BoolExpr::Var(var) => BoolExpr::Var(*var),
            BoolExpr::Not(inner) => {
                let inner_expr = self.mk_expr(inner.as_ref());
                match inner_expr {
                    BoolExpr::True => BoolExpr::False,
                    BoolExpr::False => BoolExpr::True,
                    BoolExpr::Var(var) => BoolExpr::Not(Box::new(BoolExpr::Var(var))),
                    BoolExpr::Not(inner_inner) => self.mk_expr(&inner_inner.as_ref()),
                    _ => unreachable!(),
                }
            }
            BoolExpr::And(and) => self.mk_and(and),
            BoolExpr::Or(or) => self.mk_or(or),
            BoolExpr::Le(e1, e2) => self.mk_le(e1, e2, false),
            BoolExpr::Lt(e1, e2) => self.mk_le(e1, e2, true),
            BoolExpr::Eq(e1, e2) => match (e1.as_ref(), e2.as_ref()) {
                (Expr::Bool(b1), Expr::Bool(b2)) => self.mk_bool_eq(b1, b2),
                (Expr::Arith(a1), Expr::Arith(a2)) => self.mk_arith_eq(a1, a2),
                _ => panic!("Unsupported expression types for equality: {} and {}", e1, e2),
            },
            BoolExpr::Ge(e1, e2) => self.mk_ge(e1, e2, false),
            BoolExpr::Gt(e1, e2) => self.mk_ge(e1, e2, true),
            _ => todo!(),
        }
    }

    fn mk_and(&mut self, and: &Vec<BoolExpr>) -> BoolExpr {
        let mut lits = Vec::with_capacity(and.len());
        for expr in and {
            let expr = self.mk_expr(expr);
            match expr {
                BoolExpr::True => continue,
                BoolExpr::False => return BoolExpr::False,
                BoolExpr::Var(var) => lits.push(Lit::new(var, false)),
                BoolExpr::Not(inner) => lits.push(Lit::new(self.get_proxy(inner.as_ref()).expect("Proxy should exist after mk_expr"), true)),
                _ => unreachable!(),
            }
        }
        match lits.len() {
            0 => BoolExpr::True,
            1 => {
                if lits[0].sign() {
                    BoolExpr::Not(Box::new(BoolExpr::Var(lits[0].var())))
                } else {
                    BoolExpr::Var(lits[0].var())
                }
            }
            _ => {
                let and = BoolExpr::And(lits.iter().map(|lit| if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(lit.var()))) } else { BoolExpr::Var(lit.var()) }).collect());
                if let Some(proxy) = self.get_proxy(&and) {
                    BoolExpr::Var(proxy)
                } else {
                    let proxy = self.create_proxy(and);
                    for lit in &lits {
                        self.add_clause([Lit::new(proxy, true), *lit]).expect("Adding clause should not fail");
                    }
                    BoolExpr::Var(proxy)
                }
            }
        }
    }

    fn mk_or(&mut self, or: &Vec<BoolExpr>) -> BoolExpr {
        let mut lits = Vec::with_capacity(1 + or.len());
        for expr in or {
            let expr = self.mk_expr(expr);
            match expr {
                BoolExpr::True => return BoolExpr::True,
                BoolExpr::False => continue,
                BoolExpr::Var(var) => lits.push(Lit::new(var, false)),
                BoolExpr::Not(inner) => lits.push(Lit::new(self.get_proxy(inner.as_ref()).expect("Proxy should exist after mk_expr"), true)),
                _ => unreachable!(),
            }
        }
        match lits.len() {
            0 => BoolExpr::False,
            1 => {
                if lits[0].sign() {
                    BoolExpr::Not(Box::new(BoolExpr::Var(lits[0].var())))
                } else {
                    BoolExpr::Var(lits[0].var())
                }
            }
            _ => {
                let or = BoolExpr::Or(lits.iter().map(|lit| if lit.sign() { BoolExpr::Not(Box::new(BoolExpr::Var(lit.var()))) } else { BoolExpr::Var(lit.var()) }).collect());
                if let Some(proxy) = self.get_proxy(&or) {
                    BoolExpr::Var(proxy)
                } else {
                    let proxy = self.create_proxy(or);
                    for lit in &lits {
                        self.add_clause([Lit::new(proxy, false), !*lit]).expect("Adding clause should not fail");
                    }
                    lits.push(Lit::new(proxy, true));
                    self.add_clause(lits).expect("Adding clause should not fail");
                    BoolExpr::Var(proxy)
                }
            }
        }
    }

    fn mk_le(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> BoolExpr {
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

    fn mk_bool_eq(&mut self, e1: &BoolExpr, e2: &BoolExpr) -> BoolExpr {
        let e1 = self.mk_expr(e1);
        let e2 = self.mk_expr(e2);
        if e1 == e2 {
            return BoolExpr::True;
        }
        let eq = BoolExpr::Eq(Box::new(Expr::Bool(e1.clone())), Box::new(Expr::Bool(e2.clone())));
        if let Some(proxy) = self.get_proxy(&eq) {
            BoolExpr::Var(proxy)
        } else {
            let proxy = self.create_proxy(eq);
            let lit_e1 = match e1 {
                BoolExpr::Var(v) => Lit::new(v, false),
                BoolExpr::Not(not) => match not.as_ref() {
                    BoolExpr::Var(v) => Lit::new(*v, true),
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            };
            let lit_e2 = match e2 {
                BoolExpr::Var(v) => Lit::new(v, false),
                BoolExpr::Not(not) => match not.as_ref() {
                    BoolExpr::Var(v) => Lit::new(*v, true),
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            };

            // (¬p ∨ ¬e1 ∨ e2)
            self.add_clause([Lit::new(proxy, true), !lit_e1, lit_e2]).expect("Adding clause should not fail");
            // (¬p ∨ e1 ∨ ¬e2)
            self.add_clause([Lit::new(proxy, true), lit_e1, !lit_e2]).expect("Adding clause should not fail");
            // (p ∨ ¬e1 ∨ ¬e2)
            self.add_clause([Lit::new(proxy, false), !lit_e1, !lit_e2]).expect("Adding clause should not fail");
            // (p ∨ e1 ∨ e2)
            self.add_clause([Lit::new(proxy, false), lit_e1, lit_e2]).expect("Adding clause should not fail");

            BoolExpr::Var(proxy)
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

    fn mk_ge(&mut self, e1: &ArithExpr, e2: &ArithExpr, strict: bool) -> BoolExpr {
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

    pub fn propagate(&mut self) -> Result<(), BoolExpr> {
        while let Some(lit) = self.prop_q.pop_front() {
            let falsified = !lit;
            let falsified_index = falsified.index();
            let watches = mem::take(&mut self.watches[falsified_index]);
            for i in 0..watches.len() {
                let mut clause_idx = watches[i];
                // Keep the first watched literal as the other watcher and the second as the falsified one.
                if self.clauses[clause_idx].lits[0] == falsified {
                    self.clauses[clause_idx].lits.swap(0, 1);
                }

                // Check if clause is already satisfied
                if self.lit_value(&self.clauses[clause_idx].lits[0]) == Some(true) {
                    self.watches[lit.index()].push(clause_idx);
                    continue;
                }

                // Find a replacement watcher that is not currently false.
                let mut found_replacement = false;
                for j in 2..self.clauses[clause_idx].lits.len() {
                    let next_lit = self.clauses[clause_idx].lits[j];
                    if self.lit_value(&next_lit) != Some(false) {
                        self.clauses[clause_idx].lits.swap(1, j);
                        self.watches[next_lit.index()].push(clause_idx);
                        found_replacement = true;
                        break;
                    }
                }

                if found_replacement {
                    continue;
                }

                // If we reach here, the clause is either unit or unsatisfied
                self.watches[falsified_index].push(clause_idx); // Re-add the clause to the watch list
                if !self.enqueue(self.clauses[clause_idx].lits[0], Some(clause_idx)) {
                    for c_i in watches.iter().skip(i + 1) {
                        self.watches[falsified_index].push(*c_i);
                    }
                    self.prop_q.clear();

                    let mut seen: HashSet<usize> = HashSet::new();
                    let mut counter: usize = 0;
                    let mut p: Option<(Lit, Option<usize>)> = None;
                    let mut learnt = Vec::new();
                    learnt.push(Lit::new(0, false)); // Placeholder for the asserting literal
                    let mut backtrack_level: usize = 0;

                    loop {
                        // 1. Process the current clause (either the conflict or a reason)
                        for lit in &self.clauses[clause_idx].lits {
                            // Skip the variable we are currently resolving away
                            if Some(lit.var()) == p.map(|l| l.0.var()) {
                                continue;
                            }

                            if !seen.contains(&lit.var()) {
                                seen.insert(lit.var());
                                if self.level(lit.var()).expect("Variable should have a level") == self.decision_level() {
                                    counter += 1;
                                } else {
                                    // This literal comes from a previous decision level
                                    learnt.push(*lit);
                                    backtrack_level = backtrack_level.max(self.level(lit.var()).expect("Variable should have a level"));
                                }
                            }
                        }

                        // 2. Find the next variable from the trail assigned at this level
                        p = loop {
                            let lit = *self.trail.last().expect("There should be a literal");
                            let reason = self.reason[lit.var()];
                            self.undo_one();
                            if seen.contains(&lit.var()) {
                                break Some((lit, reason));
                            }
                        };
                        counter -= 1;

                        if counter == 0 {
                            // 3. We have found the asserting literal
                            learnt[0] = !p.expect("There should be a literal").0;
                            break;
                        }

                        // 4. Update clause to the reason of the variable we just resolved away
                        clause_idx = p.expect("There should be a literal").1.expect("There should be a reason");
                    }

                    self.cancel_until(backtrack_level);
                    let mut lits = Vec::with_capacity(learnt.len());
                    for lit in learnt {
                        if lit.sign() {
                            lits.push(BoolExpr::Not(Box::new(BoolExpr::Var(lit.var()))));
                        } else {
                            lits.push(BoolExpr::Var(lit.var()));
                        }
                    }
                    return Err(BoolExpr::Or(lits));
                }
            }
        }
        Ok(())
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        trace!("Enqueue {}{}", lit, reason.map_or("".to_string(), |r| format!(" (reason: {})", r)));
        match self.lit_value(&lit) {
            None => {
                self.bools[lit.var()] = if lit.sign() { Some(false) } else { Some(true) };
                self.level[lit.var()] = Some(self.decision_level());
                self.reason[lit.var()] = reason;
                self.trail.push(lit);
                self.prop_q.push_back(lit);
                true
            }
            Some(value) => value == !lit.sign(),
        }
    }

    fn add_clause(&mut self, lits: impl IntoIterator<Item = Lit>) -> Result<(), Vec<Lit>> {
        let mut lits = lits.into_iter().collect::<Vec<_>>();
        match lits.len() {
            0 => return Err(lits),
            1 => {
                self.cancel_until(0);
                if !self.enqueue(lits[0], None) {
                    return Err(lits);
                }
            }
            _ => {
                let clause_index = self.clauses.len();
                lits.sort_by_key(|l| self.bools.get(l.var()).copied().unwrap_or(None).is_some());
                let clause = Clause { lits: lits.clone() };
                trace!("Adding clause {}: {}", clause_index, clause);
                for lit in &clause.lits[0..2] {
                    self.watches[lit.index()].push(clause_index);
                }
                self.clauses.push(clause);
                if self.lit_value(&lits[0]).is_none() && self.lit_value(&lits[1]) == Some(false) && !self.enqueue(lits[0], Some(clause_index)) {
                    return Err(lits);
                }
            }
        }
        Ok(())
    }

    fn lit_value(&self, lit: &Lit) -> Option<bool> {
        let val = self.bools.get(lit.var()).expect("Variable index out of bounds");
        if lit.sign() { val.map(|v| !v) } else { *val }
    }

    fn level(&self, var: usize) -> &Option<usize> {
        self.level.get(var).expect("Variable index out of bounds")
    }

    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    fn undo_one(&mut self) {
        if let Some(lit) = self.trail.pop() {
            trace!("Undoing assignment of {}", lit);
            self.bools[lit.var()] = None;
            self.reason[lit.var()] = None;
            self.level[lit.var()] = None;
        }
    }

    pub fn cancel_until(&mut self, level: usize) {
        trace!("Canceling until level {}", level);
        while self.decision_level() > level {
            let lim = self.trail_lim.pop().unwrap();
            while self.trail.len() > lim {
                self.undo_one();
            }
        }
    }
}

struct Clause {
    lits: Vec<Lit>, // List of literals in the clause
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<String> = self.lits.iter().map(|l| l.to_string()).collect();
        write!(f, "({})", lits.join(" ∨ "))
    }
}

#[cfg(test)]
mod tests {
    use tracing::{Level, subscriber};

    use super::*;
    use crate::smt::ast::{BoolExpr, or};

    #[test]
    fn test_smt_creation() {
        let mut smt = SMT::new();
        smt.new_bool();
        smt.new_bool();
        smt.new_int();
        smt.new_real();
        assert_eq!(smt.bools.len(), 2);
        assert_eq!(smt.ints.len(), 2);
        assert_eq!(smt.reals.len(), 2);
        smt.new_enum([1, 2, 3]);
        assert_eq!(smt.enums.len(), 1);
    }

    #[test]
    fn test_eval_bool() {
        let mut smt = SMT::new();
        let b1 = smt.new_bool();
        let b2 = smt.new_bool();
        smt.assert(&b1);
        smt.assert(&!(b2.clone()));
        assert_eq!(smt.eval_bool(&b1), Some(BoolExpr::True));
        assert_eq!(smt.eval_bool(&b2), Some(BoolExpr::False));
    }

    #[test]
    fn test_add_clause() {
        let subscriber = tracing_subscriber::fmt().with_max_level(Level::TRACE).finish();
        subscriber::set_global_default(subscriber).expect("Failed to set global default subscriber");

        let mut smt = SMT::new();
        let b1 = smt.new_bool();
        let b2 = smt.new_bool();
        let clause = or([b1.clone(), b2.clone()]);
        smt.assert(&clause);
        assert_eq!(smt.clauses.len(), 1);
    }

    #[test]
    fn test_ast_to_sat_constants() {
        let mut solver = SMT::new();

        assert_eq!(solver.mk_expr(&BoolExpr::True), BoolExpr::True);
        assert_eq!(solver.mk_expr(&BoolExpr::False), BoolExpr::False);

        assert_eq!(solver.mk_expr(&BoolExpr::Not(Box::new(BoolExpr::True))), BoolExpr::False);
        assert_eq!(solver.mk_expr(&BoolExpr::Not(Box::new(BoolExpr::False))), BoolExpr::True);
    }

    #[test]
    fn test_ast_to_sat_var_caching() {
        let mut solver = SMT::new();
        let v0 = solver.new_bool();
        let not_v0 = !v0;

        let res1 = solver.mk_expr(&not_v0);
        let res2 = solver.mk_expr(&not_v0);

        assert_eq!(res1, res2, "mk_expr should return the same proxy for the same expression");
    }

    #[test]
    fn test_ast_to_sat_and_reduction() {
        let mut solver = SMT::new();
        let v0 = solver.new_bool();

        assert_eq!(solver.mk_expr(&BoolExpr::And(vec![])), BoolExpr::True);
        assert_eq!(solver.mk_expr(&BoolExpr::And(vec![v0.clone()])), v0.clone());
        assert_eq!(solver.mk_expr(&BoolExpr::And(vec![v0, BoolExpr::False])), BoolExpr::False);
    }

    #[test]
    fn test_ast_to_sat_or_reduction() {
        let mut solver = SMT::new();
        let v0 = solver.new_bool();

        assert_eq!(solver.mk_expr(&BoolExpr::Or(vec![])), BoolExpr::False);
        assert_eq!(solver.mk_expr(&BoolExpr::Or(vec![v0.clone()])), v0.clone());
        assert_eq!(solver.mk_expr(&BoolExpr::Or(vec![v0, BoolExpr::True])), BoolExpr::True);
    }

    #[test]
    fn test_ast_to_sat_tseitin_and_proxy() {
        let mut solver = SMT::new();
        let v0 = solver.new_bool();
        let v1 = solver.new_bool();

        let and_expr = BoolExpr::And(vec![v0, v1]);
        let res = solver.mk_expr(&and_expr);

        if let BoolExpr::Var(proxy_id) = res {
            assert!(proxy_id > 1, "Proxy ID should be greater than the original variable IDs");

            assert_eq!(solver.sat_to_ast[proxy_id], Some(and_expr.clone()));
            assert_eq!(solver.ast_to_sat.get(&and_expr), Some(&proxy_id));
            assert_eq!(solver.clauses.len(), 2, "Two clauses should be added for the AND Tseitin transformation");
        } else {
            panic!("The conversion of a multi-variable AND did not return a Var(proxy)");
        }
    }

    #[test]
    fn test_ast_to_sat_double_negation() {
        let mut solver = SMT::new();

        let v0 = solver.new_bool();
        let not_v0 = !v0.clone();
        let double_not = !not_v0;

        let res = solver.mk_expr(&double_not);
        assert_eq!(res, v0, "The double negation is not simplified correctly");
    }
}
