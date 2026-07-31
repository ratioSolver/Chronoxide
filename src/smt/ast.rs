use crate::smt::rational::Rational;
use std::{fmt, ops};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
#[repr(u8)]
pub enum LBool {
    /// The variable is assigned to true.
    True,
    /// The variable is assigned to false.
    False,
    /// The variable is currently unassigned.
    #[default]
    Undef,
}

impl ops::Not for LBool {
    type Output = Self;

    fn not(self) -> Self {
        match self {
            LBool::True => LBool::False,
            LBool::False => LBool::True,
            LBool::Undef => LBool::Undef,
        }
    }
}

impl fmt::Display for LBool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LBool::True => write!(f, "true"),
            LBool::False => write!(f, "false"),
            LBool::Undef => write!(f, "undef"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Bool(BoolExpr),
    Arith(ArithExpr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    Lit(LBool),
    Var(usize),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Lt(Box<ArithExpr>, Box<ArithExpr>),
    Le(Box<ArithExpr>, Box<ArithExpr>),
    Eq(Box<Expr>, Box<Expr>),
    Ge(Box<ArithExpr>, Box<ArithExpr>),
    Gt(Box<ArithExpr>, Box<ArithExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArithExpr {
    Lit(Rational),
    Val { lb: Rational, val: Rational, ub: Rational }, // Represents a value with lower and upper bounds
    Int(usize),
    Real(usize),
    Add(Vec<ArithExpr>),
    Sub(Box<ArithExpr>, Box<ArithExpr>),
    Mul(Vec<ArithExpr>),
    Div(Box<ArithExpr>, Box<ArithExpr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::Arith(a) => write!(f, "{}", a),
        }
    }
}

impl fmt::Display for BoolExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BoolExpr::Lit(l) => write!(f, "{}", l),
            BoolExpr::Var(v) => write!(f, "b{}", v),
            BoolExpr::Not(e) => write!(f, "¬{}", e),
            BoolExpr::And(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" ∧ "))
            }
            BoolExpr::Or(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" ∨ "))
            }
            BoolExpr::Lt(a1, a2) => write!(f, "{} < {}", a1, a2),
            BoolExpr::Le(a1, a2) => write!(f, "{} ≤ {}", a1, a2),
            BoolExpr::Eq(e1, e2) => write!(f, "{} = {}", e1, e2),
            BoolExpr::Ge(a1, a2) => write!(f, "{} ≥ {}", a1, a2),
            BoolExpr::Gt(a1, a2) => write!(f, "{} > {}", a1, a2),
        }
    }
}

impl fmt::Display for ArithExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArithExpr::Lit(r) => write!(f, "{}", r),
            ArithExpr::Val { lb, val, ub } => write!(f, "{} ∈ [{} , {}]", val, lb, ub),
            ArithExpr::Int(n) => write!(f, "i{}", n),
            ArithExpr::Real(n) => write!(f, "r{}", n),
            ArithExpr::Add(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" + "))
            }
            ArithExpr::Sub(e1, e2) => write!(f, "({} - {})", e1, e2),
            ArithExpr::Mul(es) => {
                let es_str: Vec<String> = es.iter().map(|e| format!("{}", e)).collect();
                write!(f, "({})", es_str.join(" * "))
            }
            ArithExpr::Div(e1, e2) => write!(f, "({} / {})", e1, e2),
        }
    }
}

fn push_negations(expr: &BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::Not(inner) => push_inverted(inner),
        BoolExpr::And(terms) => BoolExpr::And(terms.iter().map(push_negations).collect()),
        BoolExpr::Or(terms) => BoolExpr::Or(terms.iter().map(push_negations).collect()),
        _ => expr.clone(),
    }
}

fn push_inverted(expr: &BoolExpr) -> BoolExpr {
    match expr {
        // Double negation elimination: Not(Not(x)) => x
        BoolExpr::Not(inner) => push_negations(inner),

        // De Morgan: Not(And(a, b, ...)) => Or(Not(a), Not(b), ...)
        BoolExpr::And(terms) => BoolExpr::Or(terms.iter().map(push_inverted).collect()),

        // De Morgan: Not(Or(a, b, ...)) => And(Not(a), Not(b), ...)
        BoolExpr::Or(terms) => BoolExpr::And(terms.iter().map(push_inverted).collect()),

        // Negate comparisons by flipping to their complement
        BoolExpr::Lt(a, b) => BoolExpr::Ge(a.clone(), b.clone()),
        BoolExpr::Le(a, b) => BoolExpr::Gt(a.clone(), b.clone()),
        BoolExpr::Ge(a, b) => BoolExpr::Lt(a.clone(), b.clone()),
        BoolExpr::Gt(a, b) => BoolExpr::Le(a.clone(), b.clone()),
        BoolExpr::Eq(a, b) => BoolExpr::Not(Box::new(BoolExpr::Eq(a.clone(), b.clone()))),

        // Literals, variables: wrap in Not
        _ => BoolExpr::Not(Box::new(expr.clone())),
    }
}

fn distribute(expr: &BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::Or(terms) => {
            // Step 1: Recursively distribute children, flatten nested Ors
            let mut distributed_terms = Vec::new();
            for t in terms {
                let dist = distribute(t);
                if let BoolExpr::Or(inner_terms) = dist {
                    distributed_terms.extend(inner_terms);
                } else {
                    distributed_terms.push(dist);
                }
            }

            // Step 2: Cartesian product over And boundaries
            let mut result_ands: Vec<Vec<BoolExpr>> = vec![vec![]];

            for term in distributed_terms {
                if let BoolExpr::And(and_terms) = term {
                    let mut next_ands = Vec::new();
                    for existing_and in &result_ands {
                        for and_term in &and_terms {
                            let mut combo = existing_and.clone();
                            combo.push(and_term.clone());
                            next_ands.push(combo);
                        }
                    }
                    result_ands = next_ands;
                } else {
                    for existing_and in &mut result_ands {
                        existing_and.push(term.clone());
                    }
                }
            }

            // Step 3: Wrap combinations back into Or nodes inside a master And
            let cnf_or_nodes: Vec<BoolExpr> = result_ands.into_iter().map(BoolExpr::Or).collect();

            if cnf_or_nodes.len() == 1 { cnf_or_nodes.into_iter().next().unwrap() } else { BoolExpr::And(cnf_or_nodes) }
        }

        BoolExpr::And(terms) => {
            // Flatten nested Ands
            let mut distributed_terms = Vec::new();
            for t in terms {
                let dist = distribute(t);
                if let BoolExpr::And(inner_terms) = dist {
                    distributed_terms.extend(inner_terms);
                } else {
                    distributed_terms.push(dist);
                }
            }
            BoolExpr::And(distributed_terms)
        }

        _ => expr.clone(),
    }
}

pub fn to_cnf(expr: &BoolExpr) -> BoolExpr {
    distribute(&push_negations(expr))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::rational::Rational;

    // --- Helpers ---

    fn var(v: usize) -> BoolExpr {
        BoolExpr::Var(v)
    }
    fn not(e: BoolExpr) -> BoolExpr {
        BoolExpr::Not(Box::new(e))
    }
    fn and(es: impl IntoIterator<Item = BoolExpr>) -> BoolExpr {
        BoolExpr::And(es.into_iter().collect())
    }
    fn or(es: impl IntoIterator<Item = BoolExpr>) -> BoolExpr {
        BoolExpr::Or(es.into_iter().collect())
    }
    fn lit_true() -> BoolExpr {
        BoolExpr::Lit(LBool::True)
    }
    fn lit_false() -> BoolExpr {
        BoolExpr::Lit(LBool::False)
    }
    fn aint(n: usize) -> Box<ArithExpr> {
        Box::new(ArithExpr::Int(n))
    }
    fn alit(n: i32) -> Box<ArithExpr> {
        Box::new(ArithExpr::Lit(Rational::Finite(rug::Rational::from(n))))
    }

    // --- LBool Display ---

    #[test]
    fn lbool_display() {
        assert_eq!(LBool::True.to_string(), "true");
        assert_eq!(LBool::False.to_string(), "false");
        assert_eq!(LBool::Undef.to_string(), "undef");
    }

    // --- BoolExpr Display ---

    #[test]
    fn bool_display_lit() {
        assert_eq!(lit_true().to_string(), "true");
    }

    #[test]
    fn bool_display_var() {
        assert_eq!(var(3).to_string(), "b3");
    }

    #[test]
    fn bool_display_not() {
        assert_eq!(not(var(0)).to_string(), "¬b0");
    }

    #[test]
    fn bool_display_and() {
        assert_eq!(and([var(0), var(1)]).to_string(), "(b0 ∧ b1)");
    }

    #[test]
    fn bool_display_or() {
        assert_eq!(or([var(0), var(1)]).to_string(), "(b0 ∨ b1)");
    }

    #[test]
    fn bool_display_comparisons() {
        assert_eq!(BoolExpr::Lt(aint(0), aint(1)).to_string(), "0 < 1");
        assert_eq!(BoolExpr::Le(aint(0), aint(1)).to_string(), "0 ≤ 1");
        assert_eq!(BoolExpr::Ge(aint(0), aint(1)).to_string(), "0 ≥ 1");
        assert_eq!(BoolExpr::Gt(aint(0), aint(1)).to_string(), "0 > 1");
    }

    #[test]
    fn bool_display_eq() {
        let e = BoolExpr::Eq(Box::new(Expr::Bool(var(0))), Box::new(Expr::Bool(var(1))));
        assert_eq!(e.to_string(), "b0 = b1");
    }

    // --- ArithExpr Display ---

    #[test]
    fn arith_display_lit() {
        assert_eq!(ArithExpr::Lit(Rational::Finite(rug::Rational::from(5))).to_string(), "5");
    }

    #[test]
    fn arith_display_val() {
        let e = ArithExpr::Val {
            lb: Rational::Finite(rug::Rational::from(0)),
            val: Rational::Finite(rug::Rational::from(3)),
            ub: Rational::Finite(rug::Rational::from(10)),
        };
        assert_eq!(e.to_string(), "3 ∈ [0 , 10]");
    }

    #[test]
    fn arith_display_int_real() {
        assert_eq!(ArithExpr::Int(2).to_string(), "2");
        assert_eq!(ArithExpr::Real(5).to_string(), "5");
    }

    #[test]
    fn arith_display_add() {
        let e = ArithExpr::Add(vec![ArithExpr::Int(0), ArithExpr::Int(1)]);
        assert_eq!(e.to_string(), "(0 + 1)");
    }

    #[test]
    fn arith_display_sub() {
        let e = ArithExpr::Sub(Box::new(ArithExpr::Int(0)), Box::new(ArithExpr::Int(1)));
        assert_eq!(e.to_string(), "(0 - 1)");
    }

    #[test]
    fn arith_display_mul() {
        let e = ArithExpr::Mul(vec![ArithExpr::Int(0), ArithExpr::Int(1)]);
        assert_eq!(e.to_string(), "(0 * 1)");
    }

    #[test]
    fn arith_display_div() {
        let e = ArithExpr::Div(Box::new(ArithExpr::Int(0)), Box::new(ArithExpr::Int(1)));
        assert_eq!(e.to_string(), "(0 / 1)");
    }

    // --- push_negations ---

    #[test]
    fn push_negations_literal_unchanged() {
        assert_eq!(push_negations(&lit_true()), lit_true());
    }

    #[test]
    fn push_negations_var_unchanged() {
        assert_eq!(push_negations(&var(0)), var(0));
    }

    #[test]
    fn push_negations_not_var_becomes_not_var() {
        // Not(var) has no inner Not, so stays as Not(var)
        assert_eq!(push_negations(&not(var(0))), not(var(0)));
    }

    #[test]
    fn push_negations_double_not_eliminates() {
        // Not(Not(x)) => x
        assert_eq!(push_negations(&not(not(var(0)))), var(0));
    }

    #[test]
    fn push_negations_triple_not() {
        // Not(Not(Not(x))) => Not(x)
        assert_eq!(push_negations(&not(not(not(var(0))))), not(var(0)));
    }

    #[test]
    fn push_negations_recurses_into_and() {
        let expr = and([not(not(var(0))), not(not(var(1)))]);
        assert_eq!(push_negations(&expr), and([var(0), var(1)]));
    }

    #[test]
    fn push_negations_recurses_into_or() {
        let expr = or([not(not(var(0))), var(1)]);
        assert_eq!(push_negations(&expr), or([var(0), var(1)]));
    }

    #[test]
    fn push_negations_not_and_demorgan() {
        // Not(And(a, b)) => Or(Not(a), Not(b))
        let expr = not(and([var(0), var(1)]));
        assert_eq!(push_negations(&expr), or([not(var(0)), not(var(1))]));
    }

    #[test]
    fn push_negations_not_or_demorgan() {
        // Not(Or(a, b)) => And(Not(a), Not(b))
        let expr = not(or([var(0), var(1)]));
        assert_eq!(push_negations(&expr), and([not(var(0)), not(var(1))]));
    }

    #[test]
    fn push_negations_not_lt_becomes_ge() {
        let expr = not(BoolExpr::Lt(aint(0), aint(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Ge(aint(0), aint(1)));
    }

    #[test]
    fn push_negations_not_le_becomes_gt() {
        let expr = not(BoolExpr::Le(aint(0), aint(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Gt(aint(0), aint(1)));
    }

    #[test]
    fn push_negations_not_ge_becomes_lt() {
        let expr = not(BoolExpr::Ge(aint(0), aint(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Lt(aint(0), aint(1)));
    }

    #[test]
    fn push_negations_not_gt_becomes_le() {
        let expr = not(BoolExpr::Gt(aint(0), aint(1)));
        assert_eq!(push_negations(&expr), BoolExpr::Le(aint(0), aint(1)));
    }

    #[test]
    fn push_negations_not_eq_stays_not_eq() {
        let inner = BoolExpr::Eq(Box::new(Expr::Bool(var(0))), Box::new(Expr::Bool(var(1))));
        let expr = not(inner.clone());
        assert_eq!(push_negations(&expr), not(inner));
    }

    // --- distribute ---

    #[test]
    fn distribute_atom_unchanged() {
        assert_eq!(distribute(&var(0)), var(0));
        assert_eq!(distribute(&lit_true()), lit_true());
    }

    #[test]
    fn distribute_and_of_atoms() {
        let expr = and([var(0), var(1)]);
        assert_eq!(distribute(&expr), and([var(0), var(1)]));
    }

    #[test]
    fn distribute_or_of_atoms() {
        let expr = or([var(0), var(1)]);
        // Or(a, b) with no And inside stays as-is (wrapped in And with one element, unwrapped)
        assert_eq!(distribute(&expr), or([var(0), var(1)]));
    }

    #[test]
    fn distribute_or_over_and() {
        // Or(a, And(b, c)) => And(Or(a, b), Or(a, c))
        let expr = or([var(0), and([var(1), var(2)])]);
        let expected = and([or([var(0), var(1)]), or([var(0), var(2)])]);
        assert_eq!(distribute(&expr), expected);
    }

    #[test]
    fn distribute_flattens_nested_or() {
        // Or(Or(a, b), c) => Or(a, b, c)
        let expr = or([or([var(0), var(1)]), var(2)]);
        assert_eq!(distribute(&expr), or([var(0), var(1), var(2)]));
    }

    #[test]
    fn distribute_flattens_nested_and() {
        // And(And(a, b), c) => And(a, b, c)
        let expr = and([and([var(0), var(1)]), var(2)]);
        assert_eq!(distribute(&expr), and([var(0), var(1), var(2)]));
    }

    #[test]
    fn distribute_and_inside_and_flattened() {
        let expr = and([var(0), and([var(1), var(2)])]);
        assert_eq!(distribute(&expr), and([var(0), var(1), var(2)]));
    }

    #[test]
    fn distribute_cartesian_product_two_ands() {
        // Or(And(a, b), And(c, d)) => And(Or(a,c), Or(a,d), Or(b,c), Or(b,d))
        let expr = or([and([var(0), var(1)]), and([var(2), var(3)])]);
        let result = distribute(&expr);
        // Should be an And of four Or clauses
        if let BoolExpr::And(clauses) = result {
            assert_eq!(clauses.len(), 4);
            for clause in &clauses {
                assert!(matches!(clause, BoolExpr::Or(_)));
            }
        } else {
            panic!("expected And");
        }
    }

    // --- to_cnf ---

    #[test]
    fn to_cnf_atom_unchanged() {
        assert_eq!(to_cnf(&var(0)), var(0));
    }

    #[test]
    fn to_cnf_already_cnf() {
        // And(Or(a, b), Or(c, d)) is already CNF
        let expr = and([or([var(0), var(1)]), or([var(2), var(3)])]);
        assert_eq!(to_cnf(&expr), expr);
    }

    #[test]
    fn to_cnf_double_negation() {
        assert_eq!(to_cnf(&not(not(var(0)))), var(0));
    }

    #[test]
    fn to_cnf_not_and_demorgan_then_distribute() {
        // Not(And(a, b)) => Or(Not(a), Not(b)) — already a single clause
        let expr = not(and([var(0), var(1)]));
        assert_eq!(to_cnf(&expr), or([not(var(0)), not(var(1))]));
    }

    #[test]
    fn to_cnf_not_or_demorgan() {
        // Not(Or(a, b)) => And(Not(a), Not(b))
        let expr = not(or([var(0), var(1)]));
        assert_eq!(to_cnf(&expr), and([not(var(0)), not(var(1))]));
    }

    #[test]
    fn to_cnf_or_over_and_distributes() {
        // Or(a, And(b, c)) => And(Or(a, b), Or(a, c))
        let expr = or([var(0), and([var(1), var(2)])]);
        let expected = and([or([var(0), var(1)]), or([var(0), var(2)])]);
        assert_eq!(to_cnf(&expr), expected);
    }

    #[test]
    fn to_cnf_not_comparison_flipped() {
        assert_eq!(to_cnf(&not(BoolExpr::Lt(alit(0), alit(1)))), BoolExpr::Ge(alit(0), alit(1)));
        assert_eq!(to_cnf(&not(BoolExpr::Ge(alit(0), alit(1)))), BoolExpr::Lt(alit(0), alit(1)));
    }

    #[test]
    fn to_cnf_nested_not_and_or() {
        // Not(Or(And(a,b), c)) => And(Or(Not(a), Not(c)), Or(Not(b), Not(c)))
        let expr = not(or([and([var(0), var(1)]), var(2)]));
        // push_negations: And(Or(Not(a), Not(b)), Not(c))
        // distribute: And of Or(Not(a),Not(b)) and Not(c) — already flat
        let result = to_cnf(&expr);
        if let BoolExpr::And(clauses) = result {
            assert_eq!(clauses.len(), 2);
        } else {
            panic!("expected And, got: {}", result);
        }
    }
}
