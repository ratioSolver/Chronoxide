use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
};
use riddle::{
    env::Env,
    language::{Disjunction, Expr, Statement, execute},
    scope::Scope,
};
use serde_json::{Value, json};
use std::{rc::Rc, str::FromStr};

pub(crate) struct DisjunctionFlaw {
    disjunction: Disjunction,
}

impl DisjunctionFlaw {
    pub(crate) fn new(disjunction: Disjunction) -> Self {
        Self { disjunction }
    }
}

impl Flaw for DisjunctionFlaw {
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();

        for (disjunct, cost) in &self.disjunction.disjuncts {
            let rho = smt.new_lit();
            slv.add_resolver(&mut smt, &mut graph, Box::new(DisjunctionResolver::new(expr_to_cost(cost), self.disjunction.scp.clone(), self.disjunction.env.clone(), disjunct.to_vec())), rho)?;
        }

        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "disjunction",
        })
    }
}

struct DisjunctionResolver {
    cost: rug::Rational,
    scp: Rc<dyn Scope>,
    env: Rc<dyn Env>,
    disjunct: Vec<Statement>,
}

impl DisjunctionResolver {
    fn new(cost: rug::Rational, scp: Rc<dyn Scope>, env: Rc<dyn Env>, disjunct: Vec<Statement>) -> Self {
        Self { cost, scp, env, disjunct }
    }
}

impl Resolver for DisjunctionResolver {
    fn intrinsic_cost(&self) -> rug::Rational {
        self.cost.clone()
    }

    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
        for stmt in &self.disjunct {
            execute(&self.scp, self.env.clone(), stmt).map_err(|e| SolverError::RuntimeError(format!("Error executing statement in disjunction resolver: {}", e)))?;
        }

        Ok(())
    }
}

fn expr_to_cost(expr: &Expr) -> rug::Rational {
    match expr {
        Expr::Int(val) => rug::Rational::from_str(val).expect("Failed to parse integer as Rational"),
        Expr::Real(num, den) => rug::Rational::from_str(&format!("{}/{}", num, den)).expect("Failed to parse real number as Rational"),
        Expr::Sum { terms } => terms.iter().map(expr_to_cost).sum(),
        Expr::Opposite { term } => -expr_to_cost(term),
        Expr::Mul { factors } => factors.iter().map(expr_to_cost).product(),
        Expr::Div { left, right } => expr_to_cost(left) / expr_to_cost(right),
        _ => unreachable!("Unexpected expression type for cost calculation"),
    }
}
