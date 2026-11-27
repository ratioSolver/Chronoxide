use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use riddle::{
    RiddleError,
    env::Env,
    language::{Disjunction, Expr, Statement, execute},
    scope::Scope,
};
use serde_json::{Value, json};
use std::{rc::Rc, str::FromStr};
use tracing::trace;

pub(crate) struct DisjunctionFlaw {
    disjunction: Disjunction,
}

impl DisjunctionFlaw {
    pub(crate) fn new(disjunction: Disjunction) -> Self {
        Self { disjunction }
    }
}

impl Flaw for DisjunctionFlaw {
    fn expand(&self, slv: &SolverState, flw_id: FlawId) -> Result<(), SolverError> {
        let phi = slv.flaw_phi(flw_id);
        trace!("Expanding DisjunctionFlaw {} with {} disjuncts", flw_id, self.disjunction.disjuncts.len());

        if slv.lit_val(phi) == Some(false) {
            return Ok(());
        }

        let single = self.disjunction.disjuncts.len() == 1;
        for (disjunct, cost) in &self.disjunction.disjuncts {
            let rho = if single { phi } else { slv.new_lit() };
            trace!("Adding disjunction resolver for: {}", disjunct.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(", "));
            let res = Rc::new(DisjunctionResolver::new(expr_to_cost(cost)?, self.disjunction.scp.clone(), self.disjunction.env.clone(), disjunct.to_vec()));
            slv.add_resolver(flw_id, rho, res)?;
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

    fn apply(&self, slv: &SolverState, res_id: ResolverId) -> Result<(), SolverError> {
        for stmt in &self.disjunct {
            trace!("Executing disjunction disjunct: {}", stmt);
            if let Err(e) = execute(&self.scp, self.env.clone(), stmt) {
                return match e {
                    RiddleError::InconsistencyError(msg) => {
                        trace!("DisjunctionResolver inconsistency: {}", msg);
                        let rho = slv.resolver_rho(res_id);
                        slv.add_clause(vec![!rho])
                    }
                    _ => Err(SolverError::RuntimeError(format!("Error executing statement in disjunction resolver: {}", e))),
                };
            }
        }

        Ok(())
    }
}

fn expr_to_cost(expr: &Expr) -> Result<rug::Rational, SolverError> {
    let err = |m: String| SolverError::RuntimeError(m);
    Ok(match expr {
        Expr::Int(val) => rug::Rational::from_str(val).map_err(|e| err(format!("Invalid integer cost '{val}': {e}")))?,
        Expr::Real(num, den) => rug::Rational::from_str(&format!("{num}/{den}")).map_err(|e| err(format!("Invalid real cost {num}/{den}: {e}")))?,
        Expr::Sum { terms } => {
            let mut acc = rug::Rational::from(0);
            for t in terms {
                acc += expr_to_cost(t)?;
            }
            acc
        }
        Expr::Opposite { term } => -expr_to_cost(term)?,
        Expr::Mul { factors } => {
            let mut acc = rug::Rational::from(1);
            for f in factors {
                acc *= expr_to_cost(f)?;
            }
            acc
        }
        Expr::Div { left, right } => {
            let den = expr_to_cost(right)?;
            if den == 0 {
                return Err(err(String::from("Division by zero in disjunct cost")));
            }
            expr_to_cost(left)? / den
        }
        other => return Err(err(format!("Unsupported expression in disjunct cost: {other:?}"))),
    })
}
