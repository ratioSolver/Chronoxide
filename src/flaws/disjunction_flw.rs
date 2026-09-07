use std::rc::Rc;

use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use riddle::{
    env::Env,
    language::{Disjunction, Expr, Statement, execute},
    scope::Scope,
};
use semitone::Lit;

pub(crate) struct DisjunctionFlaw {
    id: FlawId,
    phi: Lit,
    status: Option<bool>,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    disjunction: Disjunction,
}

impl DisjunctionFlaw {
    pub(crate) fn new(phi: Lit, status: Option<bool>, cause: Option<ResolverId>, disjunction: Disjunction) -> Self {
        assert!(status != Some(false), "Cannot create a ClauseFlaw with status Some(false)");
        Self {
            id: 0,
            phi,
            status,
            causes: cause.into_iter().collect(),
            resolvers: Vec::new(),
            estimated_cost: f64::INFINITY,
            is_expanded: false,
            disjunction,
        }
    }
}

impl Flaw for DisjunctionFlaw {
    fn id(&self) -> FlawId {
        self.id
    }
    fn set_id(&mut self, id: FlawId) {
        self.id = id;
    }

    fn phi(&self) -> Lit {
        self.phi
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn causes(&self) -> &[ResolverId] {
        &self.causes
    }
    fn resolvers(&self) -> &[ResolverId] {
        &self.resolvers
    }
    fn add_resolver(&mut self, id: ResolverId) {
        self.resolvers.push(id);
    }

    fn estimated_cost(&self) -> f64 {
        self.estimated_cost
    }
    fn set_estimated_cost(&mut self, cost: f64) {
        self.estimated_cost = cost;
    }

    fn is_expanded(&self) -> bool {
        self.is_expanded
    }

    fn expand(&mut self, state: &SolverState) -> Result<Vec<Box<dyn Resolver>>, SolverError> {
        self.is_expanded = true;

        let mut resolvers: Vec<Box<dyn Resolver>> = Vec::with_capacity(self.disjunction.disjuncts.len());
        for (disjunct, cost) in &self.disjunction.disjuncts {
            let rho = state.smt.borrow_mut().new_bool();
            let rho = state.smt.borrow_mut().track_expr(rho);
            let resolver = DisjunctionResolver::new(self.id, rho, None, self.disjunction.scp.clone(), self.disjunction.env.clone(), disjunct.to_vec(), expr_to_cost(cost));
            resolvers.push(Box::new(resolver));
        }

        Ok(resolvers)
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "disjunction"
        })
    }
}

fn expr_to_cost(expr: &Expr) -> f64 {
    match expr {
        Expr::Int(val) => val.parse::<f64>().expect("Failed to parse integer as f64"),
        Expr::Real(num, den) => {
            let num = num.parse::<f64>().expect("Failed to parse numerator as f64");
            let den = den.parse::<f64>().expect("Failed to parse denominator as f64");
            num / den
        }
        Expr::Sum { terms } => terms.iter().map(expr_to_cost).sum(),
        Expr::Opposite { term } => -expr_to_cost(term),
        Expr::Mul { factors } => factors.iter().map(expr_to_cost).product(),
        Expr::Div { left, right } => expr_to_cost(left) / expr_to_cost(right),
        _ => unreachable!("Unexpected expression type for cost calculation"),
    }
}

struct DisjunctionResolver {
    id: ResolverId,
    flaw: FlawId,
    rho: Lit,
    status: Option<bool>,
    sub_flaws: Vec<FlawId>,
    scp: Rc<dyn Scope>,
    env: Rc<dyn Env>,
    disjunct: Vec<Statement>,
    cost: f64,
}

impl DisjunctionResolver {
    fn new(flaw: FlawId, rho: Lit, status: Option<bool>, scp: Rc<dyn Scope>, env: Rc<dyn Env>, disjunct: Vec<Statement>, cost: f64) -> Self {
        Self { id: 0, flaw, rho, status, sub_flaws: Vec::new(), scp, env, disjunct, cost }
    }
}

impl Resolver for DisjunctionResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> Lit {
        self.rho
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn intrinsic_cost(&self) -> f64 {
        self.cost
    }

    fn sub_flaws(&self) -> &[FlawId] {
        &self.sub_flaws
    }
    fn add_sub_flaw(&mut self, id: FlawId) {
        self.sub_flaws.push(id);
    }

    fn apply(&mut self, _state: &SolverState) -> Result<(), SolverError> {
        for stmt in &self.disjunct {
            execute(&self.scp, self.env.clone(), stmt).map_err(|e| SolverError::RuntimeError(format!("Error executing statement in disjunction resolver: {}", e)))?;
        }

        Ok(())
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "kind": "lit"
        })
    }
}
