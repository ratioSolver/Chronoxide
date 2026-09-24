use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use riddle::{
    env::Env,
    language::{Disjunction, Expr, Statement, execute},
    scope::Scope,
};
use serde_json::Value;
use std::{rc::Rc, str::FromStr};

pub(crate) struct DisjunctionFlaw {
    id: FlawId,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    disjunction: Disjunction,
}

impl DisjunctionFlaw {
    pub(crate) fn new(cause: Option<ResolverId>, disjunction: Disjunction) -> Self {
        Self {
            id: FlawId::default(),
            causes: cause.into_iter().collect(),
            resolvers: Vec::with_capacity(disjunction.disjuncts.len()),
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
    fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }

    fn expand(&mut self, slv: &SolverState) -> Result<(), crate::SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();

        for (disjunct, cost) in &self.disjunction.disjuncts {
            let rho = smt.new_lit();
            let resolver_id = graph.add_resolver(&mut smt, Box::new(DisjunctionResolver::new(self.id, expr_to_cost(cost), self.disjunction.scp.clone(), self.disjunction.env.clone(), disjunct.to_vec())), rho)?;
            self.resolvers.push(resolver_id);
        }

        Ok(())
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }

    fn to_json(&self) -> Value {
        Value::Null
    }
}

struct DisjunctionResolver {
    id: ResolverId,
    flaw: FlawId,
    cost: rug::Rational,
    preconditions: Vec<FlawId>,
    scp: Rc<dyn Scope>,
    env: Rc<dyn Env>,
    disjunct: Vec<Statement>,
}

impl DisjunctionResolver {
    fn new(flaw: FlawId, cost: rug::Rational, scp: Rc<dyn Scope>, env: Rc<dyn Env>, disjunct: Vec<Statement>) -> Self {
        Self { id: ResolverId::default(), flaw, cost, preconditions: vec![], scp, env, disjunct }
    }
}

impl Resolver for DisjunctionResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn intrinsic_cost(&self) -> rug::Rational {
        self.cost.clone()
    }

    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
        for stmt in &self.disjunct {
            execute(&self.scp, self.env.clone(), stmt).map_err(|e| SolverError::RuntimeError(format!("Error executing statement in disjunction resolver: {}", e)))?;
        }

        Ok(())
    }

    fn preconditions(&self) -> Vec<FlawId> {
        self.preconditions.clone()
    }

    fn add_precondition(&mut self, flaw_id: FlawId) {
        self.preconditions.push(flaw_id);
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
