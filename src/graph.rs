use semitone::ast::BoolExpr;

pub type FlawId = usize;
pub type ResolverId = usize;

pub(super) struct Graph {
    pub(super) flaws: Vec<Box<dyn Flaw>>,
    pub(super) resolvers: Vec<Box<dyn Resolver>>,
}

impl Graph {
    pub(super) fn new() -> Self {
        Graph { flaws: Vec::new(), resolvers: Vec::new() }
    }
}

pub trait Flaw {
    fn id(&self) -> FlawId;

    fn phi(&self) -> &BoolExpr;

    fn causes(&self) -> &[ResolverId];
    fn supports(&self) -> &[ResolverId];

    fn resolvers(&self) -> &[ResolverId];

    fn estimated_cost(&self) -> f64;
    fn set_estimated_cost(&mut self, cost: f64);
}

pub trait Resolver {
    fn id(&self) -> ResolverId;

    fn rho(&self) -> &BoolExpr;

    fn flaw(&self) -> FlawId;

    fn intrinsic_cost(&self) -> f64;

    fn sub_flaws(&self) -> &[FlawId];
}
