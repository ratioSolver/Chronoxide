use semitone::ast::BoolExpr;

pub type FlawId = usize;
pub type ResolverId = usize;

pub(super) struct Graph {
    flaws: Vec<Box<dyn Flaw>>,
    resolvers: Vec<Box<dyn Resolver>>,
    current_flaw: Option<FlawId>,
    current_resolver: Option<ResolverId>,
}

impl Graph {
    pub(super) fn new() -> Self {
        Graph { flaws: Vec::new(), resolvers: Vec::new(), current_flaw: None, current_resolver: None }
    }

    pub(super) fn get_flaw(&self, id: FlawId) -> &dyn Flaw {
        &*self.flaws[id]
    }

    pub(super) fn add_flaw(&mut self, flaw: Box<dyn Flaw>) -> FlawId {
        let id = flaw.id();
        assert_eq!(id, self.flaws.len());
        self.flaws.push(flaw);
        id
    }

    pub(super) fn get_resolver(&self, id: ResolverId) -> &dyn Resolver {
        &*self.resolvers[id]
    }

    pub(super) fn add_resolver(&mut self, resolver: Box<dyn Resolver>) -> ResolverId {
        let id = resolver.id();
        assert_eq!(id, self.resolvers.len());
        self.resolvers.push(resolver);
        id
    }

    pub(super) fn set_current_flaw(&mut self, flaw_id: FlawId) {
        self.current_flaw = Some(flaw_id);
    }

    pub(super) fn get_current_flaw(&self) -> Option<&dyn Flaw> {
        self.current_flaw.map(|id| &*self.flaws[id])
    }

    pub(super) fn set_current_resolver(&mut self, resolver_id: ResolverId) {
        self.current_resolver = Some(resolver_id);
    }

    pub(super) fn get_current_resolver(&self) -> Option<&dyn Resolver> {
        self.current_resolver.map(|id| &*self.resolvers[id])
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
