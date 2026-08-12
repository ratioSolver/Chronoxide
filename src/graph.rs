use std::{collections::VecDeque, rc::Rc};

use riddle::core::Core;
use semitone::ast::BoolExpr;

use crate::SolverError;

pub type FlawId = usize;
pub type ResolverId = usize;

pub(super) struct Graph {
    flaws: Vec<Option<Box<dyn Flaw>>>,
    current_flaw: Option<FlawId>,
    resolvers: Vec<Option<Box<dyn Resolver>>>,
    current_resolver: Option<ResolverId>,
    pub(super) flaw_q: VecDeque<FlawId>,
}

impl Graph {
    pub(super) fn new() -> Self {
        Graph {
            flaws: Vec::new(),
            current_flaw: None,
            resolvers: Vec::new(),
            current_resolver: None,
            flaw_q: VecDeque::new(),
        }
    }

    pub(super) fn get_flaw(&self, id: FlawId) -> &dyn Flaw {
        self.flaws[id].as_ref().unwrap().as_ref()
    }

    pub(super) fn get_flaw_mut(&mut self, id: FlawId) -> &mut dyn Flaw {
        self.flaws[id].as_mut().unwrap().as_mut()
    }

    pub(super) fn add_flaw(&mut self, mut flaw: Box<dyn Flaw>) -> FlawId {
        let id = self.flaws.len();
        flaw.set_id(id);
        self.flaws.push(Some(flaw));
        self.flaw_q.push_back(id);
        id
    }

    pub(super) fn take_flaw(&mut self, id: FlawId) -> Box<dyn Flaw> {
        self.flaws[id].take().expect("Flaw already taken or missing!")
    }

    pub(super) fn return_flaw(&mut self, id: FlawId, flaw: Box<dyn Flaw>) {
        self.flaws[id] = Some(flaw);
    }

    pub(super) fn get_current_flaw(&self) -> Option<&dyn Flaw> {
        self.current_flaw.map(|id| self.flaws[id].as_ref().unwrap().as_ref())
    }

    pub(super) fn set_current_flaw(&mut self, flaw_id: Option<FlawId>) {
        self.current_flaw = flaw_id;
    }

    pub(super) fn get_resolver(&self, id: ResolverId) -> &dyn Resolver {
        self.resolvers[id].as_ref().unwrap().as_ref()
    }

    pub(super) fn get_resolver_mut(&mut self, id: ResolverId) -> &mut dyn Resolver {
        self.resolvers[id].as_mut().unwrap().as_mut()
    }

    pub(super) fn add_resolver(&mut self, mut resolver: Box<dyn Resolver>) -> ResolverId {
        let id = self.resolvers.len();
        resolver.set_id(id);
        self.resolvers.push(Some(resolver));
        id
    }

    pub(super) fn take_resolver(&mut self, id: ResolverId) -> Box<dyn Resolver> {
        self.resolvers[id].take().expect("Resolver already taken or missing!")
    }

    pub(super) fn return_resolver(&mut self, id: ResolverId, resolver: Box<dyn Resolver>) {
        self.resolvers[id] = Some(resolver);
    }

    pub(super) fn get_current_resolver(&self) -> Option<&dyn Resolver> {
        self.current_resolver.map(|id| self.resolvers[id].as_ref().unwrap().as_ref())
    }

    pub(super) fn set_current_resolver(&mut self, resolver_id: Option<ResolverId>) {
        self.current_resolver = resolver_id;
    }
}

pub trait Flaw {
    fn id(&self) -> FlawId;
    fn set_id(&mut self, id: FlawId);

    fn phi(&self) -> &BoolExpr;

    fn causes(&self) -> &[ResolverId];
    fn supports(&self) -> &[ResolverId];

    fn is_expanded(&self) -> bool;
    fn expand(&mut self, core: Rc<dyn Core>) -> Result<Vec<Box<dyn Resolver>>, SolverError>;

    fn resolvers(&self) -> &[ResolverId];

    fn estimated_cost(&self) -> f64;
    fn set_estimated_cost(&mut self, cost: f64);
}

pub trait Resolver {
    fn id(&self) -> ResolverId;
    fn set_id(&mut self, id: ResolverId);

    fn rho(&self) -> &BoolExpr;

    fn flaw(&self) -> FlawId;

    fn intrinsic_cost(&self) -> f64;

    fn apply(&mut self, core: Rc<dyn Core>) -> Result<(), SolverError>;

    fn sub_flaws(&self) -> &[FlawId];
}
