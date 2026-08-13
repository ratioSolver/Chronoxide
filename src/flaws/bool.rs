use std::rc::Rc;

use crate::{
    SolverError,
    graph::{Flaw, FlawId, Resolver, ResolverId},
};
use riddle::core::Core;
use semitone::ast::{self, BoolExpr};

pub(super) struct BoolFlaw {
    id: FlawId,
    phi: BoolExpr,

    causes: Vec<ResolverId>,
    supports: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    target: BoolExpr,
}

impl BoolFlaw {
    pub(super) fn new(phi: BoolExpr, target: BoolExpr) -> Self {
        Self {
            id: 0,
            phi,
            causes: Vec::new(),
            supports: Vec::new(),
            resolvers: Vec::new(),
            estimated_cost: f64::INFINITY,
            is_expanded: false,
            target,
        }
    }
}

impl Flaw for BoolFlaw {
    fn id(&self) -> FlawId {
        self.id
    }
    fn set_id(&mut self, id: FlawId) {
        self.id = id;
    }

    fn phi(&self) -> &BoolExpr {
        &self.phi
    }

    fn causes(&self) -> &[ResolverId] {
        &self.causes
    }
    fn supports(&self) -> &[ResolverId] {
        &self.supports
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

    fn expand(&mut self, _core: Rc<dyn Core>) -> Result<Vec<Box<dyn Resolver>>, SolverError> {
        self.is_expanded = true;

        let rho_true = self.target.clone();
        let rho_false = !self.target.clone();

        let res_true = Box::new(BoolResolver::new(self.id, rho_true, true));
        let res_false = Box::new(BoolResolver::new(self.id, rho_false, false));

        Ok(vec![res_true, res_false])
    }
}

struct BoolResolver {
    id: ResolverId,
    flaw: FlawId,
    rho: BoolExpr,
    sub_flaws: Vec<FlawId>,
    value: bool,
}

impl BoolResolver {
    fn new(flaw: FlawId, rho: BoolExpr, value: bool) -> Self {
        Self { id: 0, flaw, rho, sub_flaws: Vec::new(), value }
    }
}

impl Resolver for BoolResolver {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> &BoolExpr {
        &self.rho
    }

    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn intrinsic_cost(&self) -> f64 {
        1f64
    }

    fn sub_flaws(&self) -> &[FlawId] {
        &self.sub_flaws
    }

    fn apply(&mut self, core: Rc<dyn Core>) -> Result<(), SolverError> {
        Ok(())
    }
}
