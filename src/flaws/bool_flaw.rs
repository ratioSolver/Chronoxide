use riddle::env::BoolExpr;

use crate::graph::{Flaw, FlawId, ResolverId};

pub(crate) struct BoolFlaw {
    id: FlawId,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    expr: BoolExpr,
}

impl BoolFlaw {
    pub(crate) fn new(cause: Option<ResolverId>, expr: BoolExpr) -> Self {
        Self {
            id: FlawId::default(),
            causes: cause.into_iter().collect(),
            resolvers: Vec::with_capacity(2),
            expr,
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
    fn causes(&self) -> Vec<ResolverId> {
        self.causes.clone()
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }
}
