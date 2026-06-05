use crate::{
    ToJson,
    flaws::{Flaw, FlawData, FlawId, Resolver, ResolverData, ResolverId},
    solver_state::SolverState,
};
use linarith::Rational;
use serde_json::Value;
use std::rc::{Rc, Weak};
use watchsat::{Lit, VarId};

pub(crate) struct ClauseFlaw {
    flw: FlawData,
    lits: Vec<Lit>,
}

impl ClauseFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, cause: Option<ResolverId>, lits: Vec<Lit>) -> Rc<Self> {
        Rc::new(Self { flw: FlawData::new(slv, id, phi, cause.into_iter().collect()), lits })
    }
}

impl Flaw for ClauseFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.flw.solver()
    }
    fn id(&self) -> FlawId {
        self.flw.id()
    }
    fn phi(&self) -> VarId {
        self.flw.phi()
    }
}

impl ToJson for ClauseFlaw {
    fn to_json(&self) -> Value {
        let mut json = self.flw.to_json();
        json["kind"] = "clause".into();
        json["lits"] = self.lits.iter().map(|lit| lit.to_string()).collect::<Vec<_>>().into();
        json
    }
}

struct ClauseResolver {
    res: ResolverData,
    lit: Lit,
}

impl ClauseResolver {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, lit: Lit) -> Rc<Self> {
        Rc::new(Self { res: ResolverData::new(slv, id, flaw, lit.var(), Rational::from(1)), lit })
    }
}

impl Resolver for ClauseResolver {
    fn solver(&self) -> Rc<SolverState> {
        self.res.solver()
    }
    fn id(&self) -> ResolverId {
        self.res.id()
    }
    fn flaw(&self) -> FlawId {
        self.res.flaw()
    }
    fn rho(&self) -> VarId {
        self.res.rho()
    }
}

impl ToJson for ClauseResolver {
    fn to_json(&self) -> Value {
        let mut json = self.res.to_json();
        json["lit"] = self.lit.to_string().into();
        json
    }
}
