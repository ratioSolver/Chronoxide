use crate::{
    ToJson,
    flaws::{Flaw, Resolver},
    solver_state::SolverState,
};
use serde_json::{Value, json};
use std::rc::{Rc, Weak};
use watchsat::LBool;

pub struct Graph {
    slv: Weak<SolverState>,
    flaws: Vec<Box<dyn Flaw>>,
    resolvers: Vec<Box<dyn Resolver>>,
}

impl Graph {
    pub(crate) fn new(slv: Weak<SolverState>) -> Self {
        Self { slv, flaws: Vec::new(), resolvers: Vec::new() }
    }

    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("SolverState should never be dropped while in use")
    }

    pub fn get_num_flaws(&self) -> usize {
        self.flaws.len()
    }

    pub fn get_num_resolvers(&self) -> usize {
        self.resolvers.len()
    }
}

impl ToJson for LBool {
    fn to_json(&self) -> Value {
        match self {
            LBool::True => true.into(),
            LBool::False => false.into(),
            LBool::Undef => Value::Null,
        }
    }
}

impl ToJson for Graph {
    fn to_json(&self) -> Value {
        json!({
            "flaws": self.flaws.iter().map(|f| f.to_json()).collect::<Vec<_>>(),
            "resolvers": self.resolvers.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
        })
    }
}
