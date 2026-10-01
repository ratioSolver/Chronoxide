pub(super) mod reusable_resource;
pub(super) mod state_variable;

use crate::{SolverError, SolverState, graph::Flaw};
use riddle::scope::Class;
use serde_json::Value;

pub trait Timeline: Class {
    fn extract_flaws(&self, slv: &SolverState) -> Result<Vec<Box<dyn Flaw>>, SolverError>;

    fn to_json(&self, slv: &SolverState) -> Value;
}
