pub(super) mod state_variable;

use crate::{SolverError, SolverState};
use riddle::scope::Class;
use serde_json::Value;

pub trait Timeline: Class {
    fn extract_flaws(&self, slv: &SolverState) -> Result<bool, SolverError>;

    fn to_json(&self, slv: &SolverState) -> Value;
}
