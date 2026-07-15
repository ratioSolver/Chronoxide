use serde_json::Value;

pub mod solver;

mod flaws;
mod objects;
mod solver_state;

pub trait ToJson {
    fn to_json(&self) -> Value;
}
