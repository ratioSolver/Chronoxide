use riddle::serde_json::Value;

pub mod solver;

mod flaws;
mod graph;
mod objects;

pub trait ToJson {
    fn to_json(&self) -> Value;
}
