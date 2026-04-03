use crate::solver::Solver;
use riddle::serde_json::{Value, json};
use std::rc::Rc;

pub trait Flaw {
    fn solver(&self) -> Rc<Solver>;
    fn phi(&self) -> usize;
    fn to_json(&self) -> Value {
        json!({
            "phi": self.phi()
        })
    }
    fn resolvers(&self) -> Vec<Rc<dyn Resolver>>;
    fn compute_resolvers(self: Rc<Self>);
}

pub trait Resolver {
    fn flaw(&self) -> Rc<dyn Flaw>;
    fn rho(&self) -> usize;
    fn to_json(&self) -> Value {
        json!({
            "flaw": Rc::as_ptr(&self.flaw()) as *const () as usize,
            "rho": self.rho()
        })
    }
    fn ac_constraints(&self) -> Option<Vec<usize>> {
        None
    }
    fn add_ac_constraint(&self, _constraint: usize) {
        unimplemented!()
    }
    fn lin_constraints(&self) -> Option<usize> {
        None
    }
}
