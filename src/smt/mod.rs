pub mod ast;
mod lin;
mod lra;
mod proxy;
mod rational;
mod sat;

use crate::smt::{lra::LraTheory, proxy::ProxyRegistry, sat::SatSolver};

pub struct SmtSolver {
    registry: ProxyRegistry,
    lra: LraTheory,
    sat: SatSolver,
}

impl SmtSolver {
    pub fn new() -> Self {
        Self { registry: ProxyRegistry::new(), lra: LraTheory::new(), sat: SatSolver::new() }
    }
}
