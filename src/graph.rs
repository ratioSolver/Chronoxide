use std::rc::{Rc, Weak};

use crate::solver_state::SolverState;

pub struct Graph {
    slv: Weak<SolverState>,
}

impl Graph {
    pub(crate) fn new(slv: Weak<SolverState>) -> Self {
        Self { slv }
    }

    fn solver(&self) -> Rc<SolverState> {
        self.slv.upgrade().expect("SolverState should never be dropped while in use")
    }
}
