use crate::{ac, lin};

pub struct Solver {
    ac: ac::solver::Solver,
    lin: lin::solver::Solver,
}
