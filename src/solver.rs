use riddle::{core::CommonCore, env::Var};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::flaws::{Flaw, Resolver};

pub(crate) struct Solver {
    core: Rc<CommonCore>,
    slv: Weak<Solver>,
    sat: RefCell<consensus::Engine>,
    ac: RefCell<dynamic_ac::Engine>,
    lin: RefCell<linspire::Engine>,
    flaws: RefCell<Vec<Rc<dyn Flaw>>>,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    c_res: Option<Rc<dyn Resolver>>,
    variants: RefCell<HashMap<usize, usize>>,
    instances_by_id: RefCell<Vec<Rc<dyn Var>>>,
}
