use crate::{
    SolverEvent,
    flaws::{Flaw, Resolver},
};
use tokio::sync::broadcast;

pub struct Graph {
    flaws: Vec<Option<Box<dyn Flaw>>>,
    resolvers: Vec<Option<Box<dyn Resolver>>>,
}

impl Graph {
    pub(super) fn new(tx_event: broadcast::Sender<SolverEvent>) -> Self {
        Self { flaws: Vec::new(), resolvers: Vec::new() }
    }
}
