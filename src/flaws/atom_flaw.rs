use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
};
use riddle::{core::Core, env::AtomId, language::AtomKind};
use serde_json::{Value, json};
use tracing::trace;

pub(crate) struct AtomFlaw {
    atom: AtomId,
}

impl AtomFlaw {
    pub(crate) fn new(atom: AtomId) -> Self {
        Self { atom }
    }
}

impl Flaw for AtomFlaw {
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError> {
        let atom = slv.get_atom(self.atom).expect(&format!("Atom {} not found", self.atom));
        let predicate = atom.predicate();

        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().expect("No current flaw found");

        trace!(
            "Expanding AtomFlaw {} for {} {} with predicate {}",
            flw_id,
            match atom.kind() {
                AtomKind::Fact => "fact",
                AtomKind::Goal => "goal",
            },
            self.atom,
            predicate.name()
        );

        unimplemented!()
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "atom",
            "atom": self.atom.to_string()
        })
    }
}

struct GoalResolver {
    atom: AtomId,
}

impl GoalResolver {
    fn new(atom: AtomId) -> Self {
        Self { atom }
    }
}

impl Resolver for GoalResolver {
    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        trace!("Applying GoalResolver for atom {}", self.atom);

        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "goal",
            "atom": self.atom.to_string()
        })
    }
}

struct FactResolver {
    atom: AtomId,
}

impl FactResolver {
    fn new(atom: AtomId) -> Self {
        Self { atom }
    }
}

impl Resolver for FactResolver {
    fn to_json(&self) -> Value {
        json!({
            "kind": "fact",
            "atom": self.atom.to_string()
        })
    }
}
