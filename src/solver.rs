use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot},
    language::Disjunction,
    scope::{Class, Field, Function, Predicate, Scope, Type},
};
use serde_json::{Value, json};
use std::{
    collections::HashMap,
    rc::{Rc, Weak},
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace, warn};

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

#[derive(Debug)]
pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

#[derive(Clone)]
pub enum SolverEvent {
    NewFlaw {},
    FlawCostUpdate {},
    FlawStatusUpdate {},
    CurrentFlaw(),
    NewResolver {},
    ResolverStatusUpdate {},
    CurrentResolver(),
    NewCausalLink {},
}

#[derive(Clone)]
pub struct Solver {
    tx_cmd: mpsc::Sender<SolverCommand>,
    pub tx_event: broadcast::Sender<SolverEvent>,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Self {
        let (tx_cmd, mut rx_cmd) = mpsc::channel(100);
        let (tx_event, _) = broadcast::channel(100);
        let tx_event_clone = tx_event.clone();
        tokio::task::spawn_blocking(move || {
            let state = SolverState::new(tx_event_clone);

            while let Some(cmd) = rx_cmd.blocking_recv() {
                match cmd {
                    SolverCommand::ReadRiDDle(riddle, responder) => match state.read(&riddle) {
                        Ok(_) => {
                            let _ = responder.send(Ok(()));
                        }
                        Err(e) => {
                            let _ = responder.send(Err(e));
                        }
                    },
                    SolverCommand::Solve(responder) => match state.solve() {
                        Ok(_) => {
                            let _ = responder.send(Ok(()));
                        }
                        Err(e) => {
                            let _ = responder.send(Err(e));
                        }
                    },
                    SolverCommand::ToJson(responder) => {
                        let json = state.to_json();
                        let _ = responder.send(Ok(json));
                    }
                }
            }
        });
        Self { tx_cmd, tx_event }
    }

    pub async fn read(&self, riddle: String) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ReadRiDDle(riddle, reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }

    pub async fn solve(&self) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::Solve(reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }

    pub async fn to_json(&self) -> Result<Value, SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ToJson(reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }
}

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl SolverState {
    fn new(tx_event: broadcast::Sender<SolverEvent>) -> Rc<Self> {
        Rc::new_cyclic(|core| SolverState {
            core: {
                let core: Weak<SolverState> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            tx_event,
        })
    }

    fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    fn solve(&self) -> Result<(), SolverError> {
        trace!("Solving");
        unimplemented!()
    }

    fn to_json(&self) -> Value {
        let mut slv = json!({
            // "flaws": self.flaws.borrow().iter().map(|f| f.to_json()).collect::<Vec<_>>(),
            // "resolvers": self.resolvers.borrow().iter().map(|r| r.to_json()).collect::<Vec<_>>(),
        });
        // if let Some(current_flaw) = self.c_flaw.borrow().as_ref() {
        //     slv["current_flaw"] = json!(current_flaw.0);
        // }
        // if let Some(current_resolver) = self.c_res.borrow().as_ref() {
        //     slv["current_resolver"] = json!(current_resolver.0);
        // }
        slv
    }
}

impl Scope for SolverState {
    fn core(&self) -> Rc<dyn Core> {
        self.slv.upgrade().expect("SolverState should never be dropped while in use")
    }
    fn scope(&self) -> Option<Rc<dyn Scope>> {
        None
    }

    fn get_fields(&self) -> Vec<Rc<Field>> {
        self.core.get_fields()
    }
    fn get_field(&self, name: &str) -> Option<Rc<Field>> {
        self.core.get_field(name)
    }
    fn get_function(&self, name: &str, types: &[Rc<dyn Type>]) -> Option<Rc<Function>> {
        self.core.get_function(name, types)
    }
    fn get_type(&self, name: &str) -> Option<Rc<dyn Type>> {
        self.core.get_type(name)
    }
    fn get_predicate(&self, name: &str) -> Option<Rc<Predicate>> {
        self.core.get_predicate(name)
    }
}

impl Env for SolverState {
    fn parent(&self) -> Option<Rc<dyn Env>> {
        None
    }

    fn get(&self, name: &str) -> Option<Slot> {
        self.core.get(name)
    }

    fn set(&self, name: String, value: Slot) {
        self.core.set(name, value);
    }
}

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Slot {
        unimplemented!()
    }
    fn new_bool_var(&self) -> Slot {
        unimplemented!()
    }
    fn new_int(&self, value: i64) -> Slot {
        unimplemented!()
    }
    fn new_int_var(&self) -> Slot {
        unimplemented!()
    }
    fn new_real(&self, num: i64, den: i64) -> Slot {
        unimplemented!()
    }
    fn new_real_var(&self) -> Slot {
        unimplemented!()
    }
    fn new_string(&self, value: &str) -> Slot {
        unimplemented!()
    }
    fn new_string_var(&self) -> Slot {
        unimplemented!()
    }

    fn sum(&self, sum: &[Slot]) -> Result<Slot, RiddleError> {
        unimplemented!()
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        unimplemented!()
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        unimplemented!()
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        unimplemented!()
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        unimplemented!()
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        unimplemented!()
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        unimplemented!()
    }

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        unimplemented!()
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        unimplemented!()
    }
    fn new_atom(&self, predicate: Rc<Predicate>, fact: bool, args: HashMap<String, Slot>) -> AtomId {
        unimplemented!()
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        unimplemented!()
    }
}
