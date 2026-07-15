use crate::objects::{BoolVar, EnumVar, IntVar, RealVar, StringVar};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot},
    language::Disjunction,
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use serde_json::{Value, json};
use std::{
    collections::HashMap,
    rc::{Rc, Weak},
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace, warn};
use z3::{
    Goal,
    ast::{Bool, Int, Real},
};

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
    constrs: Goal,
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
            constrs: Goal::new(false, false, false),
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
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), Bool::from_bool(value))))
    }
    fn new_bool_var(&self) -> Slot {
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), Bool::fresh_const("b"))))
    }
    fn new_int(&self, value: i64) -> Slot {
        Slot::Primitive(Rc::new(IntVar::new(self.int_type(), Int::from_i64(value))))
    }
    fn new_int_var(&self) -> Slot {
        Slot::Primitive(Rc::new(IntVar::new(self.int_type(), Int::fresh_const("i"))))
    }
    fn new_real(&self, num: i64, den: i64) -> Slot {
        Slot::Primitive(Rc::new(RealVar::new(self.real_type(), Real::from_rational(num, den))))
    }
    fn new_real_var(&self) -> Slot {
        Slot::Primitive(Rc::new(RealVar::new(self.real_type(), Real::fresh_const("r"))))
    }
    fn new_string(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), z3::ast::String::from(value))))
    }
    fn new_string_var(&self) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), z3::ast::String::fresh_const("s"))))
    }

    fn sum(&self, sum: &[Slot]) -> Result<Slot, RiddleError> {
        let tp = arith_type(self, sum)?;
        match tp.name() {
            "int" => {
                let ints = sum
                    .iter()
                    .map(|s| match s {
                        Slot::Primitive(var) => {
                            if let Some(var) = var.clone().as_any().downcast_ref::<IntVar>() {
                                Ok(var.lit.clone())
                            } else {
                                Err(RiddleError::RuntimeError("Expected int".to_string()))
                            }
                        }
                        _ => return Err(RiddleError::TypeError("Expected int".to_string())),
                    })
                    .collect::<Result<Vec<_>, RiddleError>>()?;
                Ok(Slot::Primitive(Rc::new(IntVar::new(self.int_type(), Int::add(&ints)))))
            }
            "real" => {
                let reals = sum
                    .iter()
                    .map(|s| match s {
                        Slot::Primitive(var) => {
                            if let Some(var) = var.clone().as_any().downcast_ref::<IntVar>() {
                                Ok(var.lit.to_real())
                            } else if let Some(var) = var.clone().as_any().downcast_ref::<RealVar>() {
                                Ok(var.lit.clone())
                            } else {
                                Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                            }
                        }
                        _ => return Err(RiddleError::TypeError("Expected real".to_string())),
                    })
                    .collect::<Result<Vec<_>, RiddleError>>()?;
                Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), Real::add(&reals)))))
            }
            _ => Err(RiddleError::TypeError("Expected int or real".to_string())),
        }
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        match term {
            Slot::Primitive(var) => {
                if let Some(var) = var.clone().as_any().downcast_ref::<BoolVar>() {
                    Ok(Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), var.lit.not()))))
                } else if let Some(var) = var.clone().as_any().downcast_ref::<IntVar>() {
                    Ok(Slot::Primitive(Rc::new(IntVar::new(self.int_type(), var.lit.unary_minus()))))
                } else if let Some(var) = var.clone().as_any().downcast_ref::<RealVar>() {
                    Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), var.lit.unary_minus()))))
                } else {
                    Err(RiddleError::RuntimeError("Expected bool, int or real".to_string()))
                }
            }
            _ => Err(RiddleError::TypeError("Expected bool, int or real".to_string())),
        }
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        let tp = arith_type(self, mul)?;
        match tp.name() {
            "int" => {
                let ints = mul
                    .iter()
                    .map(|s| match s {
                        Slot::Primitive(var) => {
                            if let Some(var) = var.clone().as_any().downcast_ref::<IntVar>() {
                                Ok(var.lit.clone())
                            } else {
                                Err(RiddleError::RuntimeError("Expected int".to_string()))
                            }
                        }
                        _ => return Err(RiddleError::TypeError("Expected int".to_string())),
                    })
                    .collect::<Result<Vec<_>, RiddleError>>()?;
                Ok(Slot::Primitive(Rc::new(IntVar::new(self.int_type(), Int::mul(&ints)))))
            }
            "real" => {
                let reals = mul
                    .iter()
                    .map(|s| match s {
                        Slot::Primitive(var) => {
                            if let Some(var) = var.clone().as_any().downcast_ref::<IntVar>() {
                                Ok(var.lit.to_real())
                            } else if let Some(var) = var.clone().as_any().downcast_ref::<RealVar>() {
                                Ok(var.lit.clone())
                            } else {
                                Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                            }
                        }
                        _ => return Err(RiddleError::TypeError("Expected real".to_string())),
                    })
                    .collect::<Result<Vec<_>, RiddleError>>()?;
                Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), Real::mul(&reals)))))
            }
            _ => Err(RiddleError::TypeError("Expected int or real".to_string())),
        }
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        match (left, right) {
            (Slot::Primitive(left_var), Slot::Primitive(right_var)) => {
                if let Some(left_var) = left_var.clone().as_any().downcast_ref::<IntVar>() {
                    if let Some(right_var) = right_var.clone().as_any().downcast_ref::<IntVar>() {
                        Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), left_var.lit.to_real().div(&right_var.lit.to_real())))))
                    } else if let Some(right_var) = right_var.clone().as_any().downcast_ref::<RealVar>() {
                        Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), left_var.lit.to_real().div(&right_var.lit)))))
                    } else {
                        Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                    }
                } else if let Some(left_var) = left_var.clone().as_any().downcast_ref::<RealVar>() {
                    if let Some(right_var) = right_var.clone().as_any().downcast_ref::<IntVar>() {
                        Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), left_var.lit.div(&right_var.lit.to_real())))))
                    } else if let Some(right_var) = right_var.clone().as_any().downcast_ref::<RealVar>() {
                        Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), left_var.lit.div(&right_var.lit)))))
                    } else {
                        Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                    }
                } else {
                    Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                }
            }
            _ => Err(RiddleError::TypeError("Expected int or real".to_string())),
        }
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        unimplemented!()
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let var = Int::fresh_const("e");
        for id in instances {
            let instance_var = Int::from_i64(**id as i64);
            let eq = var.eq(&instance_var);
            self.constrs.assert(&eq);
        }
        Ok(Slot::Primitive(Rc::new(EnumVar::new(tp, var))))
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        unimplemented!()
    }

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        self.core.new_object(class)
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        self.core.get_object(id)
    }
    fn new_atom(&self, predicate: Rc<Predicate>, fact: bool, args: HashMap<String, Slot>) -> AtomId {
        let atm = self.core.new_atom(predicate, fact, args);
        atm
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}
