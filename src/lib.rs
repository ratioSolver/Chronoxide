use crate::{
    graph::{FlawId, Graph, ResolverId},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, Var},
    language::Disjunction,
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use semitone::{SeMiTONE, ast};
use serde_json::Value;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::{Rc, Weak},
    str::FromStr,
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};

mod flaws;
mod graph;
mod objects;

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    smt: RefCell<SeMiTONE>,
    graph: RefCell<Graph>,
    ctx: RefCell<Option<(ResolverId, ast::BoolExpr)>>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl SolverState {
    fn new(tx_event: broadcast::Sender<SolverEvent>) -> Rc<Self> {
        let slv = Rc::new_cyclic(|core| SolverState {
            core: {
                let core: Weak<SolverState> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            smt: RefCell::new(SeMiTONE::new()),
            graph: RefCell::new(Graph::new(tx_event.clone())),
            ctx: RefCell::new(None),
            tx_event,
        });
        if slv.read(include_str!("init.rddl")).is_err() {
            panic!("Failed to initialize solver");
        }
        slv
    }

    fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    fn solve(&self) -> Result<(), SolverError> {
        info!("Solving problem...");
        loop {
            let prop_result = self.smt.borrow_mut().propagate();
            match prop_result {
                Ok(_) => {
                    self.build_graph()?;
                    break;
                }
                Err((bt_level, lemma)) => {
                    if self.smt.borrow().decision_level() == 0 {
                        return Err(SolverError::Inconsistent);
                    }
                    self.cancel_until(bt_level);
                    if self.smt.borrow_mut().add_clause(lemma).is_err() {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
        Ok(())
    }

    fn build_graph(&self) -> Result<(), SolverError> {
        info!("Building graph...");
        while !self.graph.borrow().has_estimated_solution(&self.smt.borrow()) {
            let flaw_id = match self.graph.borrow_mut().pop_flaw() {
                Some(flaw_id) => flaw_id,
                None => return Err(SolverError::Inconsistent),
            };
            let mut flaw = self.graph.borrow_mut().take_flaw(flaw_id).expect("Flaw should exist in graph");
            flaw.expand(self)?;
            for resolver_id in flaw.resolvers() {
                let mut resolver = self.graph.borrow_mut().take_resolver(resolver_id).expect("Resolver should exist in graph");
                self.ctx.borrow_mut().replace((resolver_id, self.graph.borrow().resolver_rho(resolver_id).into()));
                resolver.apply(self)?;
                self.graph.borrow_mut().return_resolver(resolver);
            }
            self.graph.borrow_mut().return_flaw(flaw);
        }
        Ok(())
    }

    fn cancel_until(&self, level: usize) {
        self.smt.borrow_mut().cancel_until(level);
    }

    fn to_json(&self) -> Value {
        let json = serde_json::Map::new();
        Value::Object(json)
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

    fn get_slots(&self) -> HashMap<String, Slot> {
        self.core.get_slots()
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
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), if value { ast::BoolExpr::True } else { ast::BoolExpr::False })))
    }
    fn new_bool_var(&self) -> Slot {
        let var = self.smt.borrow_mut().new_bool();
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), var)))
    }
    fn new_int(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), ast::ArithExpr::Const(rug::Rational::from_str(value).expect("Invalid integer literal")))))
    }
    fn new_int_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), self.smt.borrow_mut().new_int())))
    }
    fn new_real(&self, num: &str, den: &str) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), ast::ArithExpr::Const(rug::Rational::from_str(&format!("{}/{}", num, den)).expect("Invalid rational literal")))))
    }
    fn new_real_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), self.smt.borrow_mut().new_real())))
    }
    fn new_string(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), value.into())))
    }
    fn new_string_var(&self) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), String::new())))
    }

    fn sum(&self, sum: &[Slot]) -> Result<Slot, RiddleError> {
        let tp = arith_type(self, sum)?;
        let sum = sum
            .iter()
            .map(|s| match s {
                Slot::Primitive(p) => {
                    if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                        Ok(arith_var.lin.clone())
                    } else {
                        Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", s)))
                    }
                }
                _ => Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", s))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Add(sum)))))
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        if let Slot::Primitive(p) = &term {
            if let Some(bool_var) = p.clone().as_any().downcast_ref::<BoolVar>() {
                Ok(Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), ast::BoolExpr::Not(Box::new(bool_var.lit.clone()))))))
            } else if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_var.var_type().clone(), ast::ArithExpr::Neg(Box::new(arith_var.lin.clone()))))))
            } else {
                Err(RiddleError::TypeError(format!("Expected a boolean variable, got {}", term)))
            }
        } else {
            Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", term)))
        }
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        let tp = arith_type(self, mul)?;
        let mul = mul
            .iter()
            .map(|s| match s {
                Slot::Primitive(p) => {
                    if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                        Ok(arith_var.lin.clone())
                    } else {
                        Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", s)))
                    }
                }
                _ => Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", s))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Mul(mul)))))
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        let tp = arith_type(self, &[left.clone(), right.clone()])?;
        let left_lin = if let Slot::Primitive(p) = &left {
            if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                arith_var.lin.clone()
            } else {
                return Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", left)));
            }
        } else {
            return Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", left)));
        };
        let right_lin = if let Slot::Primitive(p) = &right {
            if let Some(arith_var) = p.clone().as_any().downcast_ref::<ArithVar>() {
                arith_var.lin.clone()
            } else {
                return Err(RiddleError::TypeError(format!("Expected an arithmetic variable, got {}", right)));
            }
        } else {
            return Err(RiddleError::TypeError(format!("Expected a primitive variable, got {}", right)));
        };
        Ok(Slot::Primitive(Rc::new(ArithVar::new(tp, ast::ArithExpr::Div(Box::new(left_lin), Box::new(right_lin))))))
    }

    fn assert(&self, _term: Rc<BoolExpr>) -> bool {
        true
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let domain = instances.iter().map(|id| **id as i32).collect::<Vec<_>>();
        let var = self.smt.borrow_mut().new_enum(domain.clone());
        Ok(Slot::Primitive(Rc::new(EnumVar::new(tp, var))))
    }
    fn new_disjunction(&self, _disjunction: Disjunction) {}

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

pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

#[derive(Clone)]
pub enum SolverEvent {
    NewFlaw { flaw_id: FlawId, phi: String, causes: Vec<ResolverId>, supports: Vec<ResolverId>, status: Option<bool>, cost: f64, data: Value },
    FlawCostUpdate { flaw_id: FlawId, cost: f64 },
    FlawStatusUpdate { flaw_id: FlawId, status: Option<bool> },
    CurrentFlaw(Option<FlawId>),
    NewResolver { resolver_id: ResolverId, rho: String, flaw_id: FlawId, sub_flaws: Vec<FlawId>, intrinsic_cost: f64, status: Option<bool>, data: Value },
    ResolverStatusUpdate { resolver_id: ResolverId, status: Option<bool> },
    CurrentResolver(Option<ResolverId>),
    NewCausalLink { flaw_id: FlawId, resolver_id: ResolverId },
    StateUpdate { json: Value },
}
