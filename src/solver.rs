use crate::{
    graph::{AtomFlaw, DisjunctionFlaw, Flaw, FlawId, Resolver, ResolverId, State},
    objects::{BoolVar, EnumVar, IntVar, RealVar, StringVar},
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot},
    language::Disjunction,
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};
use z3::ast::{Bool, Int, Real};

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
    NewFlaw { flaw_id: FlawId, causes: Vec<ResolverId>, supports: Vec<ResolverId>, state: State, cost: f32, data: Value },
    FlawCostUpdate { flaw_id: FlawId, cost: f32 },
    FlawStateUpdate { flaw_id: FlawId, state: State },
    CurrentFlaw(Option<FlawId>),
    NewResolver { resolver_id: ResolverId, intrinsic_cost: f32, state: State, data: Value },
    ResolverStateUpdate { resolver_id: ResolverId, state: State },
    CurrentResolver(Option<ResolverId>),
    NewCausalLink { flaw_id: FlawId, resolver_id: ResolverId },
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
    smt: z3::Solver,
    atom_flaws: RefCell<Vec<FlawId>>,
    flaws: RefCell<Vec<Box<dyn Flaw>>>,
    resolvers: RefCell<Vec<Box<dyn Resolver>>>,
    c_flaw: RefCell<Option<FlawId>>,
    c_res: RefCell<Option<ResolverId>>,
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
            atom_flaws: RefCell::new(Vec::new()),
            flaws: RefCell::new(Vec::new()),
            resolvers: RefCell::new(Vec::new()),
            c_flaw: RefCell::new(None),
            c_res: RefCell::new(None),
            smt: z3::Solver::new(),
            tx_event,
        })
    }

    fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    fn solve(&self) -> Result<(), SolverError> {
        info!("Solving problem...");
        self.build_graph()?;
        Ok(())
    }

    fn build_graph(&self) -> Result<(), SolverError> {
        info!("Building graph...");
        Ok(())
    }

    pub(crate) fn add_flaw(&self, flaw: Box<dyn Flaw>) {
        let flaw_id = flaw.id();
        trace!("Adding flaw: {} ({})", flaw_id, flaw.phi());
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id,
            causes: flaw.causes(),
            supports: flaw.supports(),
            state: flaw.get_state(),
            cost: flaw.get_cost(),
            data: flaw.to_json(),
        });
        self.flaws.borrow_mut().push(flaw);
    }

    pub(crate) fn add_resolver(&self, flaw: &mut impl Flaw, resolver: Box<dyn Resolver>) {
        let resolver_id = resolver.id();
        trace!("Adding resolver: {} ({})", resolver_id, resolver.rho());
        let flaw_id = flaw.id();
        assert!(flaw_id == resolver.flaw(), "Resolver {} does not resolve flaw {}", resolver.id(), flaw_id);
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id,
            intrinsic_cost: resolver.intrinsic_cost(),
            state: resolver.get_state(),
            data: resolver.to_json(),
        });
        self.resolvers.borrow_mut().push(resolver);
    }

    fn to_json(&self) -> Value {
        let mut slv = json!({
            "flaws": self.flaws.borrow().iter().map(|f| f.to_json()).collect::<Vec<_>>(),
            "resolvers": self.resolvers.borrow().iter().map(|r| r.to_json()).collect::<Vec<_>>(),
        });
        if let Some(current_flaw) = self.c_flaw.borrow().as_ref() {
            slv["current_flaw"] = json!(current_flaw.0);
        }
        if let Some(current_resolver) = self.c_res.borrow().as_ref() {
            slv["current_resolver"] = json!(current_resolver.0);
        }
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
                        _ => Err(RiddleError::TypeError("Expected int".to_string())),
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
                        _ => Err(RiddleError::TypeError("Expected real".to_string())),
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
                        _ => Err(RiddleError::TypeError("Expected int".to_string())),
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
                        _ => Err(RiddleError::TypeError("Expected real".to_string())),
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
                        Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), left_var.lit.to_real().div(right_var.lit.to_real())))))
                    } else if let Some(right_var) = right_var.clone().as_any().downcast_ref::<RealVar>() {
                        Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), left_var.lit.to_real().div(&right_var.lit)))))
                    } else {
                        Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                    }
                } else if let Some(left_var) = left_var.clone().as_any().downcast_ref::<RealVar>() {
                    if let Some(right_var) = right_var.clone().as_any().downcast_ref::<IntVar>() {
                        Ok(Slot::Primitive(Rc::new(RealVar::new(self.real_type(), left_var.lit.div(right_var.lit.to_real())))))
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
        let resolvers = self.resolvers.borrow();
        let rho = self.c_res.borrow().map(|res_id| resolvers[*res_id].rho());
        if let Some(rho) = rho {
            self.smt.assert(&rho.implies(expr_to_bool(&term)));
        } else {
            self.smt.assert(&expr_to_bool(&term));
        }
        true
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let var = Int::fresh_const("e");
        for id in instances {
            self.smt.assert(&var.eq(Int::from_u64(**id as u64)));
        }
        Ok(Slot::Primitive(Rc::new(EnumVar::new(tp, var))))
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        let resolvers = self.resolvers.borrow();
        let c_res = self.c_res.borrow().map_or(None, |res_id| resolvers.get(*res_id).map(|res| res.as_ref()));
        let rho = c_res.map_or(Bool::from_bool(true), |res| res.rho().clone());
        let cause = c_res.map(|res| res.id());
        let flaw_id = FlawId(self.flaws.borrow().len());
        self.add_flaw(DisjunctionFlaw::new(self.slv.clone(), flaw_id, rho, cause, disjunction));
        if let Some(res) = c_res {
            self.resolvers.borrow_mut().get_mut(*res.id()).expect("Invalid resolver ID").add_requirement(flaw_id);
        }
    }

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        self.core.new_object(class)
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        self.core.get_object(id)
    }
    fn new_atom(&self, predicate: Rc<Predicate>, fact: bool, args: HashMap<String, Slot>) -> AtomId {
        let atm = self.core.new_atom(predicate, fact, args);
        let resolvers = self.resolvers.borrow();
        let c_res = self.c_res.borrow().map_or(None, |res_id| resolvers.get(*res_id).map(|res| res.as_ref()));
        let rho = c_res.map_or(Bool::from_bool(true), |res| res.rho().clone());
        let cause = c_res.map(|res| res.id());
        let flaw_id = FlawId(self.flaws.borrow().len());
        self.atom_flaws.borrow_mut().push(flaw_id);
        let sigma = Bool::fresh_const("σ");
        self.add_flaw(AtomFlaw::new(self.slv.clone(), flaw_id, rho, cause, atm, sigma));
        if let Some(res) = c_res {
            self.resolvers.borrow_mut().get_mut(*res.id()).expect("Invalid resolver ID").add_requirement(flaw_id);
        }
        atm
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

fn expr_to_bool(expr: &BoolExpr) -> Bool {
    match expr {
        BoolExpr::Term { term, .. } => {
            if let Slot::Primitive(var) = term
                && let Some(var) = var.clone().as_any().downcast_ref::<BoolVar>()
            {
                return var.lit.clone();
            }
            panic!("Expected BoolVar in BoolExpr::Term");
        }
        BoolExpr::Eq { left, right, .. } => eq_to_bool(left, right),
        BoolExpr::Lt { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right) {
                if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<IntVar>(), right.clone().as_any().downcast_ref::<IntVar>()) {
                    return left.lit.lt(&right.lit);
                } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<RealVar>(), right.clone().as_any().downcast_ref::<RealVar>()) {
                    return left.lit.lt(&right.lit);
                } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<IntVar>(), right.clone().as_any().downcast_ref::<RealVar>()) {
                    return left.lit.to_real().lt(&right.lit);
                } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<RealVar>(), right.clone().as_any().downcast_ref::<IntVar>()) {
                    return left.lit.lt(right.lit.to_real());
                }
            }
            panic!("Expected compatible primitive types in BoolExpr::Lt");
        }
        BoolExpr::Leq { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right) {
                if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<IntVar>(), right.clone().as_any().downcast_ref::<IntVar>()) {
                    return left.lit.le(&right.lit);
                } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<RealVar>(), right.clone().as_any().downcast_ref::<RealVar>()) {
                    return left.lit.le(&right.lit);
                } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<IntVar>(), right.clone().as_any().downcast_ref::<RealVar>()) {
                    return left.lit.to_real().le(&right.lit);
                } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<RealVar>(), right.clone().as_any().downcast_ref::<IntVar>()) {
                    return left.lit.le(right.lit.to_real());
                }
            }
            panic!("Expected compatible primitive types in BoolExpr::Leq");
        }
        BoolExpr::Or { terms, .. } => Bool::or(&terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::And { terms, .. } => Bool::and(&terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::Not { term, .. } => expr_to_bool(term).not(),
    }
}

fn eq_to_bool(left: &Slot, right: &Slot) -> Bool {
    match (left, right) {
        (Slot::Primitive(left), Slot::Primitive(right)) => {
            if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<BoolVar>(), right.clone().as_any().downcast_ref::<BoolVar>()) {
                return left.lit.eq(&right.lit);
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<IntVar>(), right.clone().as_any().downcast_ref::<IntVar>()) {
                return left.lit.eq(&right.lit);
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<RealVar>(), right.clone().as_any().downcast_ref::<RealVar>()) {
                return left.lit.eq(&right.lit);
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<IntVar>(), right.clone().as_any().downcast_ref::<RealVar>()) {
                return left.lit.to_real().eq(&right.lit);
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<RealVar>(), right.clone().as_any().downcast_ref::<IntVar>()) {
                return left.lit.eq(right.lit.to_real());
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<StringVar>(), right.clone().as_any().downcast_ref::<StringVar>()) {
                return left.val.eq(&right.val);
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<EnumVar>(), right.clone().as_any().downcast_ref::<EnumVar>()) {
                return left.var.eq(&right.var);
            }
        }
        (Slot::Primitive(left), Slot::ObjectRef(right)) => {
            if let Some(left) = left.clone().as_any().downcast_ref::<EnumVar>() {
                return left.var.eq(Int::from_u64(**right as u64));
            }
        }
        (Slot::ObjectRef(left), Slot::Primitive(right)) => {
            if let Some(right) = right.clone().as_any().downcast_ref::<EnumVar>() {
                return Int::from_u64(**left as u64).eq(&right.var);
            }
        }
        _ => {
            panic!("Expected compatible types in equality");
        }
    }
    panic!("Expected compatible types in equality");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn new_state() -> Rc<SolverState> {
        let (tx_event, _) = broadcast::channel(100);
        SolverState::new(tx_event)
    }

    #[test]
    fn test_smt() {
        let slv = z3::Solver::new();
        let b0 = Bool::fresh_const("b0");
        let b1 = Bool::fresh_const("b1");
        let b2 = Bool::fresh_const("b2");
        let b3 = Bool::fresh_const("b3");
        let b4 = Bool::fresh_const("b4");
        slv.assert(&b0.implies(&Bool::or(&[&b1, &b2])));
        slv.assert(&b1.implies(&b3));
        slv.assert(&b2.implies(&b4));
        match slv.check_assumptions(&[b0.clone(), b1.clone()]) {
            z3::SatResult::Sat => {
                let model = slv.get_model().unwrap();
                println!("Model: {:?}", model);
                assert!(model.eval(&b0, true).unwrap().as_bool().unwrap());
                assert!(model.eval(&b1, true).unwrap().as_bool().unwrap());
                assert!(model.eval(&b3, true).unwrap().as_bool().unwrap());
            }
            _ => panic!("Expected SAT"),
        }
        match slv.check() {
            z3::SatResult::Sat => {
                let model = slv.get_model().unwrap();
                println!("Model: {:?}", model);
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_variables() {
        let state = new_state();
        let bool_var = state.new_bool_var();
        let int_var = state.new_int_var();
        let real_var = state.new_real_var();
        let string_var = state.new_string_var();

        assert!(matches!(bool_var, Slot::Primitive(_)));
        assert!(matches!(int_var, Slot::Primitive(_)));
        assert!(matches!(real_var, Slot::Primitive(_)));
        assert!(matches!(string_var, Slot::Primitive(_)));
    }
}
