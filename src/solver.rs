use crate::{
    ToJson,
    flaws::{ClauseFlaw, EnumFlaw},
    graph::Graph,
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
};
use consensus::{FALSE_LIT, Lit, TRUE_LIT, neg, pos};
use linspire::{
    lin::{Lin, c, v},
    rational::rat,
};
use riddle::{
    core::{CommonCore, Core},
    env::{Atom, BoolExpr, Env, Var},
    language::{Disjunction, RiddleError},
    scope::{Field, Method, Predicate, Scope, Type, arith_class},
    serde_json::Value,
};
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::trace;

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    pub sat: RefCell<consensus::Engine>,
    pub ac: RefCell<dynamic_ac::Engine>,
    pub lin: RefCell<linspire::Engine>,
    pub graph: RefCell<Graph>,
    variants: RefCell<HashMap<usize, usize>>,
    instances_by_id: RefCell<Vec<Rc<dyn Var>>>,
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
            sat: RefCell::new(consensus::Engine::new()),
            ac: RefCell::new(dynamic_ac::Engine::new()),
            lin: RefCell::new(linspire::Engine::new()),
            graph: RefCell::new(Graph::new(core.clone(), tx_event.clone())),
            variants: RefCell::new(HashMap::new()),
            instances_by_id: RefCell::new(vec![]),
            tx_event,
        })
    }

    fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    fn solve(&self) -> bool {
        trace!("Solving problem...");
        if !self.graph.borrow_mut().build_graph() {
            trace!("Problem is inconsistent");
            return false;
        }

        while let Some(flaw) = self.graph.borrow().get_most_expensive_flaw() {
            trace!("Best flaw to resolve: {:?}", flaw.id());
            self.graph.borrow_mut().set_current_flaw(Some(flaw.clone()));
            if let Some(resolver) = self.graph.borrow().get_least_expensive_resolver(flaw.as_ref()) {
                trace!("Best resolver to apply: {:?}", resolver.id());
                self.graph.borrow_mut().set_current_resolver(Some(resolver.clone()));
                self.graph.borrow_mut().set_current_resolver(None);
            } else {
                trace!("No applicable resolver found for flaw {:?}. Problem is inconsistent.", flaw.id());
                return false;
            }
            self.graph.borrow_mut().set_current_flaw(None);
        }
        true
    }
}

impl ToJson for SolverState {
    fn to_json(&self) -> Value {
        self.graph.borrow().to_json()
    }
}

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
    NewFlaw(Value),
    FlawCostUpdate(Value),
    FlawStatusUpdate(Value),
    CurrentFlaw(Value),
    NewResolver(Value),
    ResolverStatusUpdate(Value),
    CurrentResolver(Value),
}

#[derive(Clone)]
pub struct Solver {
    tx_cmd: mpsc::Sender<SolverCommand>,
    pub tx_event: broadcast::Sender<SolverEvent>,
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
                        true => {
                            let _ = responder.send(Ok(()));
                        }
                        false => {
                            let _ = responder.send(Err(SolverError::Inconsistent));
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

impl Scope for SolverState {
    fn core(self: Rc<Self>) -> Rc<dyn Core> {
        self
    }
    fn scope(&self) -> Option<Rc<dyn Scope>> {
        None
    }

    fn get_field(&self, name: &str) -> Option<Rc<Field>> {
        self.core.get_field(name)
    }
    fn get_method(&self, name: &str, types: &[Rc<dyn Type>]) -> Option<Rc<Method>> {
        self.core.get_method(name, types)
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
    fn get(&self, name: &str) -> Option<Rc<dyn Var>> {
        self.core.get(name)
    }
    fn set(&self, name: String, value: Rc<dyn Var>) {
        self.core.set(name, value)
    }
}

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Rc<dyn Var> {
        Rc::new(BoolVar::new(self.bool_type(), if value { TRUE_LIT } else { FALSE_LIT }))
    }
    fn new_bool_var(&self) -> Rc<dyn Var> {
        Rc::new(BoolVar::new(self.bool_type(), pos(self.sat.borrow_mut().add_var())))
    }
    fn new_int(&self, value: i64) -> Rc<dyn Var> {
        Rc::new(ArithVar::new(self.int_type(), c(value)))
    }
    fn new_int_var(&self) -> Rc<dyn Var> {
        Rc::new(ArithVar::new(self.int_type(), v(self.lin.borrow_mut().add_var())))
    }
    fn new_real(&self, num: i64, den: i64) -> Rc<dyn Var> {
        Rc::new(ArithVar::new(self.real_type(), Lin::new_const(rat(num, den))))
    }
    fn new_real_var(&self) -> Rc<dyn Var> {
        Rc::new(ArithVar::new(self.real_type(), v(self.lin.borrow_mut().add_var())))
    }
    fn new_string(&self, value: &str) -> Rc<dyn Var> {
        Rc::new(StringVar::new(self.string_type(), value.to_string()))
    }
    fn new_string_var(&self) -> Rc<dyn Var> {
        Rc::new(StringVar::new(self.string_type(), String::new()))
    }

    fn sum(&self, sum: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        let mut result = c(0);
        for var in sum {
            if let Some(int_var) = var.clone().as_any().downcast_ref::<ArithVar>() {
                result += &int_var.lin
            } else if let Some(real_var) = var.clone().as_any().downcast_ref::<ArithVar>() {
                result += &real_var.lin
            } else {
                panic!("Expected int or ArithVar");
            };
        }
        let tp = arith_class(self, sum)?;
        if tp.name() == "int" { Ok(Rc::new(ArithVar::new(self.int_type(), result))) } else { Ok(Rc::new(ArithVar::new(self.real_type(), result))) }
    }
    fn opposite(&self, term: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        if let Some(arith_var) = term.clone().as_any().downcast_ref::<ArithVar>() {
            Ok(Rc::new(ArithVar::new(arith_var.var_type(), -arith_var.lin.clone())))
        } else {
            panic!("Expected int or real");
        }
    }
    fn mul(&self, mul: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        let mut result = c(1);
        for var in mul {
            if let Some(int_var) = var.clone().as_any().downcast_ref::<ArithVar>() {
                if result.vars.is_empty() {
                    result = &int_var.lin * result.known_term;
                } else if int_var.lin.vars.is_empty() {
                    result = &result * int_var.lin.known_term;
                } else {
                    return Err(RiddleError::RuntimeError("Non-linear multiplication is not supported".to_string()));
                }
            } else if let Some(real_var) = var.clone().as_any().downcast_ref::<ArithVar>() {
                if result.vars.is_empty() {
                    result = &real_var.lin * result.known_term;
                } else if real_var.lin.vars.is_empty() {
                    result = &result * real_var.lin.known_term;
                } else {
                    return Err(RiddleError::RuntimeError("Non-linear multiplication is not supported".to_string()));
                }
            } else {
                panic!("Expected int or real");
            };
        }
        if arith_class(self, mul)?.name() == "int" { Ok(Rc::new(ArithVar::new(self.int_type(), result))) } else { Ok(Rc::new(ArithVar::new(self.real_type(), result))) }
    }
    fn div(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        if let Some(int_var) = right.clone().as_any().downcast_ref::<ArithVar>() {
            if int_var.lin.vars.is_empty() {
                if let Some(int_var_left) = left.clone().as_any().downcast_ref::<ArithVar>() {
                    Ok(Rc::new(ArithVar::new(self.int_type(), int_var_left.lin.clone() / int_var.lin.known_term)))
                } else if let Some(real_var_left) = left.clone().as_any().downcast_ref::<ArithVar>() {
                    Ok(Rc::new(ArithVar::new(self.real_type(), real_var_left.lin.clone() / int_var.lin.known_term)))
                } else {
                    Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                }
            } else {
                Err(RiddleError::RuntimeError("Non-linear division is not supported".to_string()))
            }
        } else if let Some(real_var) = right.clone().as_any().downcast_ref::<ArithVar>() {
            if real_var.lin.vars.is_empty() {
                if let Some(int_var_left) = left.clone().as_any().downcast_ref::<ArithVar>() {
                    Ok(Rc::new(ArithVar::new(self.int_type(), int_var_left.lin.clone() / real_var.lin.known_term)))
                } else if let Some(real_var_left) = left.clone().as_any().downcast_ref::<ArithVar>() {
                    Ok(Rc::new(ArithVar::new(self.real_type(), real_var_left.lin.clone() / real_var.lin.known_term)))
                } else {
                    Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                }
            } else {
                Err(RiddleError::RuntimeError("Non-linear division is not supported".to_string()))
            }
        } else {
            Err(RiddleError::RuntimeError("Expected int or real".to_string()))
        }
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        let c_res = self.graph.borrow().get_current_resolver();
        match term.as_ref() {
            BoolExpr::Term { term, .. } => {
                let lit = bool_lit(term);
                if let Some(res) = c_res {
                    return self.sat.borrow_mut().add_clause(vec![neg(res.rho()), lit]);
                } else {
                    return self.sat.borrow_mut().add_clause(vec![lit]);
                }
            }
            BoolExpr::Eq { left, right, .. } => {
                let rho = if c_res.is_some() { c_res.as_ref().unwrap().rho() } else { 0 };
                if let Some(left_var) = left.clone().as_any().downcast_ref::<BoolVar>() {
                    if let Some(right_var) = right.clone().as_any().downcast_ref::<BoolVar>() {
                        let left_lit = left_var.lit;
                        let right_lit = right_var.lit;
                        if c_res.is_some() {
                            return self.sat.borrow_mut().add_clause(vec![neg(rho), left_lit, !right_lit]) && self.sat.borrow_mut().add_clause(vec![neg(rho), !left_lit, right_lit]);
                        } else {
                            return self.sat.borrow_mut().add_clause(vec![left_lit, !right_lit]) && self.sat.borrow_mut().add_clause(vec![!left_lit, right_lit]);
                        }
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                    }
                } else if let Some(left_var) = left.clone().as_any().downcast_ref::<ArithVar>() {
                    if let Some(right_var) = right.clone().as_any().downcast_ref::<ArithVar>() {
                        let left_lin = &left_var.lin;
                        let right_lin = &right_var.lin;
                        let lin_cnstr = if c_res.is_some() { c_res.unwrap().lin_constraints() } else { None };
                        return self.lin.borrow_mut().new_eq(left_lin, right_lin, lin_cnstr);
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                    }
                } else if let Some(left_var) = left.clone().as_any().downcast_ref::<StringVar>() {
                    if let Some(right_var) = right.clone().as_any().downcast_ref::<StringVar>() {
                        if c_res.is_some() {
                            return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                        } else {
                            left_var.value == right_var.value
                        }
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                    }
                } else if let Some(left_var) = left.clone().as_any().downcast_ref::<EnumVar>() {
                    if let Some(right_var) = right.clone().as_any().downcast_ref::<EnumVar>() {
                        match self.ac.borrow_mut().new_eq(left_var.var, right_var.var) {
                            Ok(c) => {
                                if let Some(res) = c_res.as_ref() {
                                    res.add_ac_constraint(c);
                                }
                                return true;
                            }
                            Err(_) => return self.sat.borrow_mut().add_clause(vec![neg(rho)]),
                        }
                    } else if let Some(val) = self.variants.borrow().get(&(Rc::as_ptr(right) as *const () as usize)) {
                        match self.ac.borrow_mut().set(left_var.var, *val as i32) {
                            Ok(c) => {
                                if let Some(res) = c_res.as_ref() {
                                    res.add_ac_constraint(c);
                                }
                                return true;
                            }
                            Err(_) => return self.sat.borrow_mut().add_clause(vec![neg(rho)]),
                        }
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                    }
                } else if let Some(val) = self.variants.borrow().get(&(Rc::as_ptr(right) as *const () as usize)) {
                    if let Some(right_var) = right.clone().as_any().downcast_ref::<EnumVar>() {
                        match self.ac.borrow_mut().set(right_var.var, *val as i32) {
                            Ok(c) => {
                                if let Some(res) = c_res.as_ref() {
                                    res.add_ac_constraint(c);
                                }
                                return true;
                            }
                            Err(_) => return self.sat.borrow_mut().add_clause(vec![neg(rho)]),
                        }
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                    }
                } else {
                    return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                }
            }
            BoolExpr::Lt { left, right, .. } => {
                let left_lin = numeric_lin(left);
                let right_lin = numeric_lin(right);
                let lin_cnstr = if c_res.is_some() { c_res.unwrap().lin_constraints() } else { None };
                return self.lin.borrow_mut().new_lt(&left_lin, &right_lin, true, lin_cnstr);
            }
            BoolExpr::Leq { left, right, .. } => {
                let left_lin = numeric_lin(left);
                let right_lin = numeric_lin(right);
                let lin_cnstr = if c_res.is_some() { c_res.unwrap().lin_constraints() } else { None };
                return self.lin.borrow_mut().new_le(&left_lin, &right_lin, lin_cnstr);
            }
            BoolExpr::Or { terms, .. } => {
                let lits = terms
                    .iter()
                    .map(|term| match term.as_ref() {
                        BoolExpr::Term { term, .. } => term.clone().as_any().downcast::<BoolVar>().expect("Expected BoolVar").lit,
                        _ => panic!("Expected BoolExpr::Term"),
                    })
                    .collect();
                let rho = c_res.as_ref().map(|res| res.rho()).unwrap_or(0);
                let cause = c_res.as_ref().map(|res| Some(res.id())).unwrap_or(None);
                self.graph.borrow_mut().add_flaw(ClauseFlaw::new(self.slv.clone(), self.graph.borrow().get_num_flaws(), rho, cause, lits));
                true
            }
            BoolExpr::And { terms, .. } => {
                for term in terms {
                    if !self.assert(term.clone()) {
                        return false;
                    }
                }
                true
            }
            BoolExpr::Not { term, .. } => match term.as_ref() {
                BoolExpr::Term { term, .. } => {
                    let lit = bool_lit(term);
                    if let Some(res) = &c_res {
                        return self.sat.borrow_mut().add_clause(vec![neg(res.as_ref().rho()), !lit]);
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![!lit]);
                    }
                }
                BoolExpr::Eq { left, right, .. } => {
                    let rho = if c_res.is_some() { c_res.as_ref().unwrap().rho() } else { 0 };
                    if let Some(left_bool_var) = left.clone().as_any().downcast_ref::<BoolVar>() {
                        if let Some(right_bool_var) = right.clone().as_any().downcast_ref::<BoolVar>() {
                            let left_lit = left_bool_var.lit;
                            let right_lit = right_bool_var.lit;
                            if c_res.is_some() {
                                return self.sat.borrow_mut().add_clause(vec![neg(rho), !left_lit, !right_lit]) && self.sat.borrow_mut().add_clause(vec![neg(rho), !left_lit, !right_lit]);
                            } else {
                                return self.sat.borrow_mut().add_clause(vec![!left_lit, !right_lit]) && self.sat.borrow_mut().add_clause(vec![!left_lit, !right_lit]);
                            }
                        }
                    } else if left.clone().as_any().downcast_ref::<ArithVar>().is_some() && right.clone().as_any().downcast_ref::<ArithVar>().is_some() {
                        return self.assert(Rc::new(BoolExpr::Or {
                            var_type: Rc::downgrade(&self.bool_type()),
                            terms: vec![Rc::new(BoolExpr::Lt { var_type: Rc::downgrade(&self.bool_type()), left: left.clone(), right: right.clone() }), Rc::new(BoolExpr::Lt { var_type: Rc::downgrade(&self.bool_type()), left: right.clone(), right: left.clone() })],
                        }));
                    } else if let Some(left_string_var) = left.clone().as_any().downcast_ref::<StringVar>()
                        && let Some(right_string_var) = right.clone().as_any().downcast_ref::<StringVar>()
                    {
                        if c_res.is_some() && left_string_var.value == right_string_var.value {
                            return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                        } else {
                            return left_string_var.value != right_string_var.value;
                        }
                    } else if let Some(left_var) = left.clone().as_any().downcast_ref::<EnumVar>() {
                        if let Some(right_var) = right.clone().as_any().downcast_ref::<EnumVar>() {
                            match self.ac.borrow_mut().new_neq(left_var.var, right_var.var) {
                                Ok(c) => {
                                    if let Some(res) = &c_res {
                                        res.add_ac_constraint(c);
                                    }
                                    return true;
                                }
                                Err(_) => return self.sat.borrow_mut().add_clause(vec![neg(rho)]),
                            }
                        } else if let Some(val) = self.variants.borrow().get(&(Rc::as_ptr(right) as *const () as usize)) {
                            match self.ac.borrow_mut().forbid(left_var.var, *val as i32) {
                                Ok(c) => {
                                    if let Some(res) = &c_res {
                                        res.add_ac_constraint(c);
                                    }
                                    return true;
                                }
                                Err(_) => return self.sat.borrow_mut().add_clause(vec![neg(rho)]),
                            }
                        }
                    } else if let Some(val) = self.variants.borrow().get(&(Rc::as_ptr(left) as *const () as usize)) {
                        if let Some(right_var) = right.clone().as_any().downcast_ref::<EnumVar>() {
                            match self.ac.borrow_mut().forbid(right_var.var, *val as i32) {
                                Ok(c) => {
                                    if let Some(res) = &c_res {
                                        res.add_ac_constraint(c);
                                    }
                                    return true;
                                }
                                Err(_) => return self.sat.borrow_mut().add_clause(vec![neg(rho)]),
                            }
                        }
                    }
                    true
                }
                BoolExpr::Lt { left, right, .. } => {
                    let left_lin = numeric_lin(left);
                    let right_lin = numeric_lin(right);
                    let lin_cnstr = if c_res.is_some() { c_res.unwrap().lin_constraints() } else { None };
                    return self.lin.borrow_mut().new_ge(&left_lin, &right_lin, lin_cnstr);
                }
                BoolExpr::Leq { left, right, .. } => {
                    let left_lin = numeric_lin(left);
                    let right_lin = numeric_lin(right);
                    let lin_cnstr = if c_res.is_some() { c_res.unwrap().lin_constraints() } else { None };
                    return self.lin.borrow_mut().new_gt(&left_lin, &right_lin, true, lin_cnstr);
                }
                _ => panic!("Expected BoolExpr::Term, BoolExpr::Eq, BoolExpr::Lt, or BoolExpr::Leq"),
            },
        }
    }
    fn new_var(&self, class: Rc<dyn Type>, instances: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        let mut vals = Vec::new();
        let mut variants = self.variants.borrow_mut();
        let mut instances_by_id = self.instances_by_id.borrow_mut();
        let mut current_len = variants.len();
        for instance in instances {
            let val = variants.entry(Rc::as_ptr(instance) as *const () as usize).or_insert_with(|| {
                let id = current_len;
                current_len += 1; // Increment for the next new entry
                instances_by_id.push(instance.clone());
                id
            });
            vals.push(*val as i32);
        }
        let var = self.ac.borrow_mut().add_var(vals);
        let var = Rc::new(EnumVar::new(class, var));
        let c_res = self.graph.borrow().get_current_resolver();
        let rho = c_res.as_ref().map(|res| res.rho()).unwrap_or(0);
        let cause = c_res.as_ref().map(|res| Some(res.id())).unwrap_or(None);
        self.graph.borrow_mut().add_flaw(EnumFlaw::new(self.slv.clone(), self.graph.borrow().get_num_flaws(), rho, cause, var.clone()));
        Ok(var)
    }
    fn new_disjunction(&self, _disjunction: Disjunction) {
        unimplemented!()
    }
    fn new_atom(&self, _atom: Rc<Atom>) {
        unimplemented!()
    }
}

impl fmt::Debug for SolverState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Solver").field("core", &"CommonCore").finish()
    }
}

fn bool_lit(var: &Rc<dyn Var>) -> Lit {
    var.clone().as_any().downcast_ref::<BoolVar>().expect("Expected BoolVar").lit
}

fn numeric_lin(var: &Rc<dyn Var>) -> Lin {
    var.clone().as_any().downcast_ref::<ArithVar>().expect("Expected ArithVar").lin.clone()
}
