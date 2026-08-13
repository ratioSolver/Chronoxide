mod flaws;
mod graph;
mod objects;

use crate::{
    flaws::{bool_flw::BoolFlaw, clause_flw::ClauseFlaw, enum_flw::EnumFlaw},
    graph::{Flaw, FlawId, Graph, ResolverId},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, to_cnf},
    language::Disjunction,
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use semitone::{
    SmtSolver,
    ast::{self, Expr},
};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::{Rc, Weak},
    str::FromStr,
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    smt: RefCell<SmtSolver>,
    planner_state: RefCell<PlannerState>,
    tx_event: broadcast::Sender<SolverEvent>,
}

struct PlannerState {
    graph: Graph,
    agenda: HashSet<FlawId>,
    notified_len: usize,
    lit_to_flaw: HashMap<usize, FlawId>,
    lit_to_resolver: HashMap<usize, ResolverId>,
}

impl SolverState {
    fn new(tx_event: broadcast::Sender<SolverEvent>) -> Rc<Self> {
        Rc::new_cyclic(|core| SolverState {
            core: {
                let core: Weak<SolverState> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            smt: RefCell::new(SmtSolver::new()),
            planner_state: RefCell::new(PlannerState {
                graph: Graph::new(),
                agenda: HashSet::new(),
                notified_len: 0,
                lit_to_flaw: HashMap::new(),
                lit_to_resolver: HashMap::new(),
            }),
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

    pub fn add_flaw(&self, flaw: Box<dyn Flaw>) {
        trace!("Adding flaw: {} ({})", flaw.id(), flaw.phi());
        self.planner_state.borrow_mut().graph.add_flaw(flaw);
    }

    fn sync_agenda(&self) {
        let mut planner = self.planner_state.borrow_mut();
        let smt = self.smt.borrow();

        let current_trail_len = smt.current_trail_len();
        if planner.notified_len == current_trail_len {
            return;
        }

        let new_literals = smt.get_trail_delta(planner.notified_len);

        for lit in new_literals {
            let var_id = lit.var();

            if let Some(&flaw_id) = planner.lit_to_flaw.get(&var_id) {
                if !lit.sign() {
                    planner.agenda.insert(flaw_id);
                }
            } else if let Some(&resolver_id) = planner.lit_to_resolver.get(&var_id)
                && !lit.sign()
            {
                let parent_flaw_id = planner.graph.get_resolver(resolver_id).flaw();
                planner.agenda.remove(&parent_flaw_id);
            }
        }

        planner.notified_len = current_trail_len;
    }

    fn cancel_until(&self, level: usize) {
        let mut planner = self.planner_state.borrow_mut();
        let smt = self.smt.borrow();

        let target_trail_len = smt.get_trail_len_at_level(level);
        let current_trail_len = smt.current_trail_len();

        let trail_to_undo = smt.get_trail_slice(target_trail_len, current_trail_len);

        for lit in trail_to_undo.iter().rev() {
            let var_id = lit.var();

            if let Some(&flaw_id) = planner.lit_to_flaw.get(&var_id) {
                if !lit.sign() {
                    planner.agenda.remove(&flaw_id);
                }
            } else if let Some(&resolver_id) = planner.lit_to_resolver.get(&var_id)
                && !lit.sign()
            {
                let parent_flaw_id = planner.graph.get_resolver(resolver_id).flaw();
                planner.agenda.insert(parent_flaw_id);
            }
        }

        planner.notified_len = target_trail_len;

        drop(smt);
        self.smt.borrow_mut().cancel_until(level);
    }

    fn build_graph(&self) -> Result<(), SolverError> {
        info!("Building graph...");
        self.sync_agenda();
        while self.planner_state.borrow().agenda.iter().any(|&flaw_id| self.planner_state.borrow().graph.get_flaw(flaw_id).estimated_cost() == f64::INFINITY) {
            if let Some(flaw_id) = self.planner_state.borrow_mut().graph.flaw_q.pop_front() {
                let mut flaw = {
                    let mut planner = self.planner_state.borrow_mut();
                    planner.graph.set_current_flaw(Some(flaw_id));
                    planner.graph.take_flaw(flaw_id)
                };
                assert!(!flaw.is_expanded());
                let mut or_args = Vec::with_capacity(flaw.causes().len() + 1);
                for cause_id in flaw.causes() {
                    or_args.push(!self.planner_state.borrow().graph.get_resolver(*cause_id).rho().clone());
                }
                or_args.push(flaw.phi().clone());
                self.smt.borrow_mut().assert(&ast::or(or_args)).expect("Failed to assert flaw phi in SMT solver");

                let resolvers = flaw.expand(self)?;
                let mut or_args = Vec::with_capacity(resolvers.len() + 1);
                for resolver in &resolvers {
                    let rho = resolver.rho().clone();
                    or_args.push(rho.clone());
                    self.smt.borrow_mut().assert(&ast::or([!rho, flaw.phi().clone()])).expect("Failed to assert resolver rho in SMT solver");
                }
                or_args.push(!flaw.phi().clone());
                self.smt.borrow_mut().assert(&ast::or(or_args)).expect("Failed to assert flaw phi in SMT solver after expansion");

                for resolver in resolvers {
                    let mut resolver = {
                        let mut planner = self.planner_state.borrow_mut();
                        let res_id = planner.graph.add_resolver(resolver);
                        flaw.add_resolver(res_id);
                        planner.graph.set_current_resolver(Some(res_id));
                        planner.graph.take_resolver(res_id)
                    };
                    resolver.apply(self)?;
                    {
                        let mut planner = self.planner_state.borrow_mut();
                        planner.graph.return_resolver(resolver.id(), resolver);
                        planner.graph.set_current_resolver(None);
                    }
                }
                {
                    let mut planner = self.planner_state.borrow_mut();
                    planner.graph.return_flaw(flaw_id, flaw);
                    planner.graph.set_current_flaw(None);
                }
                self.planner_state.borrow_mut().graph.propagate_costs(vec![flaw_id], |expr| self.smt.borrow().get_bool_val(expr) != Some(false));
            } else {
                return Err(SolverError::Inconsistent);
            }
        }
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({"flaws": [], "resolvers": []})
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
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), if value { ast::BoolExpr::True } else { ast::BoolExpr::False })))
    }
    fn new_bool_var(&self) -> Slot {
        let var = self.smt.borrow_mut().new_bool();
        let (phi, c_res) = if let Some(c_res) = self.planner_state.borrow().graph.get_current_resolver() { (c_res.rho().clone(), Some(c_res.id())) } else { (ast::BoolExpr::True, None) };
        self.add_flaw(Box::new(BoolFlaw::new(phi, c_res, var.clone())));
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), var)))
    }
    fn new_int(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), ast::ArithExpr::Const(rug::Rational::from_str(value).expect("Invalid integer literal")))))
    }
    fn new_int_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), self.smt.borrow_mut().new_int())))
    }
    fn new_real(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), ast::ArithExpr::Const(rug::Rational::from_str(value).expect("Invalid real literal")))))
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

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        let (phi, c_res_id) = if let Some(c_res) = self.planner_state.borrow().graph.get_current_resolver() { (c_res.rho().clone(), Some(c_res.id())) } else { (ast::BoolExpr::True, None) };
        if self.smt.borrow_mut().assert(&ast::or([!phi.clone(), expr_to_bool(&term)])).is_err() {
            return false;
        }
        let cnf_expr = to_cnf(term.clone());
        if let BoolExpr::And { terms, .. } = cnf_expr.as_ref() {
            for clause in terms {
                if let BoolExpr::Or { terms, .. } = clause.as_ref()
                    && terms.len() > 1
                {
                    let terms = terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>();
                    self.add_flaw(Box::new(ClauseFlaw::new(phi.clone(), c_res_id, terms)));
                }
            }
        } else {
            if let BoolExpr::Or { terms, .. } = cnf_expr.as_ref()
                && terms.len() > 1
            {
                let terms = terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>();
                self.add_flaw(Box::new(ClauseFlaw::new(phi.clone(), c_res_id, terms)));
            }
        }
        true
    }
    fn new_var(&self, tp: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let domain = instances.iter().map(|id| **id as i32).collect::<Vec<_>>();
        let var = self.smt.borrow_mut().new_enum(domain.clone());
        let (phi, c_res) = if let Some(c_res) = self.planner_state.borrow().graph.get_current_resolver() { (c_res.rho().clone(), Some(c_res.id())) } else { (ast::BoolExpr::True, None) };
        self.add_flaw(Box::new(EnumFlaw::new(phi, c_res, var.clone(), domain)));
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
        self.core.new_atom(predicate, fact, args)
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

fn expr_to_bool(expr: &BoolExpr) -> ast::BoolExpr {
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
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<ArithVar>(), right.clone().as_any().downcast_ref::<ArithVar>())
            {
                return ast::lt(left.lin.clone(), right.lin.clone());
            }
            panic!("Expected compatible primitive types in BoolExpr::Lt");
        }
        BoolExpr::Leq { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<ArithVar>(), right.clone().as_any().downcast_ref::<ArithVar>())
            {
                return ast::le(left.lin.clone(), right.lin.clone());
            }
            panic!("Expected compatible primitive types in BoolExpr::Leq");
        }
        BoolExpr::Or { terms, .. } => ast::or(terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::And { terms, .. } => ast::and(terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::Not { term, .. } => !expr_to_bool(term),
    }
}

fn eq_to_bool(left: &Slot, right: &Slot) -> ast::BoolExpr {
    match (left, right) {
        (Slot::Primitive(left), Slot::Primitive(right)) => {
            if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<BoolVar>(), right.clone().as_any().downcast_ref::<BoolVar>()) {
                return ast::eq(Expr::Bool(left.lit.clone()), Expr::Bool(right.lit.clone()));
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<ArithVar>(), right.clone().as_any().downcast_ref::<ArithVar>()) {
                return ast::eq(Expr::Arith(left.lin.clone()), Expr::Arith(right.lin.clone()));
            } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<EnumVar>(), right.clone().as_any().downcast_ref::<EnumVar>()) {
                return ast::eq(Expr::Enum(left.var.clone()), Expr::Enum(right.var.clone()));
            }
        }
        (Slot::Primitive(left), Slot::ObjectRef(right)) => {
            if let Some(left) = left.clone().as_any().downcast_ref::<EnumVar>() {
                return ast::eq(Expr::Enum(left.var.clone()), Expr::Enum(ast::EnumExpr::Const(**right as i32)));
            }
        }
        (Slot::ObjectRef(left), Slot::Primitive(right)) => {
            if let Some(right) = right.clone().as_any().downcast_ref::<EnumVar>() {
                return ast::eq(Expr::Enum(ast::EnumExpr::Const(**left as i32)), Expr::Enum(right.var.clone()));
            }
        }
        _ => {
            panic!("Expected compatible types in equality");
        }
    }
    panic!("Expected compatible types in equality");
}

#[derive(Clone)]
pub enum SolverEvent {
    NewFlaw { flaw_id: FlawId, phi: usize, causes: Vec<ResolverId>, supports: Vec<ResolverId>, status: Option<bool>, cost: f64, data: Value },
    FlawCostUpdate { flaw_id: FlawId, cost: f64 },
    FlawStatusUpdate { flaw_id: FlawId, status: Option<bool> },
    CurrentFlaw(Option<FlawId>),
    NewResolver { resolver_id: ResolverId, rho: usize, flaw_id: FlawId, sub_flaws: Vec<FlawId>, intrinsic_cost: f64, status: Option<bool>, data: Value },
    ResolverStatusUpdate { resolver_id: ResolverId, status: Option<bool> },
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
