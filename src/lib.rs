use crate::{
    flaws::{Flaw, FlawId, Resolver, ResolverId},
    graph::Graph,
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    delegate_env, delegate_scope,
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, Var},
    language::{AtomKind, Disjunction, ResolutionConstraint},
    scope::{Class, Field, Function, Predicate, Scope, Type},
};
use semitone::{
    Lit, SeMiTONE, ast,
    rational::{InfRational, Rational},
};
use serde_json::{Value, json};
use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    rc::{Rc, Weak},
};
use tokio::sync::{broadcast, mpsc, oneshot};
use tracing::{info, trace};

mod flaws;
mod graph;
mod objects;

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    smt: RefCell<SeMiTONE>,
    notified_len: Cell<usize>,
    graph: RefCell<Graph>,
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
            notified_len: Cell::new(0),
            graph: RefCell::new(Graph::new(tx_event.clone())),
            tx_event,
        });
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
                Ok(_) => {}
                Err((bt_level, lemma)) => {
                    let mut smt = self.smt.borrow_mut();
                    let mut graph = self.graph.borrow_mut();
                    if !self.backtrack_and_learn(&mut smt, &mut graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
        Ok(())
    }

    pub fn add_flaw(&self, smt: &mut SeMiTONE, graph: &mut Graph, causes: Vec<ResolverId>, flw: Box<dyn Flaw>) -> Result<FlawId, SolverError> {
        let mut cause_lits: Vec<Lit> = graph.resolver_rhos(&causes);
        cause_lits.sort_unstable();
        cause_lits.dedup();

        unimplemented!()
    }

    pub fn add_resolver(&self, smt: &mut SeMiTONE, graph: &mut Graph, rho: Lit, res: Box<dyn Resolver>) -> Result<ResolverId, SolverError> {
        unimplemented!()
    }

    fn track_expr(&self, smt: &mut SeMiTONE, graph: &mut Graph, expr: ast::BoolExpr) -> Result<Lit, SolverError> {
        loop {
            match smt.track_expr(expr.as_ref()) {
                Ok(lit) => {
                    return Ok(lit);
                }
                Err((bt_level, lemma)) => {
                    if !self.backtrack_and_learn(smt, graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    fn add_clause(&self, smt: &mut SeMiTONE, graph: &mut Graph, clause: impl IntoIterator<Item = Lit>) -> Result<(), SolverError> {
        let clause: Vec<Lit> = clause.into_iter().collect();
        loop {
            match smt.add_clause(clause.clone()) {
                Ok(()) => {
                    return Ok(());
                }
                Err((bt_level, lemma)) => {
                    if !self.backtrack_and_learn(smt, graph, bt_level, lemma) {
                        return Err(SolverError::Inconsistent);
                    }
                }
            }
        }
    }

    fn backtrack_and_learn(&self, smt: &mut SeMiTONE, graph: &mut Graph, bt_level: usize, lemma: Vec<Lit>) -> bool {
        if smt.decision_level() == 0 {
            return false;
        }
        let vars_to_undo = smt.cancel_until(bt_level);
        self.notified_len.set(smt.current_trail_len());
        smt.add_clause(lemma).is_ok()
    }

    fn to_json(&self) -> Value {
        let smt = self.smt.borrow();
        let env = to_json(&smt, self);
        let mut objects_map = serde_json::Map::new();
        for object in &self.core.get_objects() {
            let mut obj = json!({
                "class": object.class().full_name(),
                "env": to_json(&smt, object.as_ref()),
            });
            if let Some(name) = self.core.get_object_name(object.id()) {
                obj["name"] = json!(name);
            }
            objects_map.insert(object.id().to_string(), obj);
        }
        let mut atoms_map = serde_json::Map::new();
        for atom in &self.core.get_atoms() {
            atoms_map.insert(
                atom.id().to_string(),
                json!({
                    "predicate": atom.predicate().full_name(),
                    "fact": match atom.kind() {
                        AtomKind::Fact => true,
                        AtomKind::Goal => false,
                    },
                    "env": to_json(&smt, atom.as_ref()),
                }),
            );
        }

        drop(smt);

        json!({
            "env": env,
            "objects": Value::Object(objects_map),
            "atoms": Value::Object(atoms_map),
            "flaws": Vec::<Value>::new(),
            "resolvers": Vec::<Value>::new(),
        })
    }
}

delegate_scope!(SolverState, core);
delegate_env!(SolverState, core);

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Slot {
        unimplemented!()
    }
    fn new_bool_var(&self) -> Slot {
        unimplemented!()
    }
    fn new_int(&self, value: &str) -> Slot {
        unimplemented!()
    }
    fn new_int_var(&self) -> Slot {
        unimplemented!()
    }
    fn new_real(&self, num: &str, den: &str) -> Slot {
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
    fn new_atom(&self, predicate: Rc<Predicate>, kind: AtomKind, args: HashMap<String, Slot>, resolution_constraint: ResolutionConstraint) -> Result<AtomId, RiddleError> {
        unimplemented!()
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        unimplemented!()
    }
}

#[derive(Debug)]
pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

#[derive(Clone)]
pub enum SolverEvent {
    NewObject { obj_id: ObjectId, name: Option<String>, class: String },
    NewAtom { atom_id: AtomId, predicate: String, kind: AtomKind, args: Value, resolution_constraint: ResolutionConstraint },
    NewFlaw { flaw_id: FlawId, phi: String, causes: Vec<ResolverId>, required_by: Vec<ResolverId>, status: Option<bool>, cost: f64, data: Value },
    FlawCostUpdate { flaw_id: FlawId, cost: f64 },
    FlawStatusUpdate { flaw_id: FlawId, status: Option<bool> },
    CurrentFlaw(Option<FlawId>),
    NewResolver { resolver_id: ResolverId, rho: String, flaw_id: FlawId, preconditions: Vec<FlawId>, intrinsic_cost: f64, status: Option<bool>, data: Value },
    ResolverStatusUpdate { resolver_id: ResolverId, status: Option<bool> },
    CurrentResolver(Option<ResolverId>),
    NewCausalLink { flaw_id: FlawId, resolver_id: ResolverId },
    ToSolveFlaw { flaw_id: FlawId },
    SolvedFlaw { flaw_id: FlawId },
    StateUpdate { json: Value },
}

fn bool_expr(p: &Rc<dyn Var>) -> Option<ast::BoolExpr> {
    if let Some(var) = p.downcast::<BoolVar>() { Some(var.lit.clone()) } else { p.downcast::<BoolExpr>().map(|expr| expr_to_bool(&expr)) }
}

fn expr_to_bool(expr: &BoolExpr) -> ast::BoolExpr {
    match expr {
        BoolExpr::Term { term, .. } => {
            if let Slot::Primitive(var) = term
                && let Some(var) = var.downcast::<BoolVar>()
            {
                return var.lit.clone();
            }
            unreachable!("Expected BoolVar in BoolExpr::Term");
        }
        BoolExpr::Eq { left, right, .. } => eq_to_bool(left, right),
        BoolExpr::Lt { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>())
            {
                return left.lin.lt(&right.lin);
            }
            unreachable!("Expected compatible primitive types in BoolExpr::Lt");
        }
        BoolExpr::Leq { left, right, .. } => {
            if let (Slot::Primitive(left), Slot::Primitive(right)) = (left, right)
                && let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>())
            {
                return left.lin.le(&right.lin);
            }
            unreachable!("Expected compatible primitive types in BoolExpr::Leq");
        }
        BoolExpr::Or { terms, .. } => ast::BoolExpr::Or(terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::And { terms, .. } => ast::BoolExpr::And(terms.iter().map(|t| expr_to_bool(t)).collect::<Vec<_>>()),
        BoolExpr::Not { term, .. } => !expr_to_bool(term),
    }
}

fn eq_to_bool(left: &Slot, right: &Slot) -> ast::BoolExpr {
    match (left, right) {
        (Slot::Primitive(left), Slot::Primitive(right)) => {
            if let (Some(left), Some(right)) = (bool_expr(left), bool_expr(right)) {
                return left.eq(&right);
            } else if let (Some(left), Some(right)) = (left.downcast::<ArithVar>(), right.downcast::<ArithVar>()) {
                return left.lin.eq(&right.lin);
            } else if let (Some(left), Some(right)) = (left.downcast::<EnumVar>(), right.downcast::<EnumVar>()) {
                return left.var.eq(&right.var);
            }
        }
        (Slot::Primitive(left), Slot::ObjectRef(right)) => {
            if let Some(left) = left.downcast::<EnumVar>() {
                return left.var.eq(**right as i32);
            }
        }
        (Slot::ObjectRef(left), Slot::Primitive(right)) => {
            if let Some(right) = right.downcast::<EnumVar>() {
                return right.var.eq(**left as i32);
            }
        }
        (Slot::ObjectRef(left), Slot::ObjectRef(right)) => {
            return (**left as i32).eq(&(**right as i32)).into();
        }
        _ => return ast::BoolExpr::False,
    }
    unreachable!("Expected compatible types in equality");
}

fn to_json(smt: &SeMiTONE, env: &dyn Env) -> Value {
    let mut env_json = serde_json::Map::new();
    for (name, slot) in env.get_slots() {
        match slot {
            Slot::Primitive(p) => {
                if let Some(bool_expr) = bool_expr(&p) {
                    match smt.get_bool_val(&bool_expr) {
                        Some(true) => {
                            env_json.insert(name, json!(true));
                        }
                        Some(false) => {
                            env_json.insert(name, json!(false));
                        }
                        None => {
                            env_json.insert(
                                name,
                                json!({
                                    "type": "bool_var",
                                    "lit": bool_expr.to_string()
                                }),
                            );
                        }
                    }
                } else if let Some(arith_var) = p.downcast::<ArithVar>() {
                    let value = smt.get_arith_val(&arith_var.lin).expect("Expected an arithmetic variable to have a value");
                    env_json.insert(name, inf_rat_to_json(&value));
                } else if let Some(string_var) = p.downcast::<StringVar>() {
                    env_json.insert(name, json!(string_var.value));
                } else if let Some(enum_var) = p.downcast::<EnumVar>() {
                    if let Some(val) = smt.get_enum_val(&enum_var.var) {
                        env_json.insert(
                            name,
                            json!({
                                "type": "object_ref",
                                "id": format!("obj-{}", val)
                            }),
                        );
                    } else {
                        env_json.insert(
                            name,
                            json!({
                                "type": "enum_var",
                                "var": enum_var.var.to_string()
                            }),
                        );
                    }
                } else {
                    unreachable!("Unexpected primitive type in slot {}", name);
                }
            }
            Slot::ObjectRef(obj_id) => {
                env_json.insert(
                    name,
                    json!({
                        "type": "object_ref",
                        "id": obj_id.to_string()
                    }),
                );
            }
            Slot::AtomRef(atm_id) => {
                env_json.insert(
                    name,
                    json!({
                        "type": "atom_ref",
                        "id": atm_id.to_string()
                    }),
                );
            }
        }
    }
    Value::Object(env_json)
}

pub fn inf_rat_to_json(val: &InfRational) -> Value {
    let mut json = rat_to_json(val.rational_part());
    if !val.infinitesimal_part().is_zero() {
        let inf = val.infinitesimal_part();
        json.as_object_mut().unwrap().insert(
            String::from("inf"),
            json!({
                "num": inf.numer().to_string(),
                "den": inf.denom().to_string()
            }),
        );
    }
    json
}

pub fn rat_to_json(val: &Rational) -> Value {
    match val {
        Rational::Finite(r) => json!({
            "num": r.numer().to_string(),
            "den": r.denom().to_string()
        }),
        Rational::PositiveInf => json!({
            "num": 1,
            "den": 0
        }),
        Rational::NegativeInf => json!({
            "num": -1,
            "den": 0
        }),
    }
}

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
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
                    SolverCommand::ReadRiDDle(riddle, responder) => {
                        let result = state.read(&riddle);
                        let is_err = result.is_err();
                        let _ = responder.send(result);
                        if is_err {
                            break;
                        }
                    }
                    SolverCommand::Solve(responder) => {
                        let result = state.solve();
                        let is_err = result.is_err();
                        let _ = responder.send(result);
                        if is_err {
                            break;
                        }
                    }
                    SolverCommand::ToJson(responder) => {
                        let _ = responder.send(Ok(state.to_json()));
                    }
                }
            }
        });
        Self { tx_cmd, tx_event }
    }

    pub async fn read(&self, riddle: String) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ReadRiDDle(riddle, reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send ReadRiDDle command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive ReadRiDDle response: {:?}", e)))?
    }

    pub async fn solve(&self) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::Solve(reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send Solve command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive Solve response: {:?}", e)))?
    }

    pub async fn to_json(&self) -> Result<Value, SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ToJson(reply_tx)).await.map_err(|e| SolverError::RuntimeError(format!("Failed to send ToJson command: {:?}", e)))?;
        reply_rx.await.map_err(|e| SolverError::RuntimeError(format!("Failed to receive ToJson response: {:?}", e)))?
    }
}
