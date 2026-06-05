use crate::{
    ToJson,
    flaws::{Flaw, FlawId, Resolver, ResolverId},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
    solver::{SolverError, SolverEvent},
};
use linarith::{Lin, Rational};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, Var},
    language::Disjunction,
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;
use tracing::trace;
use watchsat::{FALSE_LIT, Lit, TRUE_LIT, neg, pos};

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    pub sat: RefCell<watchsat::Engine>,
    pub ac: RefCell<ac3rm::Engine>,
    pub lin: RefCell<linarith::Engine>,
    flaws: Vec<Box<dyn Flaw>>,
    resolvers: Vec<Box<dyn Resolver>>,
    c_flaw: RefCell<Option<FlawId>>,
    c_res: RefCell<Option<ResolverId>>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl SolverState {
    pub(super) fn new(tx_event: broadcast::Sender<SolverEvent>) -> Rc<Self> {
        Rc::new_cyclic(|core| SolverState {
            core: {
                let core: Weak<SolverState> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            sat: RefCell::new(watchsat::Engine::new()),
            ac: RefCell::new(ac3rm::Engine::new()),
            lin: RefCell::new(linarith::Engine::new()),
            flaws: Vec::new(),
            resolvers: Vec::new(),
            c_flaw: RefCell::new(None),
            c_res: RefCell::new(None),
            tx_event,
        })
    }

    pub(super) fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    pub(super) fn solve(&self) -> bool {
        trace!("Solving problem...");
        true
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
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), if value { TRUE_LIT } else { FALSE_LIT })))
    }
    fn new_bool_var(&self) -> Slot {
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), pos(self.sat.borrow_mut().add_var()))))
    }
    fn new_int(&self, value: i64) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), Lin::from(value))))
    }
    fn new_int_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), Lin::from(self.lin.borrow_mut().add_var()))))
    }
    fn new_real(&self, num: i64, den: i64) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), Lin::from(Rational::new(num, den)))))
    }
    fn new_real_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), Lin::from(self.lin.borrow_mut().add_var()))))
    }
    fn new_string(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), value.to_string())))
    }
    fn new_string_var(&self) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), String::new())))
    }

    fn sum(&self, sum: &[Slot]) -> Result<Slot, RiddleError> {
        let mut result = Lin::from(0);
        for var in sum {
            match var {
                Slot::Primitive(var) => {
                    if let Some(var) = var.clone().as_any().downcast_ref::<ArithVar>() {
                        result += &var.lin
                    } else {
                        return Err(RiddleError::RuntimeError("Expected int or real".to_string()));
                    };
                }
                _ => return Err(RiddleError::RuntimeError("Expected int or real".to_string())),
            }
        }
        let tp = arith_type(self, sum)?;
        if tp.name() == "int" { Ok(Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), result)))) } else { Ok(Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), result)))) }
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        match term {
            Slot::Primitive(var) => {
                if let Some(arith_var) = var.as_any().downcast_ref::<ArithVar>() {
                    Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_var.var_type(), -arith_var.lin.clone()))))
                } else {
                    Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                }
            }
            _ => Err(RiddleError::RuntimeError("Expected int or real".to_string())),
        }
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        let mut result = Lin::from(1);
        for var in mul {
            match var {
                Slot::Primitive(var) => {
                    if let Some(var) = var.clone().as_any().downcast_ref::<ArithVar>() {
                        if result.vars.is_empty() {
                            result = &var.lin * result.known_term;
                        } else if var.lin.vars.is_empty() {
                            result = &result * var.lin.known_term;
                        } else {
                            return Err(RiddleError::RuntimeError("Non-linear multiplication is not supported".to_string()));
                        }
                    } else {
                        panic!("Expected int or real");
                    };
                }
                _ => return Err(RiddleError::RuntimeError("Expected int or real".to_string())),
            }
        }
        if arith_type(self, mul)?.name() == "int" { Ok(Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), result)))) } else { Ok(Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), result)))) }
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        match (left, right) {
            (Slot::Primitive(left_var), Slot::Primitive(right_var)) => {
                if let Some(right_arith_var) = right_var.as_any().downcast_ref::<ArithVar>() {
                    if right_arith_var.lin.vars.is_empty() {
                        if let Some(left_arith_var) = left_var.as_any().downcast_ref::<ArithVar>() {
                            let result_lin = if left_arith_var.var_type().name() == "int" && right_arith_var.var_type().name() == "int" {
                                ArithVar::new(self.int_type(), left_arith_var.lin.clone() / right_arith_var.lin.known_term)
                            } else {
                                ArithVar::new(self.real_type(), left_arith_var.lin.clone() / right_arith_var.lin.known_term)
                            };
                            Ok(Slot::Primitive(Rc::new(result_lin)))
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
            _ => Err(RiddleError::RuntimeError("Expected int or real".to_string())),
        }
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        let c_res = self.c_res.borrow().map_or(None, |res_id| self.resolvers.get(*res_id).map(|res| res.as_ref()));
        match term.as_ref() {
            BoolExpr::Term { term, .. } => {
                let lit = bool_lit(term);
                if let Some(res) = c_res {
                    return self.sat.borrow_mut().add_clause(vec![neg(res.rho()), lit]).is_ok();
                } else {
                    return self.sat.borrow_mut().add_clause(vec![lit]).is_ok();
                }
            }
            BoolExpr::Eq { left, right, .. } => {
                let rho = c_res.map_or(watchsat::TRUE_LIT, |res| pos(res.rho()));
                match (left, right) {
                    (Slot::Primitive(left), Slot::Primitive(right)) => {
                        if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<BoolVar>(), right.clone().as_any().downcast_ref::<BoolVar>()) {
                            let left_lit = left.lit;
                            let right_lit = right.lit;
                            if c_res.is_some() {
                                return self.sat.borrow_mut().add_clause(vec![!rho, left_lit, !right_lit]).is_ok() && self.sat.borrow_mut().add_clause(vec![!rho, !left_lit, right_lit]).is_ok();
                            } else {
                                return self.sat.borrow_mut().add_clause(vec![left_lit, !right_lit]).is_ok() && self.sat.borrow_mut().add_clause(vec![!left_lit, right_lit]).is_ok();
                            }
                        } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<ArithVar>(), right.clone().as_any().downcast_ref::<ArithVar>()) {
                            let left_lin = &left.lin;
                            let right_lin = &right.lin;
                            let lin_cnstr = c_res.and_then(|res| res.lin_guard());
                            return self.lin.borrow_mut().new_eq(left_lin, right_lin, lin_cnstr).is_ok();
                        } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<StringVar>(), right.clone().as_any().downcast_ref::<StringVar>()) {
                            if c_res.is_some() {
                                return self.sat.borrow_mut().add_clause(vec![!rho]).is_ok();
                            } else {
                                left.value == right.value
                            }
                        } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<EnumVar>(), right.clone().as_any().downcast_ref::<EnumVar>()) {
                            let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Equality(left.var, right.var));
                            if let Some(res) = c_res {
                                res.add_ac_constraint(constraint_id);
                                true
                            } else {
                                return self.ac.borrow_mut().assert(constraint_id).is_ok();
                            }
                        } else {
                            return self.sat.borrow_mut().add_clause(vec![!rho]).is_ok();
                        }
                    }
                    (Slot::Primitive(left), Slot::ObjectRef(right)) => {
                        if let Some(left) = left.clone().as_any().downcast_ref::<EnumVar>() {
                            let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Set(left.var, **right as i32));
                            if let Some(res) = c_res {
                                res.add_ac_constraint(constraint_id);
                                true
                            } else {
                                return self.ac.borrow_mut().assert(constraint_id).is_ok();
                            }
                        } else {
                            return self.sat.borrow_mut().add_clause(vec![!rho]).is_ok();
                        }
                    }
                    (Slot::ObjectRef(left), Slot::Primitive(right)) => {
                        if let Some(right) = right.clone().as_any().downcast_ref::<EnumVar>() {
                            let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Set(right.var, **left as i32));
                            if let Some(res) = c_res {
                                res.add_ac_constraint(constraint_id);
                                true
                            } else {
                                return self.ac.borrow_mut().assert(constraint_id).is_ok();
                            }
                        } else {
                            return self.sat.borrow_mut().add_clause(vec![!rho]).is_ok();
                        }
                    }
                    _ => return self.sat.borrow_mut().add_clause(vec![!rho]).is_ok(),
                }
            }
            BoolExpr::Lt { left, right, .. } => {
                let left_lin = numeric_lin(left);
                let right_lin = numeric_lin(right);
                let lin_cnstr = c_res.and_then(|res| res.lin_guard());
                return self.lin.borrow_mut().new_lt(&left_lin, &right_lin, true, lin_cnstr).is_ok();
            }
            BoolExpr::Leq { left, right, .. } => {
                let left_lin = numeric_lin(left);
                let right_lin = numeric_lin(right);
                let lin_cnstr = c_res.and_then(|res| res.lin_guard());
                return self.lin.borrow_mut().new_le(&left_lin, &right_lin, lin_cnstr).is_ok();
            }
            BoolExpr::Or { terms, .. } => {
                let lits: Vec<Lit> = terms
                    .iter()
                    .map(|term| match term.as_ref() {
                        BoolExpr::Term { term, .. } => match term {
                            Slot::Primitive(var) => {
                                if let Some(bool_var) = var.clone().as_any().downcast_ref::<BoolVar>() {
                                    bool_var.lit
                                } else {
                                    panic!("Expected BoolVar");
                                }
                            }
                            _ => panic!("Expected BoolExpr::Term with a BoolVar"),
                        },
                        _ => panic!("Expected BoolExpr::Term"),
                    })
                    .collect();
                let rho = c_res.map_or(watchsat::TRUE_LIT, |res| pos(res.rho()));
                let cause = c_res.map(|res| res.id());
                let flaw_id = FlawId(self.flaws.len());
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
                    if let Some(res) = c_res {
                        return self.sat.borrow_mut().add_clause(vec![neg(res.rho()), !lit]).is_ok();
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![!lit]).is_ok();
                    }
                }
                BoolExpr::Eq { left, right, .. } => {
                    let rho = c_res.map_or(watchsat::TRUE_LIT, |res| pos(res.rho()));
                    match (left, right) {
                        (Slot::Primitive(left_v), Slot::Primitive(right_v)) => {
                            if let (Some(left), Some(right)) = (left_v.clone().as_any().downcast_ref::<BoolVar>(), right_v.clone().as_any().downcast_ref::<BoolVar>()) {
                                let left_lit = left.lit;
                                let right_lit = right.lit;
                                if c_res.is_some() { self.sat.borrow_mut().add_clause(vec![!rho, !left_lit, !right_lit]).is_ok() } else { self.sat.borrow_mut().add_clause(vec![!left_lit, !right_lit]).is_ok() }
                            } else if let (Some(_left), Some(_right)) = (left_v.clone().as_any().downcast_ref::<ArithVar>(), right_v.clone().as_any().downcast_ref::<ArithVar>()) {
                                self.assert(Rc::new(BoolExpr::Or {
                                    var_type: Rc::downgrade(&self.bool_type()),
                                    terms: vec![Rc::new(BoolExpr::Lt { var_type: Rc::downgrade(&self.bool_type()), left: left.clone(), right: right.clone() }), Rc::new(BoolExpr::Lt { var_type: Rc::downgrade(&self.bool_type()), left: left.clone(), right: right.clone() })],
                                }))
                            } else if let (Some(left), Some(right)) = (left_v.clone().as_any().downcast_ref::<StringVar>(), right_v.clone().as_any().downcast_ref::<StringVar>()) {
                                if c_res.is_some() && left.value == right.value { self.sat.borrow_mut().add_clause(vec![!rho]).is_ok() } else { true }
                            } else if let (Some(left), Some(right)) = (left_v.clone().as_any().downcast_ref::<EnumVar>(), right_v.clone().as_any().downcast_ref::<EnumVar>()) {
                                let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Inequality(left.var, right.var));
                                if let Some(res) = c_res {
                                    res.add_ac_constraint(constraint_id);
                                    true
                                } else {
                                    self.ac.borrow_mut().assert(constraint_id).is_ok()
                                }
                            } else {
                                true
                            }
                        }
                        (Slot::Primitive(left), Slot::ObjectRef(right)) => {
                            if let Some(left) = left.clone().as_any().downcast_ref::<EnumVar>() {
                                let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Forbid(left.var, **right as i32));
                                if let Some(res) = c_res {
                                    res.add_ac_constraint(constraint_id);
                                    true
                                } else {
                                    self.ac.borrow_mut().assert(constraint_id).is_ok()
                                }
                            } else {
                                self.sat.borrow_mut().add_clause(vec![!rho]).is_ok()
                            }
                        }
                        (Slot::ObjectRef(left), Slot::Primitive(right)) => {
                            if let Some(right) = right.clone().as_any().downcast_ref::<EnumVar>() {
                                let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Forbid(right.var, **left as i32));
                                if let Some(res) = c_res {
                                    res.add_ac_constraint(constraint_id);
                                    true
                                } else {
                                    self.ac.borrow_mut().assert(constraint_id).is_ok()
                                }
                            } else {
                                self.sat.borrow_mut().add_clause(vec![!rho]).is_ok()
                            }
                        }
                        _ => true,
                    }
                }
                BoolExpr::Lt { left, right, .. } => {
                    let left_lin = numeric_lin(left);
                    let right_lin = numeric_lin(right);
                    let lin_cnstr = c_res.and_then(|res| res.lin_guard());
                    return self.lin.borrow_mut().new_ge(&left_lin, &right_lin, lin_cnstr).is_ok();
                }
                BoolExpr::Leq { left, right, .. } => {
                    let left_lin = numeric_lin(left);
                    let right_lin = numeric_lin(right);
                    let lin_cnstr = c_res.and_then(|res| res.lin_guard());
                    return self.lin.borrow_mut().new_gt(&left_lin, &right_lin, true, lin_cnstr).is_ok();
                }
                _ => panic!("Expected BoolExpr::Term, BoolExpr::Eq, BoolExpr::Lt, or BoolExpr::Leq"),
            },
        }
    }

    fn new_var(&self, class: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let vals = instances.iter().map(|id| **id as i32).collect::<Vec<_>>();
        let var = self.ac.borrow_mut().add_var(vals);
        let var = Rc::new(EnumVar::new(class, var));
        let c_res = self.c_res.borrow().map_or(None, |res_id| self.resolvers.get(*res_id).map(|res| res.as_ref()));
        let rho = c_res.map_or(watchsat::TRUE_LIT, |res| pos(res.rho()));
        let cause = c_res.map(|res| res.id());
        let flaw_id = FlawId(self.flaws.len());
        Ok(Slot::Primitive(var))
    }

    fn new_disjunction(&self, _disjunction: Disjunction) {
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
        let c_res = self.c_res.borrow().map_or(None, |res_id| self.resolvers.get(*res_id).map(|res| res.as_ref()));
        let rho = c_res.map_or(watchsat::TRUE_LIT, |res| pos(res.rho()));
        let cause = c_res.map(|res| res.id());
        let flaw_id = FlawId(self.flaws.len());
        let sigma = self.sat.borrow_mut().add_var();
        atm
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

impl ToJson for SolverState {
    fn to_json(&self) -> Value {
        let mut slv = json!({
            "flaws": self.flaws.iter().map(|f| f.to_json()).collect::<Vec<_>>(),
            "resolvers": self.resolvers.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
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

fn bool_lit(var: &Slot) -> Lit {
    if let Slot::Primitive(var) = var {
        var.clone().as_any().downcast_ref::<BoolVar>().expect("Expected BoolVar").lit
    } else {
        panic!("Expected BoolVar");
    }
}

fn numeric_lin(var: &Slot) -> Lin {
    if let Slot::Primitive(var) = var {
        var.clone().as_any().downcast_ref::<ArithVar>().expect("Expected ArithVar").lin.clone()
    } else {
        panic!("Expected ArithVar");
    }
}
