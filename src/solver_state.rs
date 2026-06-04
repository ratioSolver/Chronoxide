use crate::{
    ToJson,
    graph::Graph,
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
use serde_json::Value;
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;
use tracing::trace;
use watchsat::{FALSE_LIT, Lit, TRUE_LIT, pos};

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    pub graph: RefCell<Graph>,
    pub sat: RefCell<watchsat::Engine>,
    pub ac: RefCell<ac3rm::Engine>,
    pub lin: RefCell<linarith::Engine>,
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
            graph: RefCell::new(Graph::new(core.clone())),
            sat: RefCell::new(watchsat::Engine::new()),
            ac: RefCell::new(ac3rm::Engine::new()),
            lin: RefCell::new(linarith::Engine::new()),
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

    fn assert(&self, _term: Rc<BoolExpr>) -> bool {
        true
    }

    fn new_var(&self, class: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let vals = instances.iter().map(|id| **id as i32).collect::<Vec<_>>();
        let var = self.ac.borrow_mut().add_var(vals);
        let var = Rc::new(EnumVar::new(class, var));
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
        atm
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

impl ToJson for SolverState {
    fn to_json(&self) -> Value {
        Value::Null
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
