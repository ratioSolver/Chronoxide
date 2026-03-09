use consensus::{FALSE_LIT, LBool, TRUE_LIT, pos};
use linspire::{
    inf_rational::InfRational,
    lin::{Lin, c, v},
    rational::rat,
};
use riddle::{
    core::{CommonCore, Core},
    env::{Atom, Env, Var},
    language::{Disjunction, EnumDef, PredicateDef, RiddleError},
    scope::{Field, Method, Predicate, Scope, Type, arith_class},
};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use crate::objects::{BoolVar, IntVar, RealVar, StringVar};

mod objects;

pub struct Solver {
    core: Rc<CommonCore>,
    sat: RefCell<consensus::Engine>,
    ac: RefCell<dynamic_ac::Engine>,
    lin: RefCell<linspire::Engine>,
}

impl Solver {
    pub fn new() -> Rc<Self> {
        Rc::new_cyclic(|core| Self {
            core: {
                let core: Weak<Solver> = core.clone();
                CommonCore::new(core)
            },
            sat: RefCell::new(consensus::Engine::new()),
            ac: RefCell::new(dynamic_ac::Engine::new()),
            lin: RefCell::new(linspire::Engine::new()),
        })
    }

    pub fn bool_val(&self, obj: &BoolVar) -> LBool {
        self.sat.borrow().lit_value(&obj.lit).clone()
    }

    pub fn int_val(&self, obj: &IntVar) -> InfRational {
        self.lin.borrow().lin_val(&obj.lin).clone()
    }

    pub fn real_val(&self, obj: &RealVar) -> InfRational {
        self.lin.borrow().lin_val(&obj.lin).clone()
    }

    pub fn string_val(&self, obj: &StringVar) -> String {
        obj.value.clone()
    }

    pub fn read(&self, script: &str) {
        self.core.read(script);
    }
}

impl Scope for Solver {
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
    fn get_enum(&self, name: &str) -> Option<Rc<EnumDef>> {
        self.core.get_enum(name)
    }
    fn get_predicate(&self, name: &str) -> Option<Rc<Predicate>> {
        self.core.get_predicate(name)
    }
}

impl Env for Solver {
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

impl Core for Solver {
    fn new_bool(&self, value: bool) -> Rc<dyn Var> {
        Rc::new(BoolVar::new(self.core.bool_type(), if value { TRUE_LIT } else { FALSE_LIT }))
    }
    fn new_bool_var(&self) -> Rc<dyn Var> {
        Rc::new(BoolVar::new(self.core.bool_type(), pos(self.sat.borrow_mut().add_var())))
    }
    fn new_int(&self, value: i64) -> Rc<dyn Var> {
        Rc::new(IntVar::new(self.core.int_type(), c(value)))
    }
    fn new_int_var(&self) -> Rc<dyn Var> {
        Rc::new(IntVar::new(self.core.int_type(), v(self.lin.borrow_mut().add_var())))
    }
    fn new_real(&self, num: i64, den: i64) -> Rc<dyn Var> {
        Rc::new(RealVar::new(self.core.real_type(), Lin::new_const(rat(num, den))))
    }
    fn new_real_var(&self) -> Rc<dyn Var> {
        Rc::new(RealVar::new(self.core.real_type(), v(self.lin.borrow_mut().add_var())))
    }
    fn new_string(&self, value: &str) -> Rc<dyn Var> {
        Rc::new(StringVar::new(self.core.string_type(), value.to_string()))
    }
    fn new_string_var(&self) -> Rc<dyn Var> {
        Rc::new(StringVar::new(self.core.string_type(), String::new()))
    }

    fn sum(&self, sum: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        let mut result = c(0);
        for var in sum {
            if let Some(int_var) = var.clone().as_any().downcast_ref::<IntVar>() {
                result += &int_var.lin
            } else if let Some(real_var) = var.clone().as_any().downcast_ref::<RealVar>() {
                result += &real_var.lin
            } else {
                panic!("Expected int or RealVar");
            };
        }
        let tp = arith_class(self.clone(), sum)?;
        if tp.name() == "int" { Ok(Rc::new(IntVar::new(self.core.int_type(), result))) } else { Ok(Rc::new(RealVar::new(self.core.real_type(), result))) }
    }
    fn opposite(&self, term: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        if let Some(bool_var) = term.clone().as_any().downcast_ref::<BoolVar>() {
            Ok(Rc::new(BoolVar::new(self.core.bool_type(), !bool_var.lit)))
        } else if let Some(int_var) = term.clone().as_any().downcast_ref::<IntVar>() {
            Ok(Rc::new(IntVar::new(self.core.int_type(), -int_var.lin.clone())))
        } else if let Some(real_var) = term.clone().as_any().downcast_ref::<RealVar>() {
            Ok(Rc::new(RealVar::new(self.core.real_type(), -real_var.lin.clone())))
        } else {
            panic!("Expected bool, int, or real");
        }
    }
    fn mul(&self, mul: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        let mut result = c(1);
        for var in mul {
            if let Some(int_var) = var.clone().as_any().downcast_ref::<IntVar>() {
                if result.vars.is_empty() {
                    result = &int_var.lin * result.known_term;
                } else if int_var.lin.vars.is_empty() {
                    result = &result * int_var.lin.known_term;
                } else {
                    return Err(RiddleError::RuntimeError("Non-linear multiplication is not supported".to_string()));
                }
            } else if let Some(real_var) = var.clone().as_any().downcast_ref::<RealVar>() {
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
        if arith_class(self, mul)?.name() == "int" { Ok(Rc::new(IntVar::new(self.core.int_type(), result))) } else { Ok(Rc::new(RealVar::new(self.core.real_type(), result))) }
    }
    fn div(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        if let Some(int_var) = right.clone().as_any().downcast_ref::<IntVar>() {
            if int_var.lin.vars.is_empty() {
                if let Some(int_var_left) = left.clone().as_any().downcast_ref::<IntVar>() {
                    Ok(Rc::new(IntVar::new(self.core.int_type(), int_var_left.lin.clone() / int_var.lin.known_term)))
                } else if let Some(real_var_left) = left.clone().as_any().downcast_ref::<RealVar>() {
                    Ok(Rc::new(RealVar::new(self.core.real_type(), real_var_left.lin.clone() / int_var.lin.known_term)))
                } else {
                    Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                }
            } else {
                Err(RiddleError::RuntimeError("Non-linear division is not supported".to_string()))
            }
        } else if let Some(real_var) = right.clone().as_any().downcast_ref::<RealVar>() {
            if real_var.lin.vars.is_empty() {
                if let Some(int_var_left) = left.clone().as_any().downcast_ref::<IntVar>() {
                    Ok(Rc::new(IntVar::new(self.core.int_type(), int_var_left.lin.clone() / real_var.lin.known_term)))
                } else if let Some(real_var_left) = left.clone().as_any().downcast_ref::<RealVar>() {
                    Ok(Rc::new(RealVar::new(self.core.real_type(), real_var_left.lin.clone() / real_var.lin.known_term)))
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

    fn eq(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn neq(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }

    fn lt(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn leq(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn geq(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn gt(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }

    fn or(&self, terms: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn and(&self, terms: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }

    fn assert(&self, term: Rc<dyn Var>) -> bool {
        unimplemented!()
    }
    fn new_enum(&self, variants: &[&str]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn new_var(&self, class: Rc<dyn Type>, instances: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn new_disjunction(&self, disjunction: Disjunction) {
        unimplemented!()
    }
    fn new_atom(&self, atom: Rc<Atom>) {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use consensus::LBool;
    use linspire::inf_rational::i_i;

    use crate::objects::{IntVar, RealVar};

    use super::*;

    #[test]
    fn test_solver() {
        let solver = Solver::new();
        let bool_obj = solver.new_bool_var();
        let int_obj = solver.new_int_var();
        let real_obj = solver.new_real_var();

        assert_eq!(solver.bool_val(bool_obj.as_any().downcast_ref::<BoolVar>().unwrap()), LBool::Undef);
        assert_eq!(solver.int_val(int_obj.as_any().downcast_ref::<IntVar>().unwrap()), i_i(0));
        assert_eq!(solver.real_val(real_obj.as_any().downcast_ref::<RealVar>().unwrap()), i_i(0));
    }

    #[test]
    fn test_int_sum() {
        let solver = Solver::new();
        let int_obj1 = solver.new_int_var();
        let int_obj2 = solver.new_int_var();
        let sum = solver.sum(&[int_obj1.clone(), int_obj2.clone()]).unwrap();
        assert_eq!(solver.int_val(sum.as_any().downcast_ref::<IntVar>().unwrap()), i_i(0));
    }
}
