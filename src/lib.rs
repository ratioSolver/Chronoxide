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

    fn sum(self: Rc<Self>, sum: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        let mut result = c(0);
        for var in sum {
            if let Some(int_var) = var.clone().as_any().downcast_ref::<IntVar>() {
                result += &int_var.lin
            } else if let Some(real_var) = var.clone().as_any().downcast_ref::<RealVar>() {
                result += &real_var.lin
            } else {
                panic!("Expected IntVar or RealVar");
            };
        }
        let tp = arith_class(self.clone(), sum)?;
        if tp.name() == "Int" { Ok(Rc::new(IntVar::new(self.core.int_type(), result))) } else { Ok(Rc::new(RealVar::new(self.core.real_type(), result))) }
    }
    fn opposite(self: Rc<Self>, term: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        if let Some(bool_var) = term.clone().as_any().downcast_ref::<BoolVar>() {
            Ok(Rc::new(BoolVar::new(self.core.bool_type(), !bool_var.lit)))
        } else if let Some(int_var) = term.clone().as_any().downcast_ref::<IntVar>() {
            Ok(Rc::new(IntVar::new(self.core.int_type(), -int_var.lin.clone())))
        } else if let Some(real_var) = term.clone().as_any().downcast_ref::<RealVar>() {
            Ok(Rc::new(RealVar::new(self.core.real_type(), -real_var.lin.clone())))
        } else {
            panic!("Expected BoolVar, IntVar, or RealVar");
        }
    }
    fn mul(self: Rc<Self>, mul: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn div(self: Rc<Self>, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }

    fn eq(self: Rc<Self>, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn neq(self: Rc<Self>, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }

    fn lt(self: Rc<Self>, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn leq(self: Rc<Self>, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn geq(self: Rc<Self>, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn gt(self: Rc<Self>, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }

    fn or(self: Rc<Self>, terms: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn and(self: Rc<Self>, terms: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }

    fn assert(self: Rc<Self>, term: Rc<dyn Var>) -> bool {
        unimplemented!()
    }
    fn new_enum(self: Rc<Self>, variants: &[&str]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn new_var(self: Rc<Self>, class: Rc<dyn Type>, instances: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn new_disjunction(self: Rc<Self>, disjunction: Disjunction) {
        unimplemented!()
    }
    fn new_atom(self: Rc<Self>, atom: Rc<Atom>) {
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
}
