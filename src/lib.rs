use consensus::{FALSE_LIT, LBool, TRUE_LIT, pos};
use linspire::{
    inf_rational::InfRational,
    lin::{Lin, c, v},
    rational::rat,
};
use riddle::{
    env::{BoolType, CommonEnv, CommonScope, Core, Env, Field, IntType, Method, RealType, Scope, StringType, Type, Var},
    language::{EnumDef, PredicateDef},
};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use crate::objects::{BoolVar, IntVar, RealVar, StringVar};

mod objects;

pub struct Solver {
    scope: Rc<CommonScope>,
    env: Rc<CommonEnv>,
    sat: RefCell<consensus::Engine>,
    ac: RefCell<dynamic_ac::Engine>,
    lin: RefCell<linspire::Engine>,
}

impl Solver {
    pub fn new() -> Rc<Self> {
        let core = Rc::new_cyclic(|core| Self {
            scope: {
                let core: Weak<Solver> = core.clone();
                Rc::new(CommonScope::new(core.clone(), None))
            },
            env: Rc::new(CommonEnv::new(None)),
            sat: RefCell::new(consensus::Engine::new()),
            ac: RefCell::new(dynamic_ac::Engine::new()),
            lin: RefCell::new(linspire::Engine::new()),
        });
        core
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
}

impl Scope for Solver {
    fn core(self: Rc<Self>) -> Rc<dyn Core> {
        self
    }
    fn parent(&self) -> Option<Rc<dyn Scope>> {
        None
    }

    fn get_field(&self, name: &str) -> Option<Rc<Field>> {
        self.scope.get_field(name)
    }
    fn get_method(&self, name: &str, types: &[Rc<dyn Type>]) -> Option<Rc<Method>> {
        self.scope.get_method(name, types)
    }
    fn get_class(&self, name: &str) -> Option<Rc<dyn Type>> {
        self.scope.get_class(name)
    }
    fn get_enum(&self, name: &str) -> Option<Rc<EnumDef>> {
        self.scope.get_enum(name)
    }
    fn get_predicate(&self, name: &str) -> Option<Rc<PredicateDef>> {
        self.scope.get_predicate(name)
    }
}

impl Env for Solver {
    fn parent(&self) -> Option<Rc<dyn Env>> {
        None
    }
    fn get(&self, name: &str) -> Option<Rc<dyn Var>> {
        self.env.get(name)
    }
    fn set(&self, name: String, value: Rc<dyn Var>) {
        self.env.set(name, value)
    }
}

impl Core for Solver {
    fn new_bool(&self, value: bool) -> Rc<dyn Var> {
        let bool_type = self.scope.get_class("bool").expect("Bool type not found").as_any().downcast::<BoolType>().expect("Bool type is not BoolType");
        Rc::new(BoolVar::new(bool_type, if value { TRUE_LIT } else { FALSE_LIT }))
    }
    fn new_bool_var(&self) -> Rc<dyn Var> {
        let var = self.sat.borrow_mut().add_var();
        let bool_type = self.scope.get_class("bool").expect("Bool type not found").as_any().downcast::<BoolType>().expect("Bool type is not BoolType");
        Rc::new(BoolVar::new(bool_type, pos(var)))
    }
    fn new_int(&self, value: i64) -> Rc<dyn Var> {
        let int_type = self.scope.get_class("Int").expect("Int type not found").as_any().downcast::<IntType>().expect("Int type is not IntType");
        Rc::new(IntVar::new(int_type, c(value)))
    }
    fn new_int_var(&self) -> Rc<dyn Var> {
        let var = self.lin.borrow_mut().add_var();
        let int_type = self.scope.get_class("Int").expect("Int type not found").as_any().downcast::<IntType>().expect("Int type is not IntType");
        Rc::new(IntVar::new(int_type, v(var)))
    }
    fn new_real(&self, num: i64, den: i64) -> Rc<dyn Var> {
        let real_type = self.scope.get_class("real").expect("Real type not found").as_any().downcast::<RealType>().expect("Real type is not RealType");
        Rc::new(RealVar::new(real_type, Lin::new_const(rat(num, den))))
    }
    fn new_real_var(&self) -> Rc<dyn Var> {
        let var = self.lin.borrow_mut().add_var();
        let real_type = self.scope.get_class("real").expect("Real type not found").as_any().downcast::<RealType>().expect("Real type is not RealType");
        Rc::new(RealVar::new(real_type, v(var)))
    }
    fn new_string(&self, value: &str) -> Rc<dyn Var> {
        let string_type = self.scope.get_class("string").expect("String type not found").as_any().downcast::<StringType>().expect("String type is not StringType");
        Rc::new(StringVar::new(string_type, value.to_string()))
    }
    fn new_string_var(&self) -> Rc<dyn Var> {
        let string_type = self.scope.get_class("string").expect("String type not found").as_any().downcast::<StringType>().expect("String type is not StringType");
        Rc::new(StringVar::new(string_type, String::new()))
    }

    fn sum(&self, sum: &[Rc<dyn Var>]) -> Rc<dyn Var> {
        unimplemented!()
    }
    fn opposite(&self, term: Rc<dyn Var>) -> Rc<dyn Var> {
        unimplemented!()
    }
    fn mul(&self, mul: &[Rc<dyn Var>]) -> Rc<dyn Var> {
        unimplemented!()
    }
    fn div(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Rc<dyn Var> {
        unimplemented!()
    }

    fn eq(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Rc<dyn Var> {
        unimplemented!()
    }
    fn neq(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Rc<dyn Var> {
        unimplemented!()
    }

    fn lt(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Rc<dyn Var> {
        unimplemented!()
    }
    fn leq(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Rc<dyn Var> {
        unimplemented!()
    }
    fn geq(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Rc<dyn Var> {
        unimplemented!()
    }
    fn gt(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Rc<dyn Var> {
        unimplemented!()
    }

    fn or(&self, terms: &[Rc<dyn Var>]) -> Rc<dyn Var> {
        unimplemented!()
    }
    fn and(&self, terms: &[Rc<dyn Var>]) -> Rc<dyn Var> {
        unimplemented!()
    }

    fn assert(&self, term: Rc<dyn Var>) -> bool {
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
