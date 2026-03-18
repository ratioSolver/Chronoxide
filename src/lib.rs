use crate::{
    flaw::{Flaw, OrFlaw, Resolver},
    objects::{ArithVar, BoolVar, RealVar, StringVar},
};
use consensus::{FALSE_LIT, LBool, TRUE_LIT, neg, pos};
use linspire::{
    inf_rational::InfRational,
    lin::{Lin, c, v},
    rational::rat,
};
use riddle::{
    core::{CommonCore, Core},
    env::{Atom, BoolExpr, Env, Var},
    language::{Disjunction, EnumDef, RiddleError},
    scope::{Field, Method, Predicate, Scope, Type, arith_class},
};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

mod flaw;
mod objects;

pub struct Solver {
    core: Rc<CommonCore>,
    slv: Weak<Solver>,
    sat: RefCell<consensus::Engine>,
    ac: RefCell<dynamic_ac::Engine>,
    lin: RefCell<linspire::Engine>,
    flaws: RefCell<Vec<Rc<dyn Flaw>>>,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    c_res: Option<Rc<dyn Resolver>>,
}

impl Solver {
    pub fn new() -> Rc<Self> {
        Rc::new_cyclic(|core| Self {
            core: {
                let core: Weak<Solver> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            sat: RefCell::new(consensus::Engine::new()),
            ac: RefCell::new(dynamic_ac::Engine::new()),
            lin: RefCell::new(linspire::Engine::new()),
            flaws: RefCell::new(vec![]),
            resolvers: RefCell::new(vec![]),
            c_res: None,
        })
    }

    pub fn bool_val(&self, obj: &BoolVar) -> LBool {
        self.sat.borrow().lit_value(&obj.lit).clone()
    }

    pub fn int_val(&self, obj: &ArithVar) -> InfRational {
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
        Rc::new(RealVar::new(self.real_type(), Lin::new_const(rat(num, den))))
    }
    fn new_real_var(&self) -> Rc<dyn Var> {
        Rc::new(RealVar::new(self.real_type(), v(self.lin.borrow_mut().add_var())))
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
            } else if let Some(real_var) = var.clone().as_any().downcast_ref::<RealVar>() {
                result += &real_var.lin
            } else {
                panic!("Expected int or RealVar");
            };
        }
        let tp = arith_class(self.clone(), sum)?;
        if tp.name() == "int" { Ok(Rc::new(ArithVar::new(self.int_type(), result))) } else { Ok(Rc::new(RealVar::new(self.real_type(), result))) }
    }
    fn opposite(&self, term: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        if let Some(bool_var) = term.clone().as_any().downcast_ref::<BoolVar>() {
            Ok(Rc::new(BoolVar::new(self.bool_type(), !bool_var.lit)))
        } else if let Some(int_var) = term.clone().as_any().downcast_ref::<ArithVar>() {
            Ok(Rc::new(ArithVar::new(self.int_type(), -int_var.lin.clone())))
        } else if let Some(real_var) = term.clone().as_any().downcast_ref::<RealVar>() {
            Ok(Rc::new(RealVar::new(self.real_type(), -real_var.lin.clone())))
        } else {
            panic!("Expected bool, int, or real");
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
        if arith_class(self, mul)?.name() == "int" { Ok(Rc::new(ArithVar::new(self.int_type(), result))) } else { Ok(Rc::new(RealVar::new(self.real_type(), result))) }
    }
    fn div(&self, left: Rc<dyn Var>, right: Rc<dyn Var>) -> Result<Rc<dyn Var>, RiddleError> {
        if let Some(int_var) = right.clone().as_any().downcast_ref::<ArithVar>() {
            if int_var.lin.vars.is_empty() {
                if let Some(int_var_left) = left.clone().as_any().downcast_ref::<ArithVar>() {
                    Ok(Rc::new(ArithVar::new(self.int_type(), int_var_left.lin.clone() / int_var.lin.known_term)))
                } else if let Some(real_var_left) = left.clone().as_any().downcast_ref::<RealVar>() {
                    Ok(Rc::new(RealVar::new(self.real_type(), real_var_left.lin.clone() / int_var.lin.known_term)))
                } else {
                    Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                }
            } else {
                Err(RiddleError::RuntimeError("Non-linear division is not supported".to_string()))
            }
        } else if let Some(real_var) = right.clone().as_any().downcast_ref::<RealVar>() {
            if real_var.lin.vars.is_empty() {
                if let Some(int_var_left) = left.clone().as_any().downcast_ref::<ArithVar>() {
                    Ok(Rc::new(ArithVar::new(self.int_type(), int_var_left.lin.clone() / real_var.lin.known_term)))
                } else if let Some(real_var_left) = left.clone().as_any().downcast_ref::<RealVar>() {
                    Ok(Rc::new(RealVar::new(self.real_type(), real_var_left.lin.clone() / real_var.lin.known_term)))
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
        match term.as_ref() {
            BoolExpr::Term { term, .. } => {
                let bool_var = term.clone().as_any().downcast::<BoolVar>().expect("Expected BoolVar");
                if let Some(res) = &self.c_res {
                    return self.sat.borrow_mut().add_clause(vec![neg(res.as_ref().rho()), bool_var.lit]);
                } else {
                    return self.sat.borrow_mut().add_clause(vec![bool_var.lit]);
                }
            }
            BoolExpr::Eq { left, right, .. } => {
                unimplemented!()
            }
            BoolExpr::Lt { left, right, .. } => {
                let left_lin = left.clone().as_any().downcast::<ArithVar>().expect("Expected ArithVar").lin.clone();
                let right_lin = right.clone().as_any().downcast::<ArithVar>().expect("Expected ArithVar").lin.clone();
                let lin_cnstr = if self.c_res.is_none() { None } else { self.c_res.as_ref().unwrap().lin_constraints() };
                self.lin.borrow_mut().new_lt(&left_lin, &right_lin, true, lin_cnstr);
                return true;
            }
            BoolExpr::Leq { left, right, .. } => {
                let left_lin = left.clone().as_any().downcast::<ArithVar>().expect("Expected ArithVar").lin.clone();
                let right_lin = right.clone().as_any().downcast::<ArithVar>().expect("Expected ArithVar").lin.clone();
                let lin_cnstr = if self.c_res.is_none() { None } else { self.c_res.as_ref().unwrap().lin_constraints() };
                self.lin.borrow_mut().new_le(&left_lin, &right_lin, lin_cnstr);
                return true;
            }
            BoolExpr::Or { terms, .. } => {
                let lits = terms
                    .iter()
                    .map(|term| match term.as_ref() {
                        BoolExpr::Term { term, .. } => term.clone().as_any().downcast::<BoolVar>().expect("Expected BoolVar").lit,
                        _ => panic!("Expected BoolExpr::Term"),
                    })
                    .collect();
                let phi = if self.c_res.is_none() { 0 } else { self.c_res.as_ref().unwrap().rho() };
                let flaw = OrFlaw::new(self.slv.upgrade().expect("Solver has been dropped"), phi, lits);
                self.flaws.borrow_mut().push(flaw.clone());
                return true;
            }
            BoolExpr::And { terms, .. } => {
                for term in terms {
                    if !self.assert(term.clone()) {
                        return false;
                    }
                }
                return true;
            }
            BoolExpr::Not { term, .. } => match term.as_ref() {
                BoolExpr::Term { term, .. } => {
                    let bool_var = term.clone().as_any().downcast::<BoolVar>().expect("Expected BoolVar");
                    if let Some(res) = &self.c_res {
                        return self.sat.borrow_mut().add_clause(vec![neg(res.as_ref().rho()), !bool_var.lit]);
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![!bool_var.lit]);
                    }
                }
                BoolExpr::Eq { left, right, .. } => {
                    unimplemented!()
                }
                BoolExpr::Lt { left, right, .. } => {
                    let left_lin = left.clone().as_any().downcast::<ArithVar>().expect("Expected ArithVar").lin.clone();
                    let right_lin = right.clone().as_any().downcast::<ArithVar>().expect("Expected ArithVar").lin.clone();
                    let lin_cnstr = if self.c_res.is_none() { None } else { self.c_res.as_ref().unwrap().lin_constraints() };
                    self.lin.borrow_mut().new_ge(&left_lin, &right_lin, lin_cnstr);
                    return true;
                }
                BoolExpr::Leq { left, right, .. } => {
                    let left_lin = left.clone().as_any().downcast::<ArithVar>().expect("Expected ArithVar").lin.clone();
                    let right_lin = right.clone().as_any().downcast::<ArithVar>().expect("Expected ArithVar").lin.clone();
                    let lin_cnstr = if self.c_res.is_none() { None } else { self.c_res.as_ref().unwrap().lin_constraints() };
                    self.lin.borrow_mut().new_gt(&left_lin, &right_lin, true, lin_cnstr);
                    return true;
                }
                _ => panic!("Expected BoolExpr::Term"),
            },
            _ => panic!("Expected a BoolExpr in assert"),
        }
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

    use crate::objects::{ArithVar, RealVar};

    use super::*;

    #[test]
    fn test_solver() {
        let solver = Solver::new();
        let bool_obj = solver.new_bool_var();
        let int_obj = solver.new_int_var();
        let real_obj = solver.new_real_var();

        assert_eq!(solver.bool_val(bool_obj.as_any().downcast_ref::<BoolVar>().unwrap()), LBool::Undef);
        assert_eq!(solver.int_val(int_obj.as_any().downcast_ref::<ArithVar>().unwrap()), i_i(0));
        assert_eq!(solver.real_val(real_obj.as_any().downcast_ref::<RealVar>().unwrap()), i_i(0));
    }

    #[test]
    fn test_int_sum() {
        let solver = Solver::new();
        let int_obj1 = solver.new_int_var();
        let int_obj2 = solver.new_int_var();
        let sum = solver.sum(&[int_obj1.clone(), int_obj2.clone()]).unwrap();
        assert_eq!(solver.int_val(sum.as_any().downcast_ref::<ArithVar>().unwrap()), i_i(0));
    }
}
