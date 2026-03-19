use crate::{
    flaw::{Flaw, OrFlaw, Resolver},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
};
use consensus::{FALSE_LIT, LBool, Lit, TRUE_LIT, neg, pos};
use linspire::{
    inf_rational::InfRational,
    lin::{Lin, c, v},
    rational::rat,
};
use riddle::{
    core::{CommonCore, Core},
    env::{Atom, BoolExpr, Env, Var},
    language::{Disjunction, RiddleError},
    scope::{Enum, Field, Method, Predicate, Scope, Type, arith_class},
};
use std::{
    cell::RefCell,
    collections::HashMap,
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
    variants: RefCell<HashMap<String, i32>>,
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
            variants: RefCell::new(HashMap::new()),
        })
    }

    pub fn bool_val(&self, obj: &BoolVar) -> LBool {
        self.sat.borrow().lit_value(&obj.lit).clone()
    }

    pub fn int_val(&self, obj: &ArithVar) -> InfRational {
        self.lin.borrow().lin_val(&obj.lin)
    }

    pub fn real_val(&self, obj: &ArithVar) -> InfRational {
        self.lin.borrow().lin_val(&obj.lin)
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
        match term.as_ref() {
            BoolExpr::Term { term, .. } => {
                let lit = bool_lit(term);
                if let Some(res) = &self.c_res {
                    return self.sat.borrow_mut().add_clause(vec![neg(res.as_ref().rho()), lit]);
                } else {
                    return self.sat.borrow_mut().add_clause(vec![lit]);
                }
            }
            BoolExpr::Eq { left, right, .. } => {
                let rho = if self.c_res.is_some() { self.c_res.as_ref().unwrap().rho() } else { 0 };
                if let Some(left_var) = left.clone().as_any().downcast_ref::<BoolVar>() {
                    if let Some(right_var) = right.clone().as_any().downcast_ref::<BoolVar>() {
                        let left_lit = left_var.lit;
                        let right_lit = right_var.lit;
                        if self.c_res.is_some() {
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
                        let lin_cnstr = if self.c_res.is_some() { self.c_res.as_ref().unwrap().lin_constraints() } else { None };
                        return self.lin.borrow_mut().new_eq(left_lin, right_lin, lin_cnstr);
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                    }
                } else if let Some(left_var) = left.clone().as_any().downcast_ref::<StringVar>() {
                    if let Some(right_var) = right.clone().as_any().downcast_ref::<StringVar>() {
                        if self.c_res.is_some() {
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
                                if let Some(res) = &self.c_res {
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
                let lin_cnstr = if self.c_res.is_some() { self.c_res.as_ref().unwrap().lin_constraints() } else { None };
                return self.lin.borrow_mut().new_lt(&left_lin, &right_lin, true, lin_cnstr);
            }
            BoolExpr::Leq { left, right, .. } => {
                let left_lin = numeric_lin(left);
                let right_lin = numeric_lin(right);
                let lin_cnstr = if self.c_res.is_some() { self.c_res.as_ref().unwrap().lin_constraints() } else { None };
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
                let rho = if self.c_res.is_some() { self.c_res.as_ref().unwrap().rho() } else { 0 };
                let flaw = OrFlaw::new(self.slv.upgrade().expect("Solver has been dropped"), rho, lits);
                self.flaws.borrow_mut().push(flaw.clone());
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
                    if let Some(res) = &self.c_res {
                        return self.sat.borrow_mut().add_clause(vec![neg(res.as_ref().rho()), !lit]);
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![!lit]);
                    }
                }
                BoolExpr::Eq { left, right, .. } => {
                    let rho = if self.c_res.is_some() { self.c_res.as_ref().unwrap().rho() } else { 0 };
                    if let Some(left_bool_var) = left.clone().as_any().downcast_ref::<BoolVar>() {
                        if let Some(right_bool_var) = right.clone().as_any().downcast_ref::<BoolVar>() {
                            let left_lit = left_bool_var.lit;
                            let right_lit = right_bool_var.lit;
                            if self.c_res.is_some() {
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
                        if self.c_res.is_some() && left_string_var.value == right_string_var.value {
                            return self.sat.borrow_mut().add_clause(vec![neg(rho)]);
                        } else {
                            return left_string_var.value != right_string_var.value;
                        }
                    } else if let Some(left_var) = left.clone().as_any().downcast_ref::<EnumVar>() {
                        if let Some(right_var) = right.clone().as_any().downcast_ref::<EnumVar>() {
                            match self.ac.borrow_mut().new_neq(left_var.var, right_var.var) {
                                Ok(c) => {
                                    if let Some(res) = &self.c_res {
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
                    let lin_cnstr = if self.c_res.is_some() { self.c_res.as_ref().unwrap().lin_constraints() } else { None };
                    return self.lin.borrow_mut().new_ge(&left_lin, &right_lin, lin_cnstr);
                }
                BoolExpr::Leq { left, right, .. } => {
                    let left_lin = numeric_lin(left);
                    let right_lin = numeric_lin(right);
                    let lin_cnstr = if self.c_res.is_some() { self.c_res.as_ref().unwrap().lin_constraints() } else { None };
                    return self.lin.borrow_mut().new_gt(&left_lin, &right_lin, true, lin_cnstr);
                }
                _ => panic!("Expected BoolExpr::Term, BoolExpr::Eq, BoolExpr::Lt, or BoolExpr::Leq"),
            },
        }
    }
    fn new_enum(&self, enum_type: Rc<Enum>) -> Result<Rc<dyn Var>, RiddleError> {
        let mut map = self.variants.borrow_mut();
        let mut vals: Vec<i32> = Vec::new();
        for variant in enum_type.values() {
            if let Some(val) = map.get(variant) {
                vals.push(*val);
            } else {
                let val = map.len() as i32;
                map.insert(variant.to_string(), val);
                vals.push(val);
            }
        }
        let var = self.ac.borrow_mut().add_var(vals);
        Ok(Rc::new(EnumVar::new(enum_type, var)))
    }
    fn new_var(&self, _class: Rc<dyn Type>, _instances: &[Rc<dyn Var>]) -> Result<Rc<dyn Var>, RiddleError> {
        unimplemented!()
    }
    fn new_disjunction(&self, _disjunction: Disjunction) {
        unimplemented!()
    }
    fn new_atom(&self, _atom: Rc<Atom>) {
        unimplemented!()
    }
}

fn bool_lit(var: &Rc<dyn Var>) -> Lit {
    var.clone().as_any().downcast_ref::<BoolVar>().expect("Expected BoolVar").lit
}

fn numeric_lin(var: &Rc<dyn Var>) -> Lin {
    var.clone().as_any().downcast_ref::<ArithVar>().expect("Expected ArithVar").lin.clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::objects::ArithVar;
    use consensus::LBool;
    use linspire::inf_rational::i_i;

    #[test]
    fn test_solver() {
        let solver = Solver::new();
        let bool_obj = solver.new_bool_var();
        let int_obj = solver.new_int_var();
        let real_obj = solver.new_real_var();

        assert_eq!(solver.bool_val(bool_obj.as_any().downcast_ref::<BoolVar>().unwrap()), LBool::Undef);
        assert_eq!(solver.int_val(int_obj.as_any().downcast_ref::<ArithVar>().unwrap()), i_i(0));
        assert_eq!(solver.real_val(real_obj.as_any().downcast_ref::<ArithVar>().unwrap()), i_i(0));
    }

    #[test]
    fn test_int_sum() {
        let solver = Solver::new();
        let int_obj1 = solver.new_int_var();
        let int_obj2 = solver.new_int_var();
        let sum = solver.sum(&[int_obj1.clone(), int_obj2.clone()]).unwrap();
        assert_eq!(solver.int_val(sum.as_any().downcast_ref::<ArithVar>().unwrap()), i_i(0));
    }

    #[test]
    fn test_basic_enum() {
        let solver = Solver::new();
        solver.read("enum Color { Red, Green, Blue }");
        let color_type = solver.get_type("Color").unwrap();
        assert_eq!(color_type.name(), "Color");

        let color_var = color_type.new_instance();
    }
}
