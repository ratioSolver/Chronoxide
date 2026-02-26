use crate::riddle::objects::{IntObject, Object, RealObject};
use crate::riddle::{
    classes::{Bool, Class, Field, Int, Real},
    objects::BoolObject,
};
use consensus::{LBool, pos};
use linspire::{
    inf_rational::InfRational,
    lin::{c, v},
};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

mod riddle;

pub enum RiddleError {
    TypeError(String),
}

pub struct Solver {
    weak_self: Weak<Self>,
    sat: RefCell<consensus::Engine>,
    ac: RefCell<dynamic_ac::Engine>,
    lin: RefCell<linspire::Engine>,
    fields: RefCell<HashMap<String, Rc<Field>>>,
    classes: RefCell<HashMap<String, Rc<dyn Class>>>,
}

impl Solver {
    pub fn new() -> Rc<Self> {
        let slv = Rc::new_cyclic(|weak_self| Solver {
            weak_self: weak_self.clone(),
            sat: RefCell::new(consensus::Engine::new()),
            ac: RefCell::new(dynamic_ac::Engine::new()),
            lin: RefCell::new(linspire::Engine::new()),
            fields: RefCell::new(HashMap::new()),
            classes: RefCell::new(HashMap::new()),
        });
        slv.add_class(Rc::new(Bool::new(slv.weak_self.clone())));
        slv.add_class(Rc::new(Int::new(slv.weak_self.clone())));
        slv.add_class(Rc::new(Real::new(slv.weak_self.clone())));
        slv
    }

    pub fn new_bool(&self) -> Rc<BoolObject> {
        let var = self.sat.borrow_mut().add_var();
        let classes = self.classes.borrow();
        let bool_class = classes.get("bool").expect("Bool class not found").clone();
        let bool_class = bool_class.as_any().downcast::<Bool>().expect("Failed to downcast to Bool class");
        Rc::new(BoolObject::new(Rc::downgrade(&bool_class), pos(var)))
    }

    pub fn bool_val(&self, obj: &BoolObject) -> LBool {
        self.sat.borrow().lit_value(&obj.lit).clone()
    }

    pub fn new_int(&self) -> Rc<IntObject> {
        let var = self.lin.borrow_mut().add_var();
        let classes = self.classes.borrow();
        let int_class = classes.get("int").expect("Int class not found").clone();
        let int_class = int_class.as_any().downcast::<Int>().expect("Failed to downcast to Int class");
        Rc::new(IntObject::new(Rc::downgrade(&int_class), v(var)))
    }

    pub fn int_val(&self, obj: &IntObject) -> InfRational {
        self.lin.borrow().lin_val(&obj.lin).clone()
    }

    pub fn new_real(&self) -> Rc<RealObject> {
        let var = self.lin.borrow_mut().add_var();
        let classes = self.classes.borrow();
        let real_class = classes.get("real").expect("Real class not found").clone();
        let real_class = real_class.as_any().downcast::<Real>().expect("Failed to downcast to Real class");
        Rc::new(RealObject::new(Rc::downgrade(&real_class), v(var)))
    }

    pub fn real_val(&self, obj: &RealObject) -> InfRational {
        self.lin.borrow().lin_val(&obj.lin).clone()
    }

    pub fn new_sum(&self, terms: Vec<Rc<dyn Object>>) -> Result<Rc<dyn Object>, RiddleError> {
        let class = self.arith_class(&terms)?;
        let lin = terms
            .iter()
            .map(|t| {
                if t.class().name() == "int" {
                    t.clone().as_any().downcast::<IntObject>().expect("Failed to downcast to Int object").lin.clone()
                } else if t.class().name() == "real" {
                    t.clone().as_any().downcast::<RealObject>().expect("Failed to downcast to Real object").lin.clone()
                } else {
                    panic!("Invalid term type in sum")
                }
            })
            .fold(c(0), |acc, lin| acc + lin);
        Ok(match class.name() {
            "int" => {
                let int_class = class.as_any().downcast::<Int>().expect("Failed to downcast to Int class");
                Rc::new(IntObject::new(Rc::downgrade(&int_class), lin))
            }
            "real" => {
                let real_class = class.as_any().downcast::<Real>().expect("Failed to downcast to Real class");
                Rc::new(RealObject::new(Rc::downgrade(&real_class), lin))
            }
            _ => unreachable!(),
        })
    }

    pub fn new_sub(&self, terms: Vec<Rc<dyn Object>>) -> Result<Rc<dyn Object>, RiddleError> {
        let class = self.arith_class(&terms)?;
        let lin: Vec<_> = terms
            .iter()
            .map(|t| {
                if t.class().name() == "int" {
                    t.clone().as_any().downcast::<IntObject>().expect("Failed to downcast to Int object").lin.clone()
                } else if t.class().name() == "real" {
                    t.clone().as_any().downcast::<RealObject>().expect("Failed to downcast to Real object").lin.clone()
                } else {
                    panic!("Invalid term type in subtraction")
                }
            })
            .collect();
        let (first, rest) = lin.split_first().expect("At least one term is required for subtraction");
        let lin = rest.iter().fold(first.clone(), |acc, lin| acc - lin);
        Ok(match class.name() {
            "int" => {
                let int_class = class.as_any().downcast::<Int>().expect("Failed to downcast to Int class");
                Rc::new(IntObject::new(Rc::downgrade(&int_class), lin))
            }
            "real" => {
                let real_class = class.as_any().downcast::<Real>().expect("Failed to downcast to Real class");
                Rc::new(RealObject::new(Rc::downgrade(&real_class), lin))
            }
            _ => unreachable!(),
        })
    }

    fn arith_class(&self, terms: &Vec<Rc<dyn Object>>) -> Result<Rc<dyn Class>, RiddleError> {
        let classes = self.classes.borrow();
        if terms.iter().all(|t| t.class().name() == "int") {
            let int_class = classes.get("int").expect("Int class not found").clone();
            Ok(int_class)
        } else if terms.iter().all(|t| t.class().name() == "real") {
            let real_class = classes.get("real").expect("Real class not found").clone();
            Ok(real_class)
        } else if terms.iter().all(|t| t.class().name() == "int" || t.class().name() == "real") {
            let real_class = classes.get("real").expect("Real class not found").clone();
            Ok(real_class)
        } else {
            Err(RiddleError::TypeError("Invalid term types in arithmetic operation".to_string()))
        }
    }

    pub fn add_class(&self, class: Rc<dyn Class>) {
        self.classes.borrow_mut().insert(class.name().to_string(), class);
    }
}

#[cfg(test)]
mod tests {
    use linspire::inf_rational::i_i;

    use super::*;

    #[test]
    fn test_solver() {
        let solver = Solver::new();
        let bool_obj = solver.new_bool();
        let int_obj = solver.new_int();
        let real_obj = solver.new_real();

        assert_eq!(solver.bool_val(&bool_obj), LBool::Undef);
        assert_eq!(solver.int_val(&int_obj), i_i(0));
        assert_eq!(solver.real_val(&real_obj), i_i(0));
    }
}
