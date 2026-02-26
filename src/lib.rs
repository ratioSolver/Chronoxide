use consensus::LBool;
use linspire::inf_rational::InfRational;

use crate::riddle::{
    classes::{Bool, Class, Field, Int},
    objects::{BoolObject, IntObject},
};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

mod riddle;

pub struct Solver {
    weak_self: Weak<Self>,
    sat: RefCell<consensus::Engine>,
    ac: RefCell<dynamic_ac::Engine>,
    lin: RefCell<linspire::Engine>,
    fields: HashMap<String, Rc<Field>>,
    classes: RefCell<HashMap<String, Rc<dyn Class>>>,
}

impl Solver {
    pub fn new() -> Rc<Self> {
        let slv = Rc::new_cyclic(|weak_self| Solver {
            weak_self: weak_self.clone(),
            sat: RefCell::new(consensus::Engine::new()),
            ac: RefCell::new(dynamic_ac::Engine::new()),
            lin: RefCell::new(linspire::Engine::new()),
            fields: HashMap::new(),
            classes: RefCell::new(HashMap::new()),
        });
        slv.add_class(Rc::new(Bool::new(slv.weak_self.clone())));
        slv.add_class(Rc::new(Int::new(slv.weak_self.clone())));
        slv
    }

    pub fn new_bool(&self) -> Rc<BoolObject> {
        let var = self.sat.borrow_mut().add_var();
        let classes = self.classes.borrow();
        let bool_class = classes.get("bool").expect("Bool class not found").clone();
        let bool_class = bool_class.as_any().downcast::<Bool>().expect("Failed to downcast to Bool class");
        Rc::new(BoolObject::new(Rc::downgrade(&bool_class), var))
    }

    pub fn bool_val(&self, obj: &BoolObject) -> LBool {
        self.sat.borrow().value(obj.var).clone()
    }

    pub fn new_int(&self) -> Rc<IntObject> {
        let var = self.lin.borrow_mut().add_var();
        let classes = self.classes.borrow();
        let int_class = classes.get("int").expect("Int class not found").clone();
        let int_class = int_class.as_any().downcast::<Int>().expect("Failed to downcast to Int class");
        Rc::new(IntObject::new(Rc::downgrade(&int_class), var))
    }

    pub fn int_val(&self, obj: &IntObject) -> InfRational {
        self.lin.borrow().val(obj.var).clone()
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

        assert_eq!(solver.bool_val(&bool_obj), LBool::Undef);
        assert_eq!(solver.int_val(&int_obj), i_i(0));
    }
}
