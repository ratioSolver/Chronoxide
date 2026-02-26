use consensus::LBool;

use crate::riddle::{
    classes::{Bool, Class, Field},
    objects::BoolObject,
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
    ac: dynamic_ac::Engine,
    lin: linspire::Engine,
    fields: HashMap<String, Rc<Field>>,
    classes: RefCell<HashMap<String, Rc<dyn Class>>>,
}

impl Solver {
    pub fn new() -> Rc<Self> {
        let slv = Rc::new_cyclic(|weak_self| Solver {
            weak_self: weak_self.clone(),
            sat: RefCell::new(consensus::Engine::new()),
            ac: dynamic_ac::Engine::new(),
            lin: linspire::Engine::new(),
            fields: HashMap::new(),
            classes: RefCell::new(HashMap::new()),
        });
        let bool_class = Rc::new(Bool::new(Rc::downgrade(&slv)));
        slv.add_class(bool_class);
        slv
    }

    pub fn add_class(&self, class: Rc<dyn Class>) {
        self.classes.borrow_mut().insert(class.name().to_string(), class);
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
}
