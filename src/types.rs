use riddle::{
    core::Core,
    env::{ObjectId, Slot},
    language::ConstructorDef,
    scope::{Class, CommonScope, Constructor, Field, Function, Predicate, Scope, Type},
};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

pub struct StateVariable {
    scope: Rc<CommonScope>,
    constructors: RefCell<Vec<Rc<Constructor>>>,
    instances: RefCell<Vec<ObjectId>>,
}

impl StateVariable {
    pub fn new(core: Weak<dyn Core>) -> Rc<Self> {
        let sv = Rc::new(Self {
            scope: Rc::new(CommonScope::new(core.clone(), Some(core))),
            constructors: RefCell::new(Vec::new()),
            instances: RefCell::new(Vec::new()),
        });
        sv.constructors.borrow_mut().push(Rc::new(Constructor::new(Rc::downgrade(&sv) as _, ConstructorDef { args: Vec::new(), init: Vec::new(), statements: Vec::new() })));
        sv
    }
}

impl Type for StateVariable {
    fn name(&self) -> &str {
        "StateVariable"
    }

    fn as_class(self: Rc<Self>) -> Option<Rc<dyn Class>> {
        Some(self)
    }

    fn new_instance(self: Rc<Self>) -> Slot {
        let instance = self.core().new_object(self.clone());
        self.instances.borrow_mut().push(instance);
        Slot::ObjectRef(instance)
    }
}

impl Scope for StateVariable {
    fn core(&self) -> Rc<dyn Core> {
        self.scope.core()
    }

    fn scope(&self) -> Option<Rc<dyn Scope>> {
        self.scope.scope()
    }

    fn as_class(self: Rc<Self>) -> Option<Rc<dyn Class>> {
        Some(self)
    }

    fn get_fields(&self) -> Vec<Rc<Field>> {
        self.scope.get_fields()
    }

    fn get_field(&self, name: &str) -> Option<Rc<Field>> {
        self.scope.get_field(name)
    }

    fn get_function(&self, name: &str, types: &[Rc<dyn Type>]) -> Option<Rc<Function>> {
        self.scope.get_function(name, types)
    }

    fn get_type(&self, name: &str) -> Option<Rc<dyn Type>> {
        self.scope.get_type(name)
    }

    fn get_predicate(&self, name: &str) -> Option<Rc<Predicate>> {
        self.scope.get_predicate(name)
    }
}

impl Class for StateVariable {
    fn parents(&self) -> &[Vec<String>] {
        &[]
    }

    fn constructors(&self) -> Vec<Rc<Constructor>> {
        self.constructors.borrow().clone()
    }

    fn constructor(&self, args: &[Rc<dyn Type>]) -> Option<Rc<Constructor>> {
        if args.is_empty() { Some(self.constructors.borrow()[0].clone()) } else { None }
    }

    fn predicates(&self) -> Vec<Rc<Predicate>> {
        Vec::new()
    }

    fn classes(&self) -> Vec<Rc<dyn Class>> {
        Vec::new()
    }

    fn instances(&self) -> Vec<ObjectId> {
        self.instances.borrow().clone()
    }

    fn add_instance(&self, instance: ObjectId) {
        self.instances.borrow_mut().push(instance);
    }
}
