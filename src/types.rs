use crate::{
    SolverState,
    graph::{Flaw, FlawId},
    objects::{ArithVar, EnumVar},
};
use riddle::{
    core::Core,
    env::{AtomId, Env, ObjectId, Slot},
    language::ConstructorDef,
    scope::{Class, CommonScope, Constructor, Field, Function, Predicate, Scope, Type},
};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::{Rc, Weak},
};

pub trait FlawExtractor {
    fn extract_flaws(&self, core: &SolverState) -> Vec<FlawId>;
}

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

impl FlawExtractor for StateVariable {
    fn extract_flaws(&self, core: &SolverState) -> Vec<FlawId> {
        let mut atoms_by_instance: HashMap<ObjectId, Vec<AtomId>> = HashMap::new();
        let mut processed_classes = HashSet::new();

        let smt = core.smt.borrow();
        for instance_id in self.instances.borrow().iter() {
            let Some(instance) = core.get_object(*instance_id) else {
                continue;
            };
            if !processed_classes.insert(instance.class().full_name().to_string()) {
                continue;
            }
            for pred in instance.class().predicates().iter() {
                for atom_id in pred.atoms().iter() {
                    let Some(sigma) = core.atom_sigma(*atom_id) else {
                        continue;
                    };
                    if smt.get_bool_val(&sigma) != Some(true) {
                        continue;
                    }
                    let Some(atom) = core.get_atom(*atom_id) else {
                        continue;
                    };
                    match atom.get("tau") {
                        Some(Slot::ObjectRef(sv)) => {
                            atoms_by_instance.entry(sv).or_default().push(atom.id());
                        }
                        Some(Slot::Primitive(var)) => {
                            if let Some(enum_var) = var.as_any().downcast_ref::<EnumVar>() {
                                if let Some(sv) = smt.get_enum_val(&enum_var.var) {
                                    atoms_by_instance.entry(ObjectId::from(sv as usize)).or_default().push(atom.id());
                                }
                            }
                        }
                        _ => unreachable!("Expected 'tau' to be an ObjectRef or Primitive EnumVar"),
                    }
                }
            }
        }

        for (_instance_id, atoms) in atoms_by_instance {
            for i in 0..atoms.len() {
                for j in (i + 1)..atoms.len() {
                    let atom_i = core.get_atom(atoms[i]).expect("Atom should exist");
                    let atom_j = core.get_atom(atoms[j]).expect("Atom should exist");
                    let ai_start = match atom_i.get("start") {
                        Some(Slot::Primitive(var_i)) => var_i.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have a 'start' field"),
                        _ => unreachable!("Atom should have a 'start' field"),
                    };
                    let ai_end = match atom_i.get("end") {
                        Some(Slot::Primitive(var_i)) => var_i.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'end' field"),
                        _ => unreachable!("Atom should have an 'end' field"),
                    };
                    let aj_start = match atom_j.get("start") {
                        Some(Slot::Primitive(var_j)) => var_j.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have a 'start' field"),
                        _ => unreachable!("Atom should have a 'start' field"),
                    };
                    let aj_end = match atom_j.get("end") {
                        Some(Slot::Primitive(var_j)) => var_j.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'end' field"),
                        _ => unreachable!("Atom should have an 'end' field"),
                    };
                    let ai_start_val = core.smt.borrow().get_arith_val(&ai_start).expect("Atom should have a 'start' field");
                    let ai_end_val = core.smt.borrow().get_arith_val(&ai_end).expect("Atom should have an 'end' field");
                    let aj_start_val = core.smt.borrow().get_arith_val(&aj_start).expect("Atom should have a 'start' field");
                    let aj_end_val = core.smt.borrow().get_arith_val(&aj_end).expect("Atom should have an 'end' field");
                    if (ai_start_val < aj_end_val) && (aj_start_val < ai_end_val) {}
                }
            }
        }

        let mut flaws = Vec::new();
        flaws
    }
}

struct Peak {
    object_id: ObjectId,
    atoms: Vec<AtomId>,
}
