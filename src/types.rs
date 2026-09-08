use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
    objects::{ArithVar, EnumVar},
};
use riddle::{
    core::Core,
    env::{Atom, AtomId, Env, ObjectId, Slot},
    language::ConstructorDef,
    scope::{Class, CommonScope, Constructor, Field, Function, Predicate, Scope, Type},
};
use semitone::{Lit, rational::InfRational};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    cmp::{max, min},
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    rc::{Rc, Weak},
};

pub trait FlawExtractor {
    fn extract_flaws(&self, core: &SolverState) -> Vec<FlawId>;

    fn to_json(&self, core: &SolverState) -> Value;
}

pub struct StateVariable {
    scope: Rc<CommonScope>,
    constructors: RefCell<Vec<Rc<Constructor>>>,
    instances: RefCell<Vec<ObjectId>>,
    active_overlaps: RefCell<HashMap<(AtomId, AtomId), FlawId>>,
}

impl StateVariable {
    pub fn new(core: Weak<dyn Core>) -> Rc<Self> {
        let sv = Rc::new(Self {
            scope: Rc::new(CommonScope::new(core.clone(), Some(core))),
            constructors: RefCell::new(Vec::new()),
            instances: RefCell::new(Vec::new()),
            active_overlaps: RefCell::new(HashMap::new()),
        });
        sv.constructors.borrow_mut().push(Rc::new(Constructor::new(Rc::downgrade(&sv) as _, ConstructorDef { args: Vec::new(), init: Vec::new(), statements: Vec::new() })));
        sv
    }

    fn atoms_by_instance(&self, core: &SolverState) -> HashMap<ObjectId, Vec<AtomId>> {
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
                            if let Some(enum_var) = var.as_any().downcast_ref::<EnumVar>()
                                && let Some(sv) = smt.get_enum_val(&enum_var.var)
                            {
                                atoms_by_instance.entry(ObjectId::from(sv as usize)).or_default().push(atom.id());
                            }
                        }
                        _ => unreachable!("Atom should have a 'tau' field"),
                    }
                }
            }
        }

        atoms_by_instance
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
        let atoms_by_instance = self.atoms_by_instance(core);

        let mut pending_overlaps = Vec::new();
        for (_instance_id, atoms) in atoms_by_instance {
            for i in 0..atoms.len() {
                let (ai_start, ai_end) = get_atom_times(core, atoms[i]);

                for j in (i + 1)..atoms.len() {
                    let (aj_start, aj_end) = get_atom_times(core, atoms[j]);

                    if (ai_start < aj_end) && (aj_start < ai_end) {
                        let a = min(atoms[i], atoms[j]);
                        let b = max(atoms[i], atoms[j]);
                        pending_overlaps.push((a, b));
                    }
                }
            }
        }

        let mut flaws = Vec::new();
        let mut active_overlaps = self.active_overlaps.borrow_mut();

        for (a, b) in pending_overlaps {
            if let Some(&flaw_id) = active_overlaps.get(&(a, b)) {
                flaws.push(flaw_id);
            } else {
                let mut state = core.planner_state.borrow_mut();
                let mut causes = Vec::new();

                let a_f = *state.graph.atom_to_flaw.get(&a).expect("Atom A missing flaw");
                let a_f = state.graph.get_flaw(a_f);
                if let Some(cause) = a_f.causes().first() {
                    causes.push(*cause);
                }

                let b_f = *state.graph.atom_to_flaw.get(&b).expect("Atom B missing flaw");
                let b_f = state.graph.get_flaw(b_f);
                if let Some(cause) = b_f.causes().first() {
                    causes.push(*cause);
                }

                let phi = core.smt.borrow_mut().new_lit();
                let flaw_id = state.graph.add_flaw(Box::new(Peak::new(phi, None, causes, vec![a, b])));

                active_overlaps.insert((a, b), flaw_id);
                flaws.push(flaw_id);
            }
        }

        flaws
    }

    fn to_json(&self, core: &SolverState) -> Value {
        let mut json = json!({});
        let atoms_by_instance = self.atoms_by_instance(core);

        for instance_id in self.instances.borrow().iter() {
            if let Some(atoms) = atoms_by_instance.get(instance_id) {
                let mut starting_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
                let mut ending_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
                let mut pulses: BTreeSet<InfRational> = BTreeSet::new();

                for &atom_id in atoms {
                    let (start, end) = get_atom_times(core, atom_id);

                    starting_atoms.entry(start.clone()).or_default().push(atom_id);
                    ending_atoms.entry(end.clone()).or_default().push(atom_id);

                    pulses.insert(start);
                    pulses.insert(end);
                }

                let mut intervals = Vec::new();
                let mut active_atoms: HashSet<AtomId> = HashSet::new();

                let pulses_vec: Vec<_> = pulses.into_iter().collect();

                for i in 0..pulses_vec.len().saturating_sub(1) {
                    let current_pulse = &pulses_vec[i];
                    let next_pulse = &pulses_vec[i + 1];

                    if let Some(ending) = ending_atoms.get(current_pulse) {
                        for atom_id in ending {
                            active_atoms.remove(atom_id);
                        }
                    }

                    if let Some(starting) = starting_atoms.get(current_pulse) {
                        for atom_id in starting {
                            active_atoms.insert(*atom_id);
                        }
                    }

                    intervals.push(json!({
                        "start": current_pulse.to_string(),
                        "end": next_pulse.to_string(),
                        "atoms": &active_atoms.iter().map(|atom_id| atom_id.to_string()).collect::<Vec<_>>(),
                    }));
                }

                json[instance_id.to_string()] = json!({
                    "type": "StateVariable",
                    "intervals": intervals,
                })
            } else {
                json[instance_id.to_string()] = json!({
                    "type": "StateVariable",
                    "intervals": [],
                })
            }
        }

        json
    }
}

fn get_atom_times(core: &SolverState, atom_id: AtomId) -> (InfRational, InfRational) {
    let atom = core.get_atom(atom_id).expect("Atom should exist");
    let smt = core.smt.borrow();

    let start_time = match atom.get("start") {
        Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have a 'start' field"),
        _ => unreachable!("Atom should have a 'start' field"),
    };
    let end_time = match atom.get("end") {
        Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'end' field"),
        _ => unreachable!("Atom should have an 'end' field"),
    };

    let start_val = smt.get_arith_val(&start_time).expect("Start time should have a value");
    let end_val = smt.get_arith_val(&end_time).expect("End time should have a value");

    (start_val, end_val)
}

struct Peak {
    id: FlawId,
    phi: Lit,
    status: Option<bool>,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    estimated_cost: f64,
    is_expanded: bool,

    atoms: Vec<AtomId>,
}

impl Peak {
    fn new(phi: Lit, status: Option<bool>, causes: Vec<ResolverId>, atoms: Vec<AtomId>) -> Self {
        Self {
            id: 0,
            phi,
            status,
            causes,
            resolvers: Vec::new(),
            estimated_cost: f64::INFINITY,
            is_expanded: false,
            atoms,
        }
    }
}

impl Flaw for Peak {
    fn id(&self) -> FlawId {
        self.id
    }
    fn set_id(&mut self, id: FlawId) {
        self.id = id;
    }

    fn phi(&self) -> Lit {
        self.phi
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn causes(&self) -> &[ResolverId] {
        &self.causes
    }

    fn is_expanded(&self) -> bool {
        self.is_expanded
    }
    fn expand(&mut self, core: &SolverState) -> Result<Vec<Box<dyn Resolver>>, SolverError> {
        self.is_expanded = true;

        let mut resolvers: Vec<Box<dyn Resolver>> = Vec::with_capacity(self.atoms.len() * (self.atoms.len() - 1) / 2);
        for i in 0..self.atoms.len() {
            for j in (i + 1)..self.atoms.len() {
                let atom_i = core.get_atom(self.atoms[i]).expect("Atom should exist");
                let atom_j = core.get_atom(self.atoms[j]).expect("Atom should exist");
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
                let ai_before_aj = core.smt.borrow_mut().track_expr(ai_end.lt(&aj_start));
                let ai_before_aj_status = core.smt.borrow().get_lit_val(ai_before_aj);
                if ai_before_aj_status != Some(false) {
                    resolvers.push(Box::new(Order::new(self.id, self.atoms[i], self.atoms[j], ai_before_aj, ai_before_aj_status)));
                }
                let aj_before_ai = core.smt.borrow_mut().track_expr(aj_end.lt(&ai_start));
                let aj_before_ai_status = core.smt.borrow().get_lit_val(aj_before_ai);
                if aj_before_ai_status != Some(false) {
                    resolvers.push(Box::new(Order::new(self.id, self.atoms[j], self.atoms[i], aj_before_ai, aj_before_ai_status)));
                }
            }
        }

        Ok(resolvers)
    }

    fn resolvers(&self) -> &[ResolverId] {
        &self.resolvers
    }
    fn add_resolver(&mut self, id: ResolverId) {
        self.resolvers.push(id);
    }

    fn estimated_cost(&self) -> f64 {
        self.estimated_cost
    }
    fn set_estimated_cost(&mut self, cost: f64) {
        self.estimated_cost = cost;
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "peak",
        })
    }
}

struct Order {
    id: ResolverId,
    flaw: FlawId,
    atm0: AtomId,
    atm1: AtomId,
    rho: Lit,
    status: Option<bool>,
}

impl Order {
    fn new(flaw: FlawId, atm0: AtomId, atm1: AtomId, rho: Lit, status: Option<bool>) -> Self {
        assert!(status != Some(false), "Cannot create an Order with status Some(false)");
        Self { id: 0, flaw, atm0, atm1, rho, status }
    }
}

impl Resolver for Order {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }

    fn rho(&self) -> Lit {
        self.rho
    }
    fn status(&self) -> Option<bool> {
        self.status
    }
    fn set_status(&mut self, status: Option<bool>) {
        self.status = status;
    }

    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn intrinsic_cost(&self) -> f64 {
        1f64
    }

    fn sub_flaws(&self) -> &[FlawId] {
        &[]
    }

    fn apply(&mut self, _state: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "order",
            "atm0": *self.atm0,
            "atm1": *self.atm1,
        })
    }
}
