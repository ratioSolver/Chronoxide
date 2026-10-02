use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
    inf_rat_to_json,
    objects::{ArithVar, EnumVar},
    timelines::Timeline,
};
use riddle::{
    core::Core,
    env::{AtomId, Env, ObjectId, Slot},
    language::{ClassDef, ConstructorDef, Expr, PredicateDef, Statement},
    scope::{Class, CommonScope, Constructor, Field, Function, Predicate, Scope, Type},
};
use semitone::{ast::ArithExpr, rational::InfRational};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    rc::{Rc, Weak},
};
use tracing::trace;

pub(crate) struct ReusableResource {
    scope: Rc<CommonScope>,
    constructors: RefCell<Vec<Rc<Constructor>>>,
    instances: RefCell<Vec<ObjectId>>,
}

impl ReusableResource {
    pub(crate) fn new(core: Weak<dyn Core>) -> Rc<Self> {
        let rr = Rc::new(Self {
            scope: CommonScope::from_class(
                core.clone(),
                ClassDef {
                    name: String::new(),
                    parents: Vec::new(),
                    fields: vec![(vec![String::from("real")], vec![(String::from("capacity"), None)])],
                    constructors: Vec::new(),
                    functions: Vec::new(),
                    predicates: vec![PredicateDef {
                        name: String::from("Use"),
                        args: vec![(vec![String::from("real")], String::from("amount"))],
                        parents: vec![vec![String::from("Interval")]],
                        statements: vec![
                            Statement::Expr(Expr::Eq {
                                left: Box::new(Expr::Sum {
                                    terms: vec![Expr::QualifiedId { ids: vec![String::from("end")] }, Expr::Opposite { term: Box::new(Expr::QualifiedId { ids: vec![String::from("start")] }) }],
                                }),
                                right: Box::new(Expr::QualifiedId { ids: vec![String::from("duration")] }),
                            }),
                            Statement::Expr(Expr::Gt {
                                left: Box::new(Expr::QualifiedId { ids: vec![String::from("amount")] }),
                                right: Box::new(Expr::Real(String::from("0"), String::from("1"))),
                            }),
                        ],
                    }],
                    classes: Vec::new(),
                },
            ),
            constructors: RefCell::new(Vec::new()),
            instances: RefCell::new(Vec::new()),
        });

        rr.constructors.borrow_mut().push(Rc::new(Constructor::new(
            Rc::downgrade(&rr) as _,
            ConstructorDef {
                args: vec![(vec![String::from("real")], String::from("capacity"))],
                init: vec![(vec![String::from("capacity")], vec![Expr::QualifiedId { ids: vec![String::from("capacity")] }])],
                statements: Vec::new(),
            },
        )));

        rr
    }

    fn atoms_by_instance(&self, slv: &SolverState) -> HashMap<ObjectId, Vec<AtomId>> {
        let mut atoms_by_instance: HashMap<ObjectId, Vec<AtomId>> = HashMap::new();
        let mut processed_classes = HashSet::new();

        let smt = slv.smt.borrow();
        let sigma = slv.sigma.borrow();
        for instance_id in self.instances.borrow().iter() {
            let Some(instance) = slv.get_object(*instance_id) else {
                continue;
            };
            if !processed_classes.insert(instance.class().full_name().to_string()) {
                continue;
            }
            for pred in instance.class().predicates().iter() {
                for atom_id in pred.atoms().iter() {
                    let Some(sigma) = sigma.get(**atom_id) else {
                        continue;
                    };
                    if smt.get_bool_val(sigma) != Some(true) {
                        continue;
                    }
                    let Some(atom) = slv.get_atom(*atom_id) else {
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

impl Type for ReusableResource {
    fn name(&self) -> &str {
        "ReusableResource"
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

impl Scope for ReusableResource {
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

impl Class for ReusableResource {
    fn parents(&self) -> &[Vec<String>] {
        &[]
    }

    fn constructors(&self) -> Vec<Rc<Constructor>> {
        self.constructors.borrow().clone()
    }

    fn constructor(&self, args: &[Rc<dyn Type>]) -> Option<Rc<Constructor>> {
        if args.len() == 1 && args[0].name() == "real" { Some(self.constructors.borrow()[0].clone()) } else { None }
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

impl Timeline for ReusableResource {
    fn extract_flaws(&self, slv: &SolverState) -> Result<Vec<Box<dyn Flaw>>, SolverError> {
        let mut flaws: Vec<Box<dyn Flaw>> = Vec::new();
        let atoms_by_instance = self.atoms_by_instance(slv);
        let mut reported_overlaps: HashSet<(AtomId, AtomId)> = HashSet::new();

        let graph = slv.graph.borrow();
        let smt = slv.smt.borrow();
        let atom_flaw = slv.atom_flaw.borrow();

        for instance_id in self.instances.borrow().iter() {
            if let Some(atoms) = atoms_by_instance.get(instance_id) {
                let capacity_var = match slv.get_object(*instance_id).expect("Instance should exist").get("capacity") {
                    Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Instance should have a 'capacity' field"),
                    _ => unreachable!("Instance should have a 'capacity' field"),
                };
                let capacity = smt.get_arith_val(&capacity_var).expect("Capacity should have a value");
                let mut starting_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
                let mut ending_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
                let mut pulses: BTreeSet<InfRational> = BTreeSet::new();

                for &atom_id in atoms {
                    let (start, end) = get_atom_vars(slv, atom_id);
                    let (start, end) = (smt.get_arith_val(&start).expect("Start time should have a value"), smt.get_arith_val(&end).expect("End time should have a value"));
                    starting_atoms.entry(start.clone()).or_default().push(atom_id);
                    ending_atoms.entry(end.clone()).or_default().push(atom_id);
                    pulses.insert(start);
                    pulses.insert(end);
                }

                let mut active_atoms: BTreeSet<AtomId> = BTreeSet::new();
                let mut amount = InfRational::zero();

                for pulse in pulses {
                    if let Some(ending) = ending_atoms.get(&pulse) {
                        for atom_id in ending {
                            let atom = slv.get_atom(*atom_id).expect("Atom should exist");
                            let amount_var = match atom.get("amount") {
                                Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
                                _ => unreachable!("Atom should have an 'amount' field"),
                            };
                            let atom_amount = smt.get_arith_val(&amount_var).expect("Amount should have a value");
                            amount -= atom_amount;
                            active_atoms.remove(atom_id);
                        }
                    }

                    if let Some(starting) = starting_atoms.get(&pulse) {
                        for atom_id in starting {
                            let atom = slv.get_atom(*atom_id).expect("Atom should exist");
                            let amount_var = match atom.get("amount") {
                                Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
                                _ => unreachable!("Atom should have an 'amount' field"),
                            };
                            let atom_amount = smt.get_arith_val(&amount_var).expect("Amount should have a value");
                            amount += atom_amount;
                            active_atoms.insert(*atom_id);
                        }
                    }

                    if amount > capacity {
                        let active_atoms_vec: Vec<AtomId> = active_atoms.iter().cloned().collect();
                        for i in 0..active_atoms_vec.len() {
                            for j in (i + 1)..active_atoms_vec.len() {
                                let a = active_atoms_vec[i];
                                let b = active_atoms_vec[j];
                                let pair = if a < b { (a, b) } else { (b, a) };
                                if reported_overlaps.insert(pair) {
                                    let mut causes = Vec::with_capacity(2);
                                    if let Some(flaw) = graph.flaw(*atom_flaw.get(*a).expect("Atom should have an associated flaw")) {
                                        causes.extend(flaw.causes())
                                    }
                                    if let Some(flaw) = graph.flaw(*atom_flaw.get(*b).expect("Atom should have an associated flaw")) {
                                        causes.extend(flaw.causes())
                                    }
                                    flaws.push(Box::new(Peak::new(causes, capacity_var.clone(), active_atoms.clone())));
                                    reported_overlaps.insert((a, b));
                                }
                            }
                        }
                    }
                }
            }
        }

        Ok(flaws)
    }

    fn to_json(&self, slv: &SolverState) -> Value {
        let atoms_by_instance = self.atoms_by_instance(slv);

        let smt = slv.smt.borrow();
        let mut json = json!({});

        for instance_id in self.instances.borrow().iter() {
            let capacity_var = match slv.get_object(*instance_id).expect("Instance should exist").get("capacity") {
                Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Instance should have a 'capacity' field"),
                _ => unreachable!("Instance should have a 'capacity' field"),
            };
            let capacity = smt.get_arith_val(&capacity_var).expect("Capacity should have a value");

            if let Some(atoms) = atoms_by_instance.get(instance_id) {
                let mut starting_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
                let mut ending_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
                let mut pulses: BTreeSet<InfRational> = BTreeSet::new();

                for &atom_id in atoms {
                    let (start, end) = get_atom_vars(slv, atom_id);
                    let (start, end) = (smt.get_arith_val(&start).expect("Start time should have a value"), smt.get_arith_val(&end).expect("End time should have a value"));
                    starting_atoms.entry(start.clone()).or_default().push(atom_id);
                    ending_atoms.entry(end.clone()).or_default().push(atom_id);
                    pulses.insert(start);
                    pulses.insert(end);
                }

                let mut intervals = Vec::new();
                let mut active_atoms: BTreeSet<AtomId> = BTreeSet::new();
                let mut last_pulse: Option<InfRational> = None;
                let mut amount = InfRational::zero();

                for pulse in pulses {
                    if let Some(prev_pulse) = last_pulse {
                        intervals.push(json!({
                            "start": inf_rat_to_json(&prev_pulse),
                            "end": inf_rat_to_json(&pulse),
                            "amount": inf_rat_to_json(&amount),
                            "atoms": active_atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
                        }));
                    }

                    if let Some(ending) = ending_atoms.get(&pulse) {
                        for atom_id in ending {
                            let atom = slv.get_atom(*atom_id).expect("Atom should exist");
                            let amount_var = match atom.get("amount") {
                                Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
                                _ => unreachable!("Atom should have an 'amount' field"),
                            };
                            let atom_amount = smt.get_arith_val(&amount_var).expect("Amount should have a value");
                            amount -= atom_amount;
                            active_atoms.remove(atom_id);
                        }
                    }

                    if let Some(starting) = starting_atoms.get(&pulse) {
                        for atom_id in starting {
                            let atom = slv.get_atom(*atom_id).expect("Atom should exist");
                            let amount_var = match atom.get("amount") {
                                Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
                                _ => unreachable!("Atom should have an 'amount' field"),
                            };
                            let atom_amount = smt.get_arith_val(&amount_var).expect("Amount should have a value");
                            amount += atom_amount;
                            active_atoms.insert(*atom_id);
                        }
                    }

                    last_pulse = Some(pulse);
                }

                json[instance_id.to_string()] = json!({
                    "type": "ReusableResource",
                    "capacity": inf_rat_to_json(&capacity),
                    "intervals": intervals,
                });
            } else {
                json[instance_id.to_string()] = json!({
                    "type": "ReusableResource",
                    "capacity": inf_rat_to_json(&capacity),
                    "intervals": [],
                });
            }
        }

        json
    }
}

fn get_atom_vars(slv: &SolverState, atom_id: AtomId) -> (ArithExpr, ArithExpr) {
    let atom = slv.get_atom(atom_id).expect("Atom should exist");
    let start = match atom.get("start") {
        Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have a 'start' field"),
        _ => unreachable!("Atom should have a 'start' field"),
    };
    let end = match atom.get("end") {
        Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'end' field"),
        _ => unreachable!("Atom should have an 'end' field"),
    };
    (start, end)
}

struct Peak {
    id: FlawId,

    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    capacity: ArithExpr,
    atoms: BTreeSet<AtomId>,
}

impl Peak {
    pub(crate) fn new(causes: Vec<ResolverId>, capacity: ArithExpr, atoms: BTreeSet<AtomId>) -> Self {
        Self { id: FlawId::default(), causes, resolvers: Vec::new(), capacity, atoms }
    }
}

impl Flaw for Peak {
    fn id(&self) -> FlawId {
        self.id
    }
    fn set_id(&mut self, id: FlawId) {
        self.id = id;
    }
    fn causes(&self) -> &Vec<ResolverId> {
        &self.causes
    }

    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        trace!("Expanding Peak flaw {} with atoms {}", self.id, self.atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", "));
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();

        let atoms_vec: Vec<AtomId> = self.atoms.iter().copied().collect();
        for i in 0..atoms_vec.len() {
            for j in (i + 1)..atoms_vec.len() {
                let a = atoms_vec[i];
                let b = atoms_vec[j];

                let (a_tau, b_tau) = {
                    let a_atom = slv.get_atom(a).ok_or(SolverError::RuntimeError(format!("Atom {} not found", a)))?;
                    let b_atom = slv.get_atom(b).ok_or(SolverError::RuntimeError(format!("Atom {} not found", b)))?;
                    (a_atom.get("tau").expect("Atom should have a 'tau' field"), b_atom.get("tau").expect("Atom should have a 'tau' field"))
                };
                match (a_tau, b_tau) {
                    (Slot::Primitive(a_var), Slot::ObjectRef(b_sv)) => {
                        let a_var = a_var.as_any().downcast_ref::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let disp = slv.track_expr(&mut smt, &mut graph, !a_var.eq(*b_sv as i32))?;
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Displace::new(self.id)), disp)?);
                    }
                    (Slot::ObjectRef(a_sv), Slot::Primitive(b_var)) => {
                        let b_var = b_var.as_any().downcast_ref::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let disp = slv.track_expr(&mut smt, &mut graph, !b_var.eq(*a_sv as i32))?;
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Displace::new(self.id)), disp)?);
                    }
                    (Slot::Primitive(a_var), Slot::Primitive(b_var)) => {
                        let a_var = a_var.as_any().downcast_ref::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let b_var = b_var.as_any().downcast_ref::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let disp = slv.track_expr(&mut smt, &mut graph, !a_var.eq(b_var))?;
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Displace::new(self.id)), disp)?);
                    }
                    _ => {}
                }

                let (a_start, a_end) = get_atom_vars(slv, a);
                let (b_start, b_end) = get_atom_vars(slv, b);

                let a_before_b = slv.track_expr(&mut smt, &mut graph, a_end.le(b_start))?;
                if smt.get_lit_val(a_before_b) != Some(false) {
                    self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Order::new(self.id)), a_before_b)?);
                }
                let b_before_a = slv.track_expr(&mut smt, &mut graph, b_end.le(a_start))?;
                if smt.get_lit_val(b_before_a) != Some(false) {
                    self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Order::new(self.id)), b_before_a)?);
                }
            }
        }

        let amount = ArithExpr::Add(
            atoms_vec
                .iter()
                .map(|&atom_id| {
                    let atom = slv.get_atom(atom_id).expect("Atom should exist");
                    match atom.get("amount") {
                        Some(Slot::Primitive(var)) => var.as_any().downcast_ref::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
                        _ => unreachable!("Atom should have an 'amount' field"),
                    }
                })
                .collect::<Vec<_>>(),
        );
        let over_capacity = slv.track_expr(&mut smt, &mut graph, amount.le(self.capacity.clone()))?;
        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Compress::new(self.id)), over_capacity)?);

        Ok(())
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "peak",
            "atoms": self.atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
        })
    }
}

struct Order {
    id: ResolverId,
    flaw: FlawId,
}

impl Order {
    fn new(flaw: FlawId) -> Self {
        Self { id: ResolverId::default(), flaw }
    }
}

impl Resolver for Order {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "order"
        })
    }
}

struct Compress {
    id: ResolverId,
    flaw: FlawId,
}

impl Compress {
    fn new(flaw: FlawId) -> Self {
        Self { id: ResolverId::default(), flaw }
    }
}

impl Resolver for Compress {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "compress"
        })
    }
}

struct Displace {
    id: ResolverId,
    flaw: FlawId,
}

impl Displace {
    fn new(flaw: FlawId) -> Self {
        Self { id: ResolverId::default(), flaw }
    }
}

impl Resolver for Displace {
    fn id(&self) -> ResolverId {
        self.id
    }
    fn set_id(&mut self, id: ResolverId) {
        self.id = id;
    }
    fn flaw(&self) -> FlawId {
        self.flaw
    }

    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "displace"
        })
    }
}
