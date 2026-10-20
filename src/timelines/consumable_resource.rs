use riddle::{
    core::Core,
    env::{AtomId, Env, ObjectId, Slot},
    language::{ClassDef, ConstructorDef, Expr, PredicateDef, Statement},
    scope::{Class, CommonScope, Constructor, Field, Function, Predicate, Scope, Type},
};
use semitone::{
    ast::ArithExpr,
    rational::{InfRational, Rational},
};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    rc::{Rc, Weak},
};
use tracing::trace;

use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
    inf_rat_to_json,
    objects::{ArithVar, EnumVar},
    timelines::Timeline,
};

pub(crate) struct ConsumableResource {
    scope: Rc<CommonScope>,
    constructors: RefCell<Vec<Rc<Constructor>>>,
    instances: RefCell<Vec<ObjectId>>,
}

impl ConsumableResource {
    pub(crate) fn new(core: Weak<dyn Core>) -> Rc<Self> {
        let cr = Rc::new(Self {
            scope: CommonScope::from_class(
                core.clone(),
                ClassDef {
                    name: String::new(),
                    parents: Vec::new(),
                    fields: vec![(vec![String::from("real")], vec![(String::from("capacity"), None)])],
                    constructors: Vec::new(),
                    functions: Vec::new(),
                    predicates: vec![
                        PredicateDef {
                            name: String::from("Produce"),
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
                        },
                        PredicateDef {
                            name: String::from("Consume"),
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
                        },
                    ],
                    classes: Vec::new(),
                },
            ),
            constructors: RefCell::new(Vec::new()),
            instances: RefCell::new(Vec::new()),
        });

        cr.constructors.borrow_mut().push(Rc::new(Constructor::new(
            Rc::downgrade(&cr) as _,
            ConstructorDef {
                args: vec![(vec![String::from("real")], String::from("capacity")), (vec![String::from("real")], String::from("initial_amount"))],
                init: vec![(vec![String::from("capacity")], vec![Expr::QualifiedId { ids: vec![String::from("capacity")] }]), (vec![String::from("initial_amount")], vec![Expr::QualifiedId { ids: vec![String::from("initial_amount")] }])],
                statements: Vec::new(),
            },
        )));

        cr
    }

    fn atoms_by_instance(&self, slv: &SolverState) -> (HashMap<ObjectId, Vec<AtomId>>, HashSet<AtomId>) {
        let mut atoms_by_instance: HashMap<ObjectId, Vec<AtomId>> = HashMap::new();
        let mut producers: HashSet<AtomId> = HashSet::new();
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
                let is_producer = pred.name() == "Produce";
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
                    if is_producer {
                        producers.insert(atom.id());
                    }
                    match atom.get("tau") {
                        Some(Slot::ObjectRef(sv)) => {
                            atoms_by_instance.entry(sv).or_default().push(atom.id());
                        }
                        Some(Slot::Primitive(var)) => {
                            if let Some(enum_var) = var.downcast::<EnumVar>()
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

        (atoms_by_instance, producers)
    }
}

impl Type for ConsumableResource {
    fn name(&self) -> &str {
        "ConsumableResource"
    }

    fn into_class(self: Rc<Self>) -> Option<Rc<dyn Class>> {
        Some(self)
    }

    fn new_instance(self: Rc<Self>) -> Slot {
        Slot::ObjectRef(self.core().new_object(self.clone()))
    }
}

impl Scope for ConsumableResource {
    fn core(&self) -> Rc<dyn Core> {
        self.scope.core()
    }

    fn scope(&self) -> Option<Rc<dyn Scope>> {
        self.scope.scope()
    }

    fn as_class(self: Rc<Self>) -> Option<Rc<dyn Class>> {
        Some(self)
    }

    fn fields(&self) -> Vec<Rc<Field>> {
        self.scope.fields()
    }

    fn get_field(&self, name: &str) -> Option<Rc<Field>> {
        self.scope.get_field(name)
    }

    fn functions(&self) -> Vec<Rc<Function>> {
        self.scope.functions()
    }

    fn get_function(&self, name: &str, types: &[Rc<dyn Type>]) -> Option<Rc<Function>> {
        self.scope.get_function(name, types)
    }

    fn types(&self) -> Vec<Rc<dyn Type>> {
        self.scope.types()
    }

    fn get_type(&self, name: &str) -> Option<Rc<dyn Type>> {
        self.scope.get_type(name)
    }

    fn predicates(&self) -> Vec<Rc<Predicate>> {
        self.scope.predicates()
    }

    fn get_predicate(&self, name: &str) -> Option<Rc<Predicate>> {
        self.scope.get_predicate(name)
    }
}

impl Class for ConsumableResource {
    fn parents(&self) -> &[Vec<String>] {
        &[]
    }

    fn constructors(&self) -> Vec<Rc<Constructor>> {
        self.constructors.borrow().clone()
    }

    fn constructor(&self, args: &[Rc<dyn Type>]) -> Option<Rc<Constructor>> {
        if args.len() == 2 && args.iter().all(|a| a.name() == "real") { Some(self.constructors.borrow()[0].clone()) } else { None }
    }

    fn instances(&self) -> Vec<ObjectId> {
        self.instances.borrow().clone()
    }

    fn add_instance(&self, instance: ObjectId) {
        self.instances.borrow_mut().push(instance);
    }
}

impl Timeline for ConsumableResource {
    fn extract_flaws(&self, slv: &SolverState) -> Result<Vec<Box<dyn Flaw>>, SolverError> {
        let mut flaws: Vec<Box<dyn Flaw>> = Vec::new();
        let (atoms_by_instance, _producers) = self.atoms_by_instance(slv);
        let mut reported: HashSet<BTreeSet<AtomId>> = HashSet::new();

        let graph = slv.graph.borrow();
        let smt = slv.smt.borrow();
        let atom_flaw = slv.atom_flaw.borrow();

        for instance_id in self.instances.borrow().iter() {
            let Some(atoms) = atoms_by_instance.get(instance_id) else {
                continue;
            };
            let capacity_var = match slv.get_object(*instance_id).expect("Instance should exist").get("capacity") {
                Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Instance should have a 'capacity' field"),
                _ => unreachable!("Instance should have a 'capacity' field"),
            };
            let capacity = smt.get_arith_val(&capacity_var).expect("Capacity should have a value");

            let mut starting_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut ending_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut pulses: BTreeSet<InfRational> = BTreeSet::new();
            let mut amounts: HashMap<AtomId, InfRational> = HashMap::new();

            for &atom_id in atoms {
                let (start, end) = get_atom_vars(slv, atom_id);
                let (start, end) = (smt.get_arith_val(&start).expect("Start time should have a value"), smt.get_arith_val(&end).expect("End time should have a value"));
                let amount = smt.get_arith_val(&get_atom_amount(slv, atom_id)).expect("Amount should have a value");
                amounts.insert(atom_id, amount);
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
                        amount -= amounts[atom_id].clone();
                        active_atoms.remove(atom_id);
                    }
                }
                if let Some(starting) = starting_atoms.get(&pulse) {
                    for atom_id in starting {
                        amount += amounts[atom_id].clone();
                        active_atoms.insert(*atom_id);
                    }
                }

                if amount > capacity {
                    for conflict in minimal_conflicts(&active_atoms, &amounts, &capacity) {
                        if !reported.insert(conflict.clone()) {
                            continue;
                        }
                        let mut causes = Vec::new();
                        for &atom_id in &conflict {
                            if let Some(flaw) = graph.flaw(*atom_flaw.get(*atom_id).expect("Atom should have an associated flaw")) {
                                causes.extend(flaw.causes());
                            }
                        }
                        flaws.push(Box::new(Peak::new(causes, capacity_var.clone(), conflict)));
                    }
                }
            }
        }

        Ok(flaws)
    }

    fn to_json(&self, slv: &SolverState) -> Value {
        let (atoms_by_instance, producers) = self.atoms_by_instance(slv);
        let smt = slv.smt.borrow();
        let mut json = json!({});

        for instance_id in self.instances.borrow().iter() {
            let capacity_var = match slv.get_object(*instance_id).expect("Instance should exist").get("capacity") {
                Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Instance should have a 'capacity' field"),
                _ => unreachable!("Instance should have a 'capacity' field"),
            };
            let capacity = smt.get_arith_val(&capacity_var).expect("Capacity should have a value");
            let initial_amount_var = match slv.get_object(*instance_id).expect("Instance should exist").get("initial_amount") {
                Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Instance should have an 'initial_amount' field"),
                _ => unreachable!("Instance should have an 'initial_amount' field"),
            };
            let initial_amount = smt.get_arith_val(&initial_amount_var).expect("Initial amount should have a value");

            let atoms = atoms_by_instance.get(instance_id).map(Vec::as_slice).unwrap_or(&[]);

            let mut starting_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut ending_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut pulses: BTreeSet<InfRational> = BTreeSet::new();
            let mut amounts: HashMap<AtomId, InfRational> = HashMap::new();
            let mut durations: HashMap<AtomId, InfRational> = HashMap::new();

            for &atom_id in atoms {
                let (start, end) = get_atom_vars(slv, atom_id);
                let (start, end) = (smt.get_arith_val(&start).expect("Start time should have a value"), smt.get_arith_val(&end).expect("End time should have a value"));
                amounts.insert(atom_id, smt.get_arith_val(&get_atom_amount(slv, atom_id)).expect("Amount should have a value"));
                durations.insert(atom_id, end.clone() - start.clone());
                starting_atoms.entry(start.clone()).or_default().push(atom_id);
                ending_atoms.entry(end.clone()).or_default().push(atom_id);
                pulses.insert(start);
                pulses.insert(end);
            }

            let mut intervals = Vec::new();
            let mut active_atoms: BTreeSet<AtomId> = BTreeSet::new();
            let mut last_pulse: Option<InfRational> = None;
            let mut level = initial_amount.clone();

            for pulse in pulses {
                if let Some(prev_pulse) = &last_pulse {
                    let span = pulse.clone() - prev_pulse.clone();
                    let mut final_amount = level.clone();
                    for atom_id in &active_atoms {
                        let delta = flow_delta(&amounts[atom_id], &span, &durations[atom_id]);
                        if producers.contains(atom_id) {
                            final_amount += delta;
                        } else {
                            final_amount -= delta;
                        }
                    }
                    intervals.push(json!({
                        "start": inf_rat_to_json(prev_pulse),
                        "end": inf_rat_to_json(&pulse),
                        "initial_amount": inf_rat_to_json(&level),
                        "final_amount": inf_rat_to_json(&final_amount),
                        "atoms": active_atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
                    }));
                    level = final_amount;
                }

                if let Some(ending) = ending_atoms.get(&pulse) {
                    for atom_id in ending {
                        active_atoms.remove(atom_id);
                    }
                }
                if let Some(starting) = starting_atoms.get(&pulse) {
                    for atom_id in starting {
                        if durations[atom_id].rational_part().is_zero() {
                            if producers.contains(atom_id) {
                                level += amounts[atom_id].clone();
                            } else {
                                level -= amounts[atom_id].clone();
                            }
                        } else {
                            active_atoms.insert(*atom_id);
                        }
                    }
                }

                last_pulse = Some(pulse);
            }

            json[instance_id.to_string()] = json!({
                "type": "ConsumableResource",
                "capacity": inf_rat_to_json(&capacity),
                "initial_amount": inf_rat_to_json(&initial_amount),
                "intervals": intervals,
            });
        }

        json
    }
}

fn minimal_conflicts(active: &BTreeSet<AtomId>, amounts: &HashMap<AtomId, InfRational>, capacity: &InfRational) -> Vec<BTreeSet<AtomId>> {
    let mut sorted: Vec<AtomId> = active.iter().copied().collect();
    sorted.sort_by(|a, b| amounts[b].cmp(&amounts[a]).then(a.cmp(b)));

    let mut conflicts = Vec::new();
    let mut window: VecDeque<AtomId> = VecDeque::new();
    let mut sum = InfRational::zero();

    for atom_id in sorted {
        sum += amounts[&atom_id].clone();
        window.push_back(atom_id);

        if sum > *capacity {
            conflicts.push(window.iter().copied().collect());
            let largest = window.pop_front().expect("Window should not be empty");
            sum -= amounts[&largest].clone();
        }
    }

    conflicts
}

fn get_atom_amount(slv: &SolverState, atom_id: AtomId) -> ArithExpr {
    let atom = slv.get_atom(atom_id).expect("Atom should exist");
    match atom.get("amount") {
        Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
        _ => unreachable!("Atom should have an 'amount' field"),
    }
}

fn get_atom_vars(slv: &SolverState, atom_id: AtomId) -> (ArithExpr, ArithExpr) {
    let atom = slv.get_atom(atom_id).expect("Atom should exist");
    let start = match atom.get("start") {
        Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have a 'start' field"),
        _ => unreachable!("Atom should have a 'start' field"),
    };
    let end = match atom.get("end") {
        Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'end' field"),
        _ => unreachable!("Atom should have an 'end' field"),
    };
    (start, end)
}

fn flow_delta(amount: &InfRational, span: &InfRational, duration: &InfRational) -> InfRational {
    let ratio = match span.rational_part() / duration.rational_part() {
        Rational::Finite(r) => r,
        other => panic!("flow ratio must be finite, got {other}"),
    };
    amount * &ratio
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
                        let a_var = a_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let disp = slv.track_expr(&mut smt, &mut graph, !a_var.eq(*b_sv as i32))?;
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Displace::new(self.id)), disp)?);
                    }
                    (Slot::ObjectRef(a_sv), Slot::Primitive(b_var)) => {
                        let b_var = b_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let disp = slv.track_expr(&mut smt, &mut graph, !b_var.eq(*a_sv as i32))?;
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Displace::new(self.id)), disp)?);
                    }
                    (Slot::Primitive(a_var), Slot::Primitive(b_var)) => {
                        let a_var = a_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let b_var = b_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let disp = slv.track_expr(&mut smt, &mut graph, !a_var.eq(b_var))?;
                        self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Displace::new(self.id)), disp)?);
                    }
                    _ => {}
                }

                let (a_start, a_end) = get_atom_vars(slv, a);
                let (b_start, b_end) = get_atom_vars(slv, b);

                let a_before_b = slv.track_expr(&mut smt, &mut graph, a_end.le(b_start))?;
                if smt.get_lit_val_and_level(a_before_b) != Some((false, 0)) {
                    self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Order::new(self.id)), a_before_b)?);
                }
                let b_before_a = slv.track_expr(&mut smt, &mut graph, b_end.le(a_start))?;
                if smt.get_lit_val_and_level(b_before_a) != Some((false, 0)) {
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
                        Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Atom should have an 'amount' field"),
                        _ => unreachable!("Atom should have an 'amount' field"),
                    }
                })
                .collect::<Vec<_>>(),
        );
        let over_capacity = slv.track_expr(&mut smt, &mut graph, amount.le(self.capacity.clone()))?;
        if smt.get_lit_val_and_level(over_capacity) != Some((false, 0)) {
            self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Compress::new(self.id)), over_capacity)?);
        }

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
