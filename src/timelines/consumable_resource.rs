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
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    rc::{Rc, Weak},
};
use tracing::trace;

use crate::{
    SolverError, SolverState,
    graph::{Flaw, FlawId, Resolver, ResolverId},
    inf_rat_to_json,
    objects::{ArithVar, EnumVar},
    timelines::{Timeline, get_atom_amount, get_atom_vars},
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
                    fields: vec![(vec![String::from("real")], vec![(String::from("capacity"), None), (String::from("initial_amount"), None)])],
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
        let (atoms_by_instance, producers) = self.atoms_by_instance(slv);
        let mut reported: HashSet<(Kind, BTreeSet<AtomId>)> = HashSet::new();

        let graph = slv.graph.borrow();
        let smt = slv.smt.borrow();
        let atom_flaw = slv.atom_flaw.borrow();

        for instance_id in self.instances.borrow().iter() {
            let Some(atoms) = atoms_by_instance.get(instance_id) else {
                continue;
            };
            let obj = slv.get_object(*instance_id).expect("Instance should exist");
            let capacity_var = match obj.get("capacity") {
                Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Instance should have a 'capacity' field"),
                _ => unreachable!("Instance should have a 'capacity' field"),
            };
            let capacity = smt.get_arith_val(&capacity_var).expect("Capacity should have a value");
            let initial_amount_var = match obj.get("initial_amount") {
                Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Instance should have an 'initial_amount' field"),
                _ => unreachable!("Instance should have an 'initial_amount' field"),
            };
            let initial_amount = smt.get_arith_val(&initial_amount_var).expect("Initial amount should have a value");

            let mut starting_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut ending_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut pulses: BTreeMap<InfRational, ArithExpr> = BTreeMap::new();
            let mut amounts: HashMap<AtomId, InfRational> = HashMap::new();
            let mut durations: HashMap<AtomId, InfRational> = HashMap::new();
            let mut ends: HashMap<AtomId, InfRational> = HashMap::new();

            for &atom_id in atoms {
                let (start_expr, end_expr) = get_atom_vars(slv, atom_id);
                let start = smt.get_arith_val(&start_expr).expect("Start time should have a value");
                let end = smt.get_arith_val(&end_expr).expect("End time should have a value");
                amounts.insert(atom_id, smt.get_arith_val(&get_atom_amount(slv, atom_id)).expect("Amount should have a value"));
                durations.insert(atom_id, end.clone() - start.clone());
                ends.insert(atom_id, end.clone());
                starting_atoms.entry(start.clone()).or_default().push(atom_id);
                ending_atoms.entry(end.clone()).or_default().push(atom_id);
                pulses.entry(start).or_insert(start_expr);
                pulses.entry(end).or_insert(end_expr);
            }

            let mut started: BTreeSet<AtomId> = BTreeSet::new();
            let mut active: BTreeSet<AtomId> = BTreeSet::new();
            let mut level = initial_amount;
            let mut last_pulse: Option<&InfRational> = None;

            for (pulse, pulse_expr) in &pulses {
                if let Some(prev) = last_pulse {
                    let span = pulse.clone() - prev.clone();
                    for atom_id in &active {
                        let delta = flow_delta(&amounts[atom_id], &span, &durations[atom_id]);
                        if producers.contains(atom_id) {
                            level += delta;
                        } else {
                            level -= delta;
                        }
                    }

                    let kind = if level > capacity {
                        Some(Kind::Overflow)
                    } else if level < InfRational::zero() {
                        Some(Kind::Underflow)
                    } else {
                        None
                    };

                    if let Some(kind) = kind {
                        let culprit_is_producer = kind == Kind::Overflow;
                        let past: BTreeSet<AtomId> = started.iter().copied().filter(|a| producers.contains(a) == culprit_is_producer).collect();
                        if !past.is_empty() && reported.insert((kind, past.clone())) {
                            let future: Vec<AtomId> = atoms.iter().copied().filter(|a| producers.contains(a) != culprit_is_producer && ends[a] > *pulse).collect();
                            let mut causes = Vec::new();
                            for &atom_id in &past {
                                if let Some(flaw) = graph.flaw(*atom_flaw.get(*atom_id).expect("Atom should have an associated flaw")) {
                                    causes.extend(flaw.causes());
                                }
                            }
                            flaws.push(Box::new(LevelFlaw::new(kind, causes, *instance_id, pulse_expr.clone(), past, future)));
                        }
                    }
                }

                if let Some(ending) = ending_atoms.get(pulse) {
                    for atom_id in ending {
                        active.remove(atom_id);
                    }
                }
                if let Some(starting) = starting_atoms.get(pulse) {
                    started.extend(starting.iter().copied());
                    active.extend(starting.iter().copied());
                }

                last_pulse = Some(pulse);
            }
        }

        Ok(flaws)
    }

    fn to_json(&self, slv: &SolverState) -> Value {
        let (atoms_by_instance, producers) = self.atoms_by_instance(slv);
        let smt = slv.smt.borrow();
        let mut json = json!({});

        for instance_id in self.instances.borrow().iter() {
            let obj = slv.get_object(*instance_id).expect("Instance should exist");
            let capacity_var = match obj.get("capacity") {
                Some(Slot::Primitive(var)) => var.downcast::<ArithVar>().map(|v| v.lin.clone()).expect("Instance should have a 'capacity' field"),
                _ => unreachable!("Instance should have a 'capacity' field"),
            };
            let capacity = smt.get_arith_val(&capacity_var).expect("Capacity should have a value");
            let initial_amount_var = match obj.get("initial_amount") {
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
                    active_atoms.extend(starting.iter().copied());
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

fn flow_delta(amount: &InfRational, span: &InfRational, duration: &InfRational) -> InfRational {
    let ratio = if duration.rational_part().is_zero() {
        span.infinitesimal_part().clone() / duration.infinitesimal_part()
    } else {
        match span.rational_part() / duration.rational_part() {
            Rational::Finite(r) => r,
            other => panic!("flow ratio must be finite, got {other}"),
        }
    };
    amount * &ratio
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Kind {
    Overflow,
    Underflow,
}

impl Kind {
    fn as_str(self) -> &'static str {
        match self {
            Kind::Overflow => "overflow",
            Kind::Underflow => "underflow",
        }
    }
}

struct LevelFlaw {
    id: FlawId,

    kind: Kind,
    causes: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,

    instance: ObjectId,
    at: ArithExpr,
    atoms: BTreeSet<AtomId>,
    future: Vec<AtomId>,
}

impl LevelFlaw {
    fn new(kind: Kind, causes: Vec<ResolverId>, instance: ObjectId, at: ArithExpr, atoms: BTreeSet<AtomId>, future: Vec<AtomId>) -> Self {
        Self { id: FlawId::default(), kind, causes, resolvers: Vec::new(), instance, at, atoms, future }
    }
}

impl Flaw for LevelFlaw {
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
        trace!("Expanding {} flaw {} with atoms {}", self.kind.as_str(), self.id, self.atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", "));
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();

        for &atom_id in &self.atoms {
            let tau = {
                let atom = slv.get_atom(atom_id).ok_or(SolverError::RuntimeError(format!("Atom {} not found", atom_id)))?;
                atom.get("tau").expect("Atom should have a 'tau' field")
            };
            if let Slot::Primitive(var) = tau {
                let var = var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                let displace = slv.track_expr(&mut smt, &mut graph, !var.eq(*self.instance as i32))?;
                if smt.get_lit_val_and_level(displace) != Some((false, 0)) {
                    self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Displace::new(self.id)), displace)?);
                }
            }
        }

        for &atom_id in &self.future {
            let (_, end) = get_atom_vars(slv, atom_id);
            let anticipate = slv.track_expr(&mut smt, &mut graph, end.le(self.at.clone()))?;
            if smt.get_lit_val_and_level(anticipate) != Some((false, 0)) {
                self.resolvers.push(slv.add_resolver(&mut smt, &mut graph, Box::new(Anticipate::new(self.id)), anticipate)?);
            }
        }

        Ok(())
    }

    fn resolvers(&self) -> Vec<ResolverId> {
        self.resolvers.clone()
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": self.kind.as_str(),
            "atoms": self.atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
            "future": self.future.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
        })
    }
}

struct Anticipate {
    id: ResolverId,
    flaw: FlawId,
}

impl Anticipate {
    fn new(flaw: FlawId) -> Self {
        Self { id: ResolverId::default(), flaw }
    }
}

impl Resolver for Anticipate {
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
            "kind": "anticipate"
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
