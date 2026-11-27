use crate::{
    SolverError, SolverState,
    flaws::{LitResolver, add_lit_candidates},
    graph::{Flaw, FlawId},
    inf_rat_to_json,
    objects::{ArithVar, EnumVar},
    timelines::{FlawWithCauses, Timeline, get_amount, get_interval_vars, get_tau},
};
use riddle::{
    core::Core,
    env::{AtomId, Env, ObjectId, Slot},
    language::{ClassDef, ConstructorDef, Expr, PredicateDef, Statement},
    scope::{Class, CommonScope, Constructor, Field, Function, Predicate, Scope, Type},
};
use semitone::{
    Lit,
    ast::ArithExpr,
    rational::{InfRational, Rational},
};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt, iter,
    rc::{Rc, Weak},
};
use tracing::trace;

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
                            invariant: true,
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
                            invariant: true,
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

    fn atoms_by_instance(&self, slv: &SolverState) -> HashMap<ObjectId, (BTreeSet<AtomId>, BTreeSet<AtomId>)> {
        let mut atoms_by_instance: HashMap<ObjectId, (BTreeSet<AtomId>, BTreeSet<AtomId>)> = HashMap::new();
        let mut processed_classes = HashSet::new();

        let smt = slv.smt.borrow();
        let atom_sigma = slv.atom_sigma.borrow();
        for instance_id in self.instances.borrow().iter() {
            let Some(instance) = slv.get_object(*instance_id) else {
                continue;
            };
            if !processed_classes.insert(instance.class().full_name().to_string()) {
                continue;
            }
            for pred in instance.class().predicates() {
                let is_producer = pred.name() == "Produce";
                for atom_id in pred.atoms() {
                    let Some(sigma_res) = atom_sigma[atom_id] else {
                        continue;
                    };
                    if !slv.is_resolver_active(sigma_res) {
                        continue;
                    }
                    match get_tau(slv, atom_id) {
                        Slot::ObjectRef(cr) => {
                            if is_producer {
                                atoms_by_instance.entry(cr).or_default().0.insert(atom_id);
                            } else {
                                atoms_by_instance.entry(cr).or_default().1.insert(atom_id);
                            }
                        }
                        Slot::Primitive(var) => {
                            if let Some(enum_var) = var.downcast::<EnumVar>()
                                && let Some(cr) = smt.get_enum_val(&enum_var.var)
                            {
                                let cr = ObjectId::from(cr);
                                if is_producer {
                                    atoms_by_instance.entry(cr).or_default().0.insert(atom_id);
                                } else {
                                    atoms_by_instance.entry(cr).or_default().1.insert(atom_id);
                                }
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

impl Class for ConsumableResource {
    fn parents(&self) -> &[Vec<String>] {
        &[]
    }

    fn constructors(&self) -> Vec<Rc<Constructor>> {
        self.constructors.borrow().clone()
    }

    fn get_constructor(&self, args: &[Rc<dyn Type>]) -> Option<Rc<Constructor>> {
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
    fn extract_flaws(&self, slv: &SolverState) -> Result<Vec<FlawWithCauses>, SolverError> {
        let mut flaws: Vec<FlawWithCauses> = Vec::new();
        let atoms_by_instance = self.atoms_by_instance(slv);
        let mut reported: HashSet<(Kind, BTreeSet<AtomId>)> = HashSet::new();

        let smt = slv.smt.borrow();
        let atom_sigma = slv.atom_sigma.borrow();

        for instance_id in self.instances.borrow().iter() {
            let Some((productions, consumptions)) = atoms_by_instance.get(instance_id) else {
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
            let mut durations: HashMap<AtomId, InfRational> = HashMap::new();
            let mut ends: HashMap<AtomId, InfRational> = HashMap::new();
            let mut pulses: BTreeSet<InfRational> = BTreeSet::new();
            let mut amounts: HashMap<AtomId, InfRational> = HashMap::new();

            for &atom_id in productions.iter().chain(consumptions.iter()) {
                let (start, end) = get_interval_vars(slv, atom_id);
                let (start, end) = (smt.get_arith_val(&start).expect("Start time should have a value"), smt.get_arith_val(&end).expect("End time should have a value"));
                starting_atoms.entry(start.clone()).or_default().push(atom_id);
                ending_atoms.entry(end.clone()).or_default().push(atom_id);
                durations.insert(atom_id, end.clone() - start.clone());
                ends.insert(atom_id, end.clone());
                pulses.insert(start);
                pulses.insert(end);
                let amount = smt.get_arith_val(get_amount(slv, atom_id)).expect("Amount should have a value");
                amounts.insert(atom_id, amount);
            }

            let mut started: BTreeSet<AtomId> = BTreeSet::new();
            let mut active: BTreeSet<AtomId> = BTreeSet::new();
            let mut level = initial_amount;
            let mut last_pulse: Option<&InfRational> = None;

            for pulse in &pulses {
                if let Some(prev) = last_pulse {
                    let span = pulse.clone() - prev.clone();
                    for atom_id in &active {
                        let delta = flow_delta(&amounts[atom_id], &span, &durations[atom_id]);
                        if productions.contains(atom_id) {
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
                        let (culprits, others) = if kind == Kind::Overflow { (productions, consumptions) } else { (consumptions, productions) };
                        let past: BTreeSet<AtomId> = started.intersection(culprits).copied().collect();
                        if !past.is_empty() && reported.insert((kind, past.clone())) {
                            let future: BTreeSet<AtomId> = others.iter().copied().filter(|a| ends[a] > *pulse).collect();
                            let settled: BTreeSet<AtomId> = others.iter().copied().filter(|a| ends[a] <= *pulse).collect();

                            let mut causes = Vec::new();
                            for &atom_id in past.iter().chain(future.iter()).chain(settled.iter()) {
                                let r_a = atom_sigma[atom_id].expect("Active atom on timeline should have a Fact/Goal resolver");
                                causes.push(r_a);
                            }
                            flaws.push((Rc::new(LevelFlaw::new(kind, *instance_id, capacity_var.clone(), initial_amount_var.clone(), past, future, settled)), causes));
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
        let atoms_by_instance = self.atoms_by_instance(slv);
        let empty = (BTreeSet::new(), BTreeSet::new());
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

            let (productions, consumptions) = atoms_by_instance.get(instance_id).unwrap_or(&empty);

            let mut starting_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut ending_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut pulses: BTreeSet<InfRational> = BTreeSet::new();
            let mut amounts: HashMap<AtomId, InfRational> = HashMap::new();
            let mut durations: HashMap<AtomId, InfRational> = HashMap::new();

            for &atom_id in productions.iter().chain(consumptions.iter()) {
                let (start, end) = get_interval_vars(slv, atom_id);
                let (start, end) = (smt.get_arith_val(&start).expect("Start time should have a value"), smt.get_arith_val(&end).expect("End time should have a value"));
                amounts.insert(atom_id, smt.get_arith_val(get_amount(slv, atom_id)).expect("Amount should have a value"));
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
                        if productions.contains(atom_id) {
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

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Overflow => write!(f, "overflow"),
            Kind::Underflow => write!(f, "underflow"),
        }
    }
}

struct LevelFlaw {
    kind: Kind,
    instance: ObjectId,
    capacity: ArithExpr,
    initial_amount: ArithExpr,
    past: BTreeSet<AtomId>,
    future: BTreeSet<AtomId>,
    settled: BTreeSet<AtomId>,
}

impl LevelFlaw {
    fn new(kind: Kind, instance: ObjectId, capacity: ArithExpr, initial_amount: ArithExpr, past: BTreeSet<AtomId>, future: BTreeSet<AtomId>, settled: BTreeSet<AtomId>) -> Self {
        Self { kind, instance, capacity, initial_amount, past, future, settled }
    }
}

impl Flaw for LevelFlaw {
    fn expand(&self, slv: &SolverState, flw_id: FlawId) -> Result<(), SolverError> {
        let phi = slv.flaw_phi(flw_id);
        trace!("Expanding {} flaw {} with atoms {}", self.kind, flw_id, self.past.iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", "));

        if slv.lit_val(phi) == Some(false) {
            return Ok(());
        }

        let mut candidates: Vec<(Lit, &'static str)> = Vec::new();

        for &atom_id in &self.past {
            if let Slot::Primitive(var) = get_tau(slv, atom_id) {
                let var = var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                let displace = slv.track_expr(!var.eq(usize::from(self.instance)))?;
                if slv.lit_val(displace) != Some(false) {
                    candidates.push((displace, "displace"));
                }
            }
        }

        for &future_id in &self.future {
            let (_, future_end) = get_interval_vars(slv, future_id);
            for &past_id in &self.past {
                let (past_start, _) = get_interval_vars(slv, past_id);
                let order = slv.track_expr(future_end.clone().le(past_start))?;
                if slv.lit_val(order) != Some(false) {
                    candidates.push((order, "order"));
                }
            }
        }

        // Compress: sufficient condition for the level to stay within [0, capacity] at the flaw's pulse.
        let amounts = |ids: &BTreeSet<AtomId>| ids.iter().map(|&id| get_amount(slv, id)).collect::<Vec<_>>();
        let (lhs, rhs) = match self.kind {
            // initial + Σ started productions ≤ capacity + Σ settled consumptions
            Kind::Overflow => (ArithExpr::Add(iter::once(self.initial_amount.clone()).chain(amounts(&self.past)).collect()), ArithExpr::Add(iter::once(self.capacity.clone()).chain(amounts(&self.settled)).collect())),
            // Σ started consumptions ≤ initial + Σ settled productions
            Kind::Underflow => (ArithExpr::Add(amounts(&self.past)), ArithExpr::Add(iter::once(self.initial_amount.clone()).chain(amounts(&self.settled)).collect())),
        };
        let compress = slv.track_expr(lhs.le(rhs))?;
        if slv.lit_val(compress) != Some(false) {
            candidates.push((compress, "compress"));
        }

        if slv.lit_val(phi) == Some(false) {
            return Ok(());
        }

        add_lit_candidates(slv, flw_id, phi, candidates, |lit, kind| Rc::new(LitResolver::new(lit, json!({ "kind": kind }))))
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": self.kind.to_string(),
            "past": self.past.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
            "future": self.future.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
            "settled": self.settled.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
        })
    }
}
