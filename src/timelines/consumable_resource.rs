use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt,
    rc::{Rc, Weak},
};

use riddle::{
    core::Core,
    delegate_scope,
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
use tracing::trace;

use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
    inf_rat_to_json,
    objects::{ArithVar, EnumVar},
    timelines::{FlawWithCauses, Timeline, get_amount, get_interval_vars, get_tau},
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

        let graph = slv.graph.borrow();
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
                    // Check if the atom has a sigma
                    let Some(sigma_res) = atom_sigma[atom_id] else {
                        continue;
                    };
                    // Check if the atom is active
                    if smt.get_lit_val(graph.rho(sigma_res)) != Some(true) {
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

delegate_scope!(ConsumableResource, scope);

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
        if args.is_empty() { Some(self.constructors.borrow()[0].clone()) } else { None }
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

                            let mut causes = Vec::new();
                            for &atom_id in past.iter().chain(future.iter()) {
                                let r_a = atom_sigma[atom_id].expect("Active atom on timeline should have a Fact/Goal resolver");
                                causes.push(r_a);
                            }
                            flaws.push((Box::new(LevelFlaw::new(kind, *instance_id, capacity_var.clone(), past, future)), causes));
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
                amounts.insert(atom_id, smt.get_arith_val(&get_amount(slv, atom_id)).expect("Amount should have a value"));
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
    past: BTreeSet<AtomId>,
    future: BTreeSet<AtomId>,
}

impl LevelFlaw {
    fn new(kind: Kind, instance: ObjectId, capacity: ArithExpr, past: BTreeSet<AtomId>, future: BTreeSet<AtomId>) -> Self {
        Self { kind, instance, capacity, past, future }
    }
}

impl Flaw for LevelFlaw {
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding {} flaw {} with atoms {}", self.kind, flw_id, self.past.iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", "));

        let mut candidates: Vec<Box<dyn Resolver>> = Vec::new();

        for &atom_id in &self.past {
            let tau = {
                let atom = slv.get_atom(atom_id).ok_or(SolverError::RuntimeError(format!("Atom {} not found", atom_id)))?;
                atom.get("tau").expect("Atom should have a 'tau' field")
            };
            if let Slot::Primitive(var) = tau {
                let var = var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                let displace = slv.track_expr(&mut smt, &mut graph, !var.eq(usize::from(self.instance)))?;
                if smt.probe(&[phi, displace]).map_err(|_| SolverError::Inconsistent)? {
                    candidates.push(Box::new(Displace::new(displace)));
                }
            }
        }

        for &future_id in &self.future {
            let (_, future_end) = get_interval_vars(slv, future_id);
            for &past_id in &self.past {
                let (past_start, _) = get_interval_vars(slv, past_id);
                let order = slv.track_expr(&mut smt, &mut graph, future_end.clone().le(past_start.clone()))?;
                if smt.probe(&[phi, order]).map_err(|_| SolverError::Inconsistent)? {
                    candidates.push(Box::new(Order::new(order)));
                }
            }
        }

        match self.kind {
            Kind::Overflow => {
                let amount = ArithExpr::Add(self.past.iter().map(|&atom_id| get_amount(slv, atom_id)).collect());
                let over_capacity = slv.track_expr(&mut smt, &mut graph, amount.le(self.capacity.clone()))?;
                if smt.probe(&[phi, over_capacity]).map_err(|_| SolverError::Inconsistent)? {
                    candidates.push(Box::new(Compress::new(over_capacity)));
                }
            }
            Kind::Underflow => {
                let amount = ArithExpr::Add(self.past.iter().map(|&atom_id| get_amount(slv, atom_id)).collect());
                let under_zero = slv.track_expr(&mut smt, &mut graph, amount.ge(ArithExpr::Const(rug::Rational::from(0))))?;
                if smt.probe(&[phi, under_zero]).map_err(|_| SolverError::Inconsistent)? {
                    candidates.push(Box::new(Compress::new(under_zero)));
                }
            }
        }

        let single = candidates.len() == 1;
        for res in candidates {
            let rho = if single { phi } else { smt.new_lit() };
            slv.add_resolver(&mut smt, &mut graph, rho, res)?;
        }

        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind" : self.kind.to_string(),
            "past": self.past.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
            "future": self.future.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
        })
    }
}

struct Order {
    lit: Lit,
}

impl Order {
    fn new(lit: Lit) -> Self {
        Self { lit }
    }
}

impl Resolver for Order {
    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().expect("No current resolver found");
        // ρ → lit
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "order"
        })
    }
}

struct Displace {
    lit: Lit,
}

impl Displace {
    fn new(lit: Lit) -> Self {
        Self { lit }
    }
}

impl Resolver for Displace {
    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().expect("No current resolver found");
        // ρ → lit
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "displace"
        })
    }
}

struct Compress {
    lit: Lit,
}

impl Compress {
    fn new(lit: Lit) -> Self {
        Self { lit }
    }
}

impl Resolver for Compress {
    fn apply(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().expect("No current resolver found");
        // ρ → lit
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "displace"
        })
    }
}
