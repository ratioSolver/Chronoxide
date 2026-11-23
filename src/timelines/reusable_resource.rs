use crate::{
    SolverError, SolverState,
    graph::{Flaw, Resolver},
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
use semitone::{Lit, ast::ArithExpr, rational::InfRational};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
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
                        Slot::ObjectRef(rr) => {
                            atoms_by_instance.entry(rr).or_default().push(atom_id);
                        }
                        Slot::Primitive(var) => {
                            if let Some(enum_var) = var.downcast::<EnumVar>()
                                && let Some(rr) = smt.get_enum_val(&enum_var.var)
                            {
                                atoms_by_instance.entry(ObjectId::from(rr)).or_default().push(atom_id);
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

impl Timeline for ReusableResource {
    fn extract_flaws(&self, slv: &SolverState) -> Result<Vec<FlawWithCauses>, SolverError> {
        let mut flaws: Vec<FlawWithCauses> = Vec::new();
        let atoms_by_instance = self.atoms_by_instance(slv);
        let mut reported: HashSet<BTreeSet<AtomId>> = HashSet::new();

        let smt = slv.smt.borrow();
        let atom_sigma = slv.atom_sigma.borrow();

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
                let (start, end) = get_interval_vars(slv, atom_id);
                let (start, end) = (smt.get_arith_val(&start).expect("Start time should have a value"), smt.get_arith_val(&end).expect("End time should have a value"));
                starting_atoms.entry(start.clone()).or_default().push(atom_id);
                ending_atoms.entry(end.clone()).or_default().push(atom_id);
                pulses.insert(start);
                pulses.insert(end);
                let amount = smt.get_arith_val(get_amount(slv, atom_id)).expect("Amount should have a value");
                amounts.insert(atom_id, amount);
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
                            let r_a = atom_sigma[atom_id].expect("Active atom on timeline should have a Fact/Goal resolver");
                            causes.push(r_a);
                        }
                        flaws.push((Box::new(Peak::new(capacity_var.clone(), conflict)), causes));
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
            let atoms = atoms_by_instance.get(instance_id).map(Vec::as_slice).unwrap_or(&[]);

            let mut starting_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut ending_atoms: BTreeMap<InfRational, Vec<AtomId>> = BTreeMap::new();
            let mut pulses: BTreeSet<InfRational> = BTreeSet::new();

            for &atom_id in atoms {
                let (start, end) = get_interval_vars(slv, atom_id);
                let (start, end) = (smt.get_arith_val(&start).expect("Start time should have a value"), smt.get_arith_val(&end).expect("End time should have a value"));
                starting_atoms.entry(start.clone()).or_default().push(atom_id);
                ending_atoms.entry(end.clone()).or_default().push(atom_id);
                pulses.insert(start);
                pulses.insert(end);
            }

            let mut intervals = Vec::new();
            let mut active_atoms: BTreeSet<AtomId> = BTreeSet::new();
            let mut last_pulse: Option<InfRational> = None;

            for pulse in pulses {
                if let Some(prev_pulse) = &last_pulse {
                    intervals.push(json!({
                        "start": inf_rat_to_json(prev_pulse),
                        "end": inf_rat_to_json(&pulse),
                        "atoms": active_atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
                    }));
                }

                if let Some(ending) = ending_atoms.get(&pulse) {
                    for atom_id in ending {
                        active_atoms.remove(atom_id);
                    }
                }
                if let Some(starting) = starting_atoms.get(&pulse) {
                    for atom_id in starting {
                        active_atoms.insert(*atom_id);
                    }
                }

                last_pulse = Some(pulse);
            }

            json[instance_id.to_string()] = json!({
                "type": "ReusableResource",
                "intervals": intervals,
            });
        }

        json
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

impl Type for ReusableResource {
    fn name(&self) -> &str {
        "ReusableResource"
    }

    fn into_class(self: Rc<Self>) -> Option<Rc<dyn Class>> {
        Some(self)
    }

    fn new_instance(self: Rc<Self>) -> Slot {
        Slot::ObjectRef(self.core().new_object(self.clone()))
    }
}

impl Class for ReusableResource {
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

struct Peak {
    capacity: ArithExpr,
    atoms: BTreeSet<AtomId>,
}

impl Peak {
    pub(crate) fn new(capacity: ArithExpr, atoms: BTreeSet<AtomId>) -> Self {
        Self { capacity, atoms }
    }
}

impl Flaw for Peak {
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding Peak flaw {} with atoms {}", flw_id, self.atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", "));

        let mut candidates: Vec<Box<dyn Resolver>> = Vec::with_capacity(3);

        let atoms_vec: Vec<AtomId> = self.atoms.iter().copied().collect();
        for i in 0..atoms_vec.len() {
            for j in (i + 1)..atoms_vec.len() {
                let a = atoms_vec[i];
                let b = atoms_vec[j];

                let a_tau = get_tau(slv, a);
                let b_tau = get_tau(slv, b);
                let displace_expr = match (a_tau, b_tau) {
                    (Slot::Primitive(a_var), Slot::ObjectRef(b_sv)) => {
                        let a_var = a_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        Some(!a_var.eq(usize::from(b_sv)))
                    }
                    (Slot::ObjectRef(a_sv), Slot::Primitive(b_var)) => {
                        let b_var = b_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        Some(!b_var.eq(usize::from(a_sv)))
                    }
                    (Slot::Primitive(a_var), Slot::Primitive(b_var)) => {
                        let a_var = a_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        let b_var = b_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                        Some(!a_var.eq(b_var))
                    }
                    _ => None,
                };
                if let Some(expr) = displace_expr {
                    let displace = slv.track_expr(&mut smt, &mut graph, expr)?;
                    if smt.probe(&[phi, displace]).map_err(|_| SolverError::Inconsistent)? {
                        candidates.push(Box::new(Displace::new(displace)));
                    }
                }

                let (a_start, a_end) = get_interval_vars(slv, a);
                let (b_start, b_end) = get_interval_vars(slv, b);

                let a_before_b = slv.track_expr(&mut smt, &mut graph, a_end.le(b_start))?;
                if smt.probe(&[phi, a_before_b]).map_err(|_| SolverError::Inconsistent)? {
                    candidates.push(Box::new(Order::new(a_before_b)));
                }
                let b_before_a = slv.track_expr(&mut smt, &mut graph, b_end.le(a_start))?;
                if smt.probe(&[phi, b_before_a]).map_err(|_| SolverError::Inconsistent)? {
                    candidates.push(Box::new(Order::new(b_before_a)));
                }
            }
        }

        let amount = ArithExpr::Add(atoms_vec.iter().map(|&atom_id| get_amount(slv, atom_id)).collect());
        let over_capacity = slv.track_expr(&mut smt, &mut graph, amount.le(self.capacity.clone()))?;
        if smt.probe(&[phi, over_capacity]).map_err(|_| SolverError::Inconsistent)? {
            candidates.push(Box::new(Compress::new(over_capacity)));
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
            "kind": "peak",
            "atoms": self.atoms.iter().map(|id| id.to_string()).collect::<Vec<_>>(),
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
