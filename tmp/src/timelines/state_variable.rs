use crate::{
    SolverError, SolverState, Timeline,
    graph::{Flaw, Resolver, ResolverId},
    inf_rat_to_json,
    objects::EnumVar,
    timelines::{FlawWithResolvers, get_atom_vars},
};
use riddle::{
    core::Core,
    env::{AtomId, Env, ObjectId, Slot},
    language::ConstructorDef,
    scope::{Class, CommonScope, Constructor, Field, Function, Predicate, Scope, Type},
};
use semitone::{Lit, rational::InfRational};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    rc::{Rc, Weak},
};
use tracing::trace;

pub(crate) struct StateVariable {
    scope: Rc<CommonScope>,
    constructors: RefCell<Vec<Rc<Constructor>>>,
    instances: RefCell<Vec<ObjectId>>,
}

impl StateVariable {
    pub(crate) fn new(core: Weak<dyn Core>) -> Rc<Self> {
        let sv = Rc::new(Self {
            scope: Rc::new(CommonScope::new(core.clone(), Some(core))),
            constructors: RefCell::new(Vec::new()),
            instances: RefCell::new(Vec::new()),
        });
        sv.constructors.borrow_mut().push(Rc::new(Constructor::new(Rc::downgrade(&sv) as _, ConstructorDef { args: Vec::new(), init: Vec::new(), statements: Vec::new() })));
        sv
    }

    fn atoms_by_instance(&self, slv: &SolverState) -> HashMap<ObjectId, Vec<AtomId>> {
        let mut atoms_by_instance: HashMap<ObjectId, Vec<AtomId>> = HashMap::new();
        let mut processed_classes = HashSet::new();

        let graph = slv.graph.borrow();
        let smt = slv.smt.borrow();
        let atom_fg = slv.atom_fg.borrow();
        for instance_id in self.instances.borrow().iter() {
            let Some(instance) = slv.get_object(*instance_id) else {
                continue;
            };
            if !processed_classes.insert(instance.class().full_name().to_string()) {
                continue;
            }
            for pred in instance.class().predicates() {
                for atom_id in pred.atoms() {
                    let Some(Some(fg_res)) = atom_fg.get(*atom_id) else {
                        continue;
                    };
                    if smt.get_lit_val(graph.rho(*fg_res)) != Some(true) {
                        continue;
                    }
                    let Some(atom) = slv.get_atom(atom_id) else {
                        continue;
                    };
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

        atoms_by_instance
    }
}

impl Type for StateVariable {
    fn name(&self) -> &str {
        "StateVariable"
    }

    fn into_class(self: Rc<Self>) -> Option<Rc<dyn Class>> {
        Some(self)
    }

    fn new_instance(self: Rc<Self>) -> Slot {
        Slot::ObjectRef(self.core().new_object(self.clone()))
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

impl Class for StateVariable {
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

impl Timeline for StateVariable {
    fn extract_flaws(&self, slv: &SolverState) -> Result<Vec<FlawWithResolvers>, SolverError> {
        let mut flaws: Vec<(Vec<ResolverId>, Box<dyn Flaw>)> = Vec::new();
        let atoms_by_instance = self.atoms_by_instance(slv);
        let mut reported: HashSet<(AtomId, AtomId)> = HashSet::new();

        let smt = slv.smt.borrow();
        let atom_fg = slv.atom_fg.borrow();

        for instance_id in self.instances.borrow().iter() {
            let Some(atoms) = atoms_by_instance.get(instance_id) else {
                continue;
            };

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

            for pulse in pulses {
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

                let active_atoms_vec: Vec<AtomId> = active_atoms.iter().copied().collect();
                for pair in active_atoms_vec.windows(2) {
                    let (a, b) = (pair[0], pair[1]);
                    if !reported.insert((a, b)) {
                        continue;
                    }
                    let r_a = atom_fg[*a].expect("Active atom on timeline should have a Fact/Goal resolver");
                    let r_b = atom_fg[*b].expect("Active atom on timeline should have a Fact/Goal resolver");
                    let causes = if r_a == r_b { vec![r_a] } else { vec![r_a, r_b] };
                    flaws.push((causes, Box::new(Peak::new(a, b))));
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
                "type": "StateVariable",
                "intervals": intervals,
            });
        }

        json
    }
}

struct Peak {
    a: AtomId,
    b: AtomId,
}

impl Peak {
    pub(crate) fn new(a: AtomId, b: AtomId) -> Self {
        Self { a, b }
    }
}

impl Flaw for Peak {
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut graph = slv.graph.borrow_mut();
        let mut smt = slv.smt.borrow_mut();
        let (flw_id, phi) = graph.current_flaw().ok_or(SolverError::RuntimeError(String::from("No current flaw found")))?;
        trace!("Expanding Peak flaw {} between atoms {} and {}", flw_id, self.a, self.b);

        let mut candidates: Vec<(Box<dyn Resolver>, Lit)> = Vec::with_capacity(3);

        let (a_tau, b_tau) = {
            let a_atom = slv.get_atom(self.a).ok_or(SolverError::RuntimeError(format!("Atom {} not found", self.a)))?;
            let b_atom = slv.get_atom(self.b).ok_or(SolverError::RuntimeError(format!("Atom {} not found", self.b)))?;
            (a_atom.get("tau").expect("Atom should have a 'tau' field"), b_atom.get("tau").expect("Atom should have a 'tau' field"))
        };
        let displace_expr = match (a_tau, b_tau) {
            (Slot::Primitive(a_var), Slot::ObjectRef(b_sv)) => {
                let a_var = a_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                Some(!a_var.eq(*b_sv as i32))
            }
            (Slot::ObjectRef(a_sv), Slot::Primitive(b_var)) => {
                let b_var = b_var.downcast::<EnumVar>().expect("Atom should have an EnumVar for 'tau'").var.clone();
                Some(!b_var.eq(*a_sv as i32))
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
                candidates.push((Box::new(Displace::new(displace)), displace));
            }
        }

        let (a_start, a_end) = get_atom_vars(slv, self.a);
        let (b_start, b_end) = get_atom_vars(slv, self.b);

        let a_before_b = slv.track_expr(&mut smt, &mut graph, a_end.le(b_start))?;
        if smt.probe(&[phi, a_before_b]).map_err(|_| SolverError::Inconsistent)? {
            candidates.push((Box::new(Order::new(a_before_b)), a_before_b));
        }
        let b_before_a = slv.track_expr(&mut smt, &mut graph, b_end.le(a_start))?;
        if smt.probe(&[phi, b_before_a]).map_err(|_| SolverError::Inconsistent)? {
            candidates.push((Box::new(Order::new(b_before_a)), b_before_a));
        }

        let single = candidates.len() == 1;
        for (resolver, lit) in candidates {
            let rho = if single { phi } else { smt.new_lit() };
            slv.add_clause(&mut smt, &mut graph, vec![!phi, !lit, rho])?;
            slv.add_resolver(&mut smt, &mut graph, resolver, rho)?;
        }

        Ok(())
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "peak",
            "atoms": [self.a.to_string(), self.b.to_string()],
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
    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;
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
    fn apply(&mut self, slv: &SolverState) -> Result<(), SolverError> {
        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();
        let (_, rho) = graph.current_resolver().ok_or(SolverError::RuntimeError(String::from("No current resolver found")))?;
        slv.add_clause(&mut smt, &mut graph, vec![!rho, self.lit])
    }

    fn to_json(&self) -> Value {
        json!({
            "kind": "displace"
        })
    }
}
