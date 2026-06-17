use crate::{
    ToJson,
    flaws::{Flaw, FlawId, Resolver, ResolverId, atom_flaw::AtomFlaw, clause_flaw::ClauseFlaw, enum_flaw::EnumFlaw},
    objects::{ArithVar, BoolVar, EnumVar, StringVar},
    solver::{SolverError, SolverEvent},
};
use linarith::{Lin, Rational};
use riddle::{
    RiddleError,
    core::{CommonCore, Core},
    env::{Atom, AtomId, BoolExpr, Env, Object, ObjectId, Slot, Var},
    language::Disjunction,
    scope::{Class, Field, Function, Predicate, Scope, Type, arith_type},
};
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;
use tracing::{info, trace, warn};
use watchsat::{FALSE_LIT, LBool, Lit, TRUE_LIT, VarId, neg, pos};

pub struct SolverState {
    core: Rc<CommonCore>,
    slv: Weak<SolverState>,
    pub sat: RefCell<watchsat::Engine>,
    prop_q: RefCell<VecDeque<Lit>>,
    pub ac: RefCell<ac3rm::Engine>,
    pub lin: RefCell<linarith::Engine>,
    flaws: RefCell<Vec<Rc<RefCell<Box<dyn Flaw>>>>>,
    atom_flaws: RefCell<Vec<(FlawId, VarId)>>, // Maps AtomId to its corresponding FlawId and sigma variable
    resolvers: RefCell<Vec<Box<dyn Resolver>>>,
    c_flaw: RefCell<Option<FlawId>>,
    c_res: RefCell<Option<ResolverId>>,
    active_flaws: Rc<RefCell<HashSet<FlawId>>>,
    flaw_q: RefCell<VecDeque<FlawId>>,
    to_recompute: Rc<RefCell<HashSet<FlawId>>>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl SolverState {
    pub(super) fn new(tx_event: broadcast::Sender<SolverEvent>) -> Rc<Self> {
        Rc::new_cyclic(|core| SolverState {
            core: {
                let core: Weak<SolverState> = core.clone();
                CommonCore::new(core)
            },
            slv: core.clone(),
            sat: RefCell::new(watchsat::Engine::new()),
            prop_q: RefCell::new(VecDeque::new()),
            ac: RefCell::new(ac3rm::Engine::new()),
            lin: RefCell::new(linarith::Engine::new()),
            flaws: RefCell::new(Vec::new()),
            atom_flaws: RefCell::new(Vec::new()),
            resolvers: RefCell::new(Vec::new()),
            c_flaw: RefCell::new(None),
            c_res: RefCell::new(None),
            active_flaws: Rc::new(RefCell::new(HashSet::new())),
            flaw_q: RefCell::new(VecDeque::new()),
            to_recompute: Rc::new(RefCell::new(HashSet::new())),
            tx_event,
        })
    }

    pub(super) fn read(&self, script: &str) -> Result<(), SolverError> {
        trace!("Reading RiDDle script");
        self.core.read(script).map_err(|e| SolverError::RuntimeError(format!("Failed to read RiDDle script: {:?}", e)))
    }

    pub fn enqueue(&self, lit: Lit) {
        self.prop_q.borrow_mut().push_back(lit);
    }

    pub(super) fn solve(&self) -> bool {
        info!("Solving problem...");
        if !self.build_graph() {
            trace!("No solution found during graph building");
            return false;
        }

        loop {
            let resolvers = self.resolvers.borrow();
            if let Some(flaw) = self.get_most_expensive_flaw() {
                trace!("Best flaw to resolve: {}", flaw);
                let (is_expanded, cost) = {
                    let flaws = self.flaws.borrow();
                    let f = flaws.get(*flaw).expect("Invalid flaw ID").borrow();
                    (f.is_expanded(), f.cost())
                };
                assert!(is_expanded, "Most expensive flaw is not expanded, problem is inconsistent");
                assert!(!cost.is_infinite(), "Most expensive flaw has infinite cost, problem is inconsistent");
                self.set_current_flaw(Some(flaw));
                if let Some(resolver) = self.get_least_expensive_resolver(flaw) {
                    trace!("Best resolver to apply: {}", resolver);
                    self.set_current_resolver(Some(resolver));
                    if let Err(_) = self.sat.borrow_mut().assert(pos(resolvers.get(*resolver).expect("Invalid resolver ID").rho())) {
                        warn!("Failed to assert resolver {}, problem is inconsistent", resolver);
                        return false;
                    }
                    let mut sat = self.sat.borrow_mut();
                    while let Some(lit) = self.prop_q.borrow_mut().pop_front() {
                        match sat.lit_value(&lit) {
                            LBool::True => continue,
                            LBool::False => {
                                warn!("Conflict detected when applying resolver {}, problem is inconsistent", resolver);
                                return false;
                            }
                            LBool::Undef => {
                                if let Err(_) = sat.assert(lit) {
                                    warn!("Failed to add clause for resolver {}, problem is inconsistent", resolver);
                                    return false;
                                }
                            }
                        }
                    }
                    self.set_current_resolver(None);
                } else {
                    warn!("No applicable resolver for flaw {}, problem is inconsistent", flaw);
                    return false;
                }
                self.set_current_flaw(None);
                self.update_costs();
            } else {
                info!("Hurray! No more flaws to resolve. Problem is consistent.");
                return true;
            };
        }
    }

    pub fn add_flaw(&self, flaw: Box<dyn Flaw>) {
        let flaw_id = flaw.id();
        trace!("Adding flaw: {}", flaw_id);
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id,
            phi: flaw.phi(),
            causes: flaw.causes(),
            supports: flaw.supports(),
            status: self.sat.borrow().value(flaw.phi()),
            cost: flaw.cost(),
            data: flaw.to_json(),
        });
        if self.sat.borrow().value(flaw.phi()) == LBool::True {
            let mut active_flaws = self.active_flaws.borrow_mut();
            active_flaws.insert(flaw_id);
            trace!("Active flaws count: {}", active_flaws.len());
        }
        self.sat.borrow_mut().add_listener(flaw.phi(), {
            let tx_event = self.tx_event.clone();
            let active_flaws = self.active_flaws.clone();
            move |_var, val| {
                if val == LBool::True {
                    let mut active_flaws = active_flaws.borrow_mut();
                    if active_flaws.insert(flaw_id) {
                        trace!("Flaw {} became active.", flaw_id);
                        trace!("Active flaws count: {}", active_flaws.len());
                    }
                }
                let _ = tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id, status: val });
            }
        });
        self.flaw_q.borrow_mut().push_back(flaw_id);
        self.flaws.borrow_mut().push(Rc::new(RefCell::new(flaw)));
    }

    pub fn is_expanded(&self, atom_id: AtomId) -> bool {
        let flaw_id = self.atom_flaws.borrow().get(*atom_id).expect("Atom should have a corresponding flaw").0;
        self.flaws.borrow().get(*flaw_id).expect("Invalid flaw ID").borrow().is_expanded()
    }

    pub(crate) fn get_sigma(&self, atom_id: AtomId) -> VarId {
        self.atom_flaws.borrow().get(*atom_id).expect("Atom should have a corresponding flaw").1
    }

    pub fn add_resolver(&self, flaw: &mut impl Flaw, resolver: Box<dyn Resolver>) {
        let resolver_id = resolver.id();
        trace!("Adding resolver: {}", resolver_id);
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id,
            rho: resolver.rho(),
            flaw_id: resolver.flaw(),
            requirements: resolver.requirements(),
            intrinsic_cost: resolver.intrinsic_cost(),
            status: self.sat.borrow().value(resolver.rho()),
            data: resolver.to_json(),
        });
        if self.sat.borrow().value(resolver.rho()) == LBool::True {
            let mut active_flaws = self.active_flaws.borrow_mut();
            if active_flaws.remove(&resolver.flaw()) {
                trace!("Flaw {} resolved by resolver {}.", resolver.flaw(), resolver_id);
                trace!("Active flaws count: {}", active_flaws.len());
            }
        }
        let active_flaws = self.active_flaws.clone();
        let resolver_flaw = resolver.flaw();
        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        self.sat.borrow_mut().add_listener(resolver.rho(), {
            let tx_event = self.tx_event.clone();
            let to_recompute = self.to_recompute.clone();
            move |_var, val| {
                match val {
                    LBool::True => {
                        if let Some(constrs) = solver.resolvers.borrow().get(*resolver_id).expect("Invalid resolver ID").ac_constraints() {
                            match solver.ac.borrow_mut().assert_batch(&constrs) {
                                Ok(_) => {
                                    trace!("Applied AC constraints for resolver {} successfully.", resolver_id);
                                }
                                Err(e) => trace!("Failed to apply AC constraints for resolver {} with error: {:?}. Problem might be inconsistent.", resolver_id, e),
                            }
                        }
                        let mut active_flaws = active_flaws.borrow_mut();
                        if active_flaws.remove(&resolver_flaw) {
                            trace!("Flaw {} resolved by resolver {}.", resolver_flaw, resolver_id);
                            trace!("Active flaws count: {}", active_flaws.len());
                        }
                        to_recompute.borrow_mut().remove(&resolver_flaw);
                    }
                    LBool::False => {
                        to_recompute.borrow_mut().insert(resolver_flaw);
                    }
                    LBool::Undef => {}
                }
                let _ = tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id, status: val });
            }
        });

        flaw.add_resolver(resolver_id);
        self.sat.borrow_mut().add_clause(vec![neg(resolver.rho()), pos(flaw.phi())]).expect("Failed to add clause for OR flaw resolver");
        self.resolvers.borrow_mut().push(resolver);
    }

    pub fn get_resolvers_len(&self) -> usize {
        self.resolvers.borrow().len()
    }

    pub(crate) fn add_causal_link(&self, flaw_id: FlawId, resolver_id: ResolverId) {
        self.flaws.borrow().get(*flaw_id).expect("Invalid flaw ID").borrow_mut().add_support(resolver_id);
        self.sat.borrow_mut().add_clause(vec![neg(self.resolvers.borrow().get(*resolver_id).expect("Invalid resolver ID").rho()), pos(self.flaws.borrow().get(*flaw_id).expect("Invalid flaw ID").borrow().phi())]).expect("Failed to add clause for causal link");
        let _ = self.tx_event.send(SolverEvent::NewCausalLink { flaw_id, resolver_id });
    }

    fn set_current_flaw(&self, flaw: Option<FlawId>) {
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(flaw));
        self.c_flaw.replace(flaw);
    }

    fn set_current_resolver(&self, resolver: Option<ResolverId>) {
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(resolver));
        self.c_res.replace(resolver);
    }

    fn build_graph(&self) -> bool {
        info!("Building graph...");
        while self.active_flaws.borrow().iter().any(|flaw| self.flaws.borrow().get(**flaw).expect("Invalid flaw ID").borrow().cost().is_infinite()) {
            if let Some(flaw) = self.flaw_q.borrow_mut().pop_front() {
                trace!("Expanding flaw {}", flaw);
                let flaw_ref = self.flaws.borrow().get(*flaw).expect("Invalid flaw ID").clone();
                flaw_ref.borrow_mut().compute_resolvers();
                let (flaw_phi, resolver_ids) = {
                    let f = flaw_ref.borrow();
                    (f.phi(), f.resolvers())
                };
                let mut causal_constraint = vec![neg(flaw_phi)];
                for res_id in resolver_ids {
                    trace!("Applying resolver {}", res_id);
                    self.set_current_resolver(Some(res_id));
                    let rho = {
                        let mut resolvers = self.resolvers.borrow_mut();
                        let resolver = resolvers.get_mut(*res_id).expect("Invalid resolver ID");
                        if let Err(_) = resolver.apply() {
                            trace!("Failed to apply resolver {}", res_id);
                            return false;
                        }
                        resolver.rho()
                    };
                    causal_constraint.push(pos(rho));
                }
                self.set_current_resolver(None);
                if let Err(_) = self.sat.borrow_mut().add_clause(causal_constraint) {
                    trace!("Failed to add causal constraint for flaw {}", flaw);
                    return false;
                }
                self.compute_flaw_cost(flaw);
            } else {
                trace!("No more active flaws to expand, but some flaws have infinite cost. No solution found.");
                return false;
            }
        }
        true
    }

    fn update_costs(&self) {
        trace!("Recomputing costs for flaws: {}", self.to_recompute.borrow().iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", "));
        for flaw_id in self.to_recompute.borrow().iter() {
            self.compute_flaw_cost(*flaw_id);
        }
        self.to_recompute.borrow_mut().clear();
    }

    fn compute_flaw_cost(&self, flaw_id: FlawId) {
        trace!("Computing cost for flaw: {}", flaw_id);
        let mut stack: Vec<(FlawId, HashSet<FlawId>)> = vec![(flaw_id, HashSet::new())];

        let resolvers = self.resolvers.borrow();
        while let Some((flaw, mut visited)) = stack.pop() {
            let mut current_cost = Rational::POSITIVE_INFINITY;

            let (phi, resolver_ids, old_cost, supports) = {
                let flaws = self.flaws.borrow();
                let f = flaws.get(*flaw).expect("Invalid flaw ID").borrow();
                (f.phi(), f.resolvers(), f.cost(), f.supports())
            };

            if self.sat.borrow().value(phi) != LBool::False && visited.insert(flaw_id) {
                for resolver_id in resolver_ids {
                    let resolver = resolvers.get(*resolver_id).expect("Invalid resolver ID");
                    if self.sat.borrow().value(resolver.rho()) != LBool::False {
                        let resolver_cost = self.compute_resolver_cost(resolver_id);
                        if resolver_cost < current_cost {
                            current_cost = resolver_cost;
                        }
                    }
                }
            }

            if old_cost != current_cost {
                trace!("Updating cost for flaw {} from {} to {}", flaw_id, old_cost, current_cost);
                let flaw_ref = {
                    let flaws = self.flaws.borrow();
                    flaws.get(*flaw_id).expect("Invalid flaw ID").clone()
                };
                flaw_ref.borrow_mut().set_cost(current_cost);
                let _ = self.tx_event.send(SolverEvent::FlawCostUpdate { flaw_id, cost: current_cost });
                for support in supports {
                    let support = resolvers.get(*support).expect("Invalid flaw cause");
                    stack.push((support.flaw(), visited.clone()));
                }
            }
        }
    }

    fn compute_resolver_cost(&self, resolver: ResolverId) -> Rational {
        let resolvers = self.resolvers.borrow();
        let resolver = resolvers.get(*resolver).expect("Invalid resolver ID");
        resolver.requirements().iter().map(|flaw| self.flaws.borrow().get(**flaw).expect("Invalid resolver requirement").borrow().cost()).fold(resolver.intrinsic_cost(), |max_cost, c| if c > max_cost { c } else { max_cost })
    }

    fn get_most_expensive_flaw(&self) -> Option<FlawId> {
        let flaws = self.flaws.borrow();
        self.active_flaws.borrow().iter().max_by_key(|flaw| flaws.get(***flaw).expect("Invalid flaw ID").borrow().cost()).copied()
    }

    fn get_least_expensive_resolver(&self, flaw: FlawId) -> Option<ResolverId> {
        let resolvers = self.resolvers.borrow();
        let flaws = self.flaws.borrow();
        let flaw = flaws.get(*flaw).expect("Invalid flaw ID").borrow();
        flaw.resolvers().iter().filter_map(|res_id| if self.sat.borrow().value(resolvers.get(**res_id).expect("Invalid resolver ID").rho()) != LBool::False { Some((res_id, self.compute_resolver_cost(*res_id))) } else { None }).min_by_key(|(_, cost)| *cost).map(|(res_id, _)| *res_id)
    }
}

impl Scope for SolverState {
    fn core(&self) -> Rc<dyn Core> {
        self.slv.upgrade().expect("SolverState should never be dropped while in use")
    }
    fn scope(&self) -> Option<Rc<dyn Scope>> {
        None
    }

    fn get_fields(&self) -> Vec<Rc<Field>> {
        self.core.get_fields()
    }
    fn get_field(&self, name: &str) -> Option<Rc<Field>> {
        self.core.get_field(name)
    }
    fn get_function(&self, name: &str, types: &[Rc<dyn Type>]) -> Option<Rc<Function>> {
        self.core.get_function(name, types)
    }
    fn get_type(&self, name: &str) -> Option<Rc<dyn Type>> {
        self.core.get_type(name)
    }
    fn get_predicate(&self, name: &str) -> Option<Rc<Predicate>> {
        self.core.get_predicate(name)
    }
}

impl Env for SolverState {
    fn parent(&self) -> Option<Rc<dyn Env>> {
        None
    }

    fn get(&self, name: &str) -> Option<Slot> {
        self.core.get(name)
    }

    fn set(&self, name: String, value: Slot) {
        self.core.set(name, value);
    }
}

impl Core for SolverState {
    fn new_bool(&self, value: bool) -> Slot {
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), if value { TRUE_LIT } else { FALSE_LIT })))
    }
    fn new_bool_var(&self) -> Slot {
        Slot::Primitive(Rc::new(BoolVar::new(self.bool_type(), pos(self.sat.borrow_mut().add_var()))))
    }
    fn new_int(&self, value: i64) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), Lin::from(value))))
    }
    fn new_int_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), Lin::from(self.lin.borrow_mut().add_var()))))
    }
    fn new_real(&self, num: i64, den: i64) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), Lin::from(Rational::new(num, den)))))
    }
    fn new_real_var(&self) -> Slot {
        Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), Lin::from(self.lin.borrow_mut().add_var()))))
    }
    fn new_string(&self, value: &str) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), value.to_string())))
    }
    fn new_string_var(&self) -> Slot {
        Slot::Primitive(Rc::new(StringVar::new(self.string_type(), String::new())))
    }

    fn sum(&self, sum: &[Slot]) -> Result<Slot, RiddleError> {
        let mut result = Lin::from(0);
        for var in sum {
            match var {
                Slot::Primitive(var) => {
                    if let Some(var) = var.clone().as_any().downcast_ref::<ArithVar>() {
                        result += &var.lin
                    } else {
                        return Err(RiddleError::RuntimeError("Expected int or real".to_string()));
                    };
                }
                _ => return Err(RiddleError::RuntimeError("Expected int or real".to_string())),
            }
        }
        let tp = arith_type(self, sum)?;
        if tp.name() == "int" { Ok(Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), result)))) } else { Ok(Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), result)))) }
    }
    fn opposite(&self, term: Slot) -> Result<Slot, RiddleError> {
        match term {
            Slot::Primitive(var) => {
                if let Some(arith_var) = var.as_any().downcast_ref::<ArithVar>() {
                    Ok(Slot::Primitive(Rc::new(ArithVar::new(arith_var.var_type(), -arith_var.lin.clone()))))
                } else {
                    Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                }
            }
            _ => Err(RiddleError::RuntimeError("Expected int or real".to_string())),
        }
    }
    fn mul(&self, mul: &[Slot]) -> Result<Slot, RiddleError> {
        let mut result = Lin::from(1);
        for var in mul {
            match var {
                Slot::Primitive(var) => {
                    if let Some(var) = var.clone().as_any().downcast_ref::<ArithVar>() {
                        if result.vars.is_empty() {
                            result = &var.lin * result.known_term;
                        } else if var.lin.vars.is_empty() {
                            result = &result * var.lin.known_term;
                        } else {
                            return Err(RiddleError::RuntimeError("Non-linear multiplication is not supported".to_string()));
                        }
                    } else {
                        panic!("Expected int or real");
                    };
                }
                _ => return Err(RiddleError::RuntimeError("Expected int or real".to_string())),
            }
        }
        if arith_type(self, mul)?.name() == "int" { Ok(Slot::Primitive(Rc::new(ArithVar::new(self.int_type(), result)))) } else { Ok(Slot::Primitive(Rc::new(ArithVar::new(self.real_type(), result)))) }
    }
    fn div(&self, left: Slot, right: Slot) -> Result<Slot, RiddleError> {
        match (left, right) {
            (Slot::Primitive(left_var), Slot::Primitive(right_var)) => {
                if let Some(right_arith_var) = right_var.as_any().downcast_ref::<ArithVar>() {
                    if right_arith_var.lin.vars.is_empty() {
                        if let Some(left_arith_var) = left_var.as_any().downcast_ref::<ArithVar>() {
                            let result_lin = if left_arith_var.var_type().name() == "int" && right_arith_var.var_type().name() == "int" {
                                ArithVar::new(self.int_type(), left_arith_var.lin.clone() / right_arith_var.lin.known_term)
                            } else {
                                ArithVar::new(self.real_type(), left_arith_var.lin.clone() / right_arith_var.lin.known_term)
                            };
                            Ok(Slot::Primitive(Rc::new(result_lin)))
                        } else {
                            Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                        }
                    } else {
                        Err(RiddleError::RuntimeError("Non-linear division is not supported".to_string()))
                    }
                } else {
                    Err(RiddleError::RuntimeError("Expected int or real".to_string()))
                }
            }
            _ => Err(RiddleError::RuntimeError("Expected int or real".to_string())),
        }
    }

    fn assert(&self, term: Rc<BoolExpr>) -> bool {
        let mut resolvers = self.resolvers.borrow_mut();
        match term.as_ref() {
            BoolExpr::Term { term, .. } => {
                let lit = bool_lit(term);
                if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                    return self.sat.borrow_mut().add_clause(vec![neg(res.rho()), lit]).is_ok();
                } else {
                    return self.sat.borrow_mut().add_clause(vec![lit]).is_ok();
                }
            }
            BoolExpr::Eq { left, right, .. } => match (left, right) {
                (Slot::Primitive(left), Slot::Primitive(right)) => {
                    if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<BoolVar>(), right.clone().as_any().downcast_ref::<BoolVar>()) {
                        let left_lit = left.lit;
                        let right_lit = right.lit;
                        if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                            self.sat.borrow_mut().add_clause(vec![neg(res.rho()), left_lit, !right_lit]).is_ok() && self.sat.borrow_mut().add_clause(vec![neg(res.rho()), !left_lit, right_lit]).is_ok()
                        } else {
                            self.sat.borrow_mut().add_clause(vec![left_lit, !right_lit]).is_ok() && self.sat.borrow_mut().add_clause(vec![!left_lit, right_lit]).is_ok()
                        }
                    } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<ArithVar>(), right.clone().as_any().downcast_ref::<ArithVar>()) {
                        let left_lin = &left.lin;
                        let right_lin = &right.lin;
                        let lin_cnstr = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)).and_then(|res| Some(res.lin_guard()));
                        self.lin.borrow_mut().new_eq(left_lin, right_lin, lin_cnstr).is_ok()
                    } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<StringVar>(), right.clone().as_any().downcast_ref::<StringVar>()) {
                        if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) { self.sat.borrow_mut().add_clause(vec![neg(res.rho())]).is_ok() } else { left.value == right.value }
                    } else if let (Some(left), Some(right)) = (left.clone().as_any().downcast_ref::<EnumVar>(), right.clone().as_any().downcast_ref::<EnumVar>()) {
                        let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Equality(left.var, right.var));
                        if let Some(res) = self.c_res.borrow_mut().and_then(|res_id| resolvers.get_mut(*res_id)) {
                            res.add_ac_constraint(constraint_id);
                            true
                        } else {
                            self.ac.borrow_mut().assert(constraint_id).is_ok()
                        }
                    } else if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                        self.sat.borrow_mut().add_clause(vec![neg(res.rho())]).is_ok()
                    } else {
                        false
                    }
                }
                (Slot::Primitive(left), Slot::ObjectRef(right)) => {
                    if let Some(left) = left.clone().as_any().downcast_ref::<EnumVar>() {
                        let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Set(left.var, **right as i32));
                        if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get_mut(*res_id)) {
                            res.add_ac_constraint(constraint_id);
                            true
                        } else {
                            self.ac.borrow_mut().assert(constraint_id).is_ok()
                        }
                    } else if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                        self.sat.borrow_mut().add_clause(vec![neg(res.rho())]).is_ok()
                    } else {
                        false
                    }
                }
                (Slot::ObjectRef(left), Slot::Primitive(right)) => {
                    if let Some(right) = right.clone().as_any().downcast_ref::<EnumVar>() {
                        let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Set(right.var, **left as i32));
                        if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get_mut(*res_id)) {
                            res.add_ac_constraint(constraint_id);
                            true
                        } else {
                            self.ac.borrow_mut().assert(constraint_id).is_ok()
                        }
                    } else if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                        self.sat.borrow_mut().add_clause(vec![neg(res.rho())]).is_ok()
                    } else {
                        false
                    }
                }
                _ => {
                    if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                        self.sat.borrow_mut().add_clause(vec![neg(res.rho())]).is_ok()
                    } else {
                        false
                    }
                }
            },
            BoolExpr::Lt { left, right, .. } => {
                let left_lin = numeric_lin(left);
                let right_lin = numeric_lin(right);
                let lin_cnstr = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)).and_then(|res| Some(res.lin_guard()));
                return self.lin.borrow_mut().new_lt(&left_lin, &right_lin, true, lin_cnstr).is_ok();
            }
            BoolExpr::Leq { left, right, .. } => {
                let left_lin = numeric_lin(left);
                let right_lin = numeric_lin(right);
                let lin_cnstr = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)).and_then(|res| Some(res.lin_guard()));
                return self.lin.borrow_mut().new_le(&left_lin, &right_lin, lin_cnstr).is_ok();
            }
            BoolExpr::Or { terms, .. } => {
                let lits: Vec<Lit> = terms
                    .iter()
                    .map(|term| match term.as_ref() {
                        BoolExpr::Term { term, .. } => match term {
                            Slot::Primitive(var) => {
                                if let Some(bool_var) = var.clone().as_any().downcast_ref::<BoolVar>() {
                                    bool_var.lit
                                } else {
                                    panic!("Expected BoolVar");
                                }
                            }
                            _ => panic!("Expected BoolExpr::Term with a BoolVar"),
                        },
                        _ => panic!("Expected BoolExpr::Term"),
                    })
                    .collect();
                let (phi, cause) = if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) { (pos(res.rho()), Some(res.id())) } else { (TRUE_LIT, None) };
                let flaw_id = FlawId(self.flaws.borrow().len());
                self.add_flaw(ClauseFlaw::new(self.slv.clone(), flaw_id, phi.var(), cause, lits));
                true
            }
            BoolExpr::And { terms, .. } => {
                for term in terms {
                    if !self.assert(term.clone()) {
                        return false;
                    }
                }
                true
            }
            BoolExpr::Not { term, .. } => match term.as_ref() {
                BoolExpr::Term { term, .. } => {
                    let lit = bool_lit(term);
                    if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                        return self.sat.borrow_mut().add_clause(vec![neg(res.rho()), !lit]).is_ok();
                    } else {
                        return self.sat.borrow_mut().add_clause(vec![!lit]).is_ok();
                    }
                }
                BoolExpr::Eq { left, right, .. } => match (left, right) {
                    (Slot::Primitive(left_v), Slot::Primitive(right_v)) => {
                        if let (Some(left), Some(right)) = (left_v.clone().as_any().downcast_ref::<BoolVar>(), right_v.clone().as_any().downcast_ref::<BoolVar>()) {
                            let left_lit = left.lit;
                            let right_lit = right.lit;
                            if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) { self.sat.borrow_mut().add_clause(vec![neg(res.rho()), !left_lit, !right_lit]).is_ok() } else { self.sat.borrow_mut().add_clause(vec![!left_lit, !right_lit]).is_ok() }
                        } else if let (Some(_left), Some(_right)) = (left_v.clone().as_any().downcast_ref::<ArithVar>(), right_v.clone().as_any().downcast_ref::<ArithVar>()) {
                            self.assert(Rc::new(BoolExpr::Or {
                                var_type: Rc::downgrade(&self.bool_type()),
                                terms: vec![Rc::new(BoolExpr::Lt { var_type: Rc::downgrade(&self.bool_type()), left: left.clone(), right: right.clone() }), Rc::new(BoolExpr::Lt { var_type: Rc::downgrade(&self.bool_type()), left: left.clone(), right: right.clone() })],
                            }))
                        } else if let (Some(left), Some(right)) = (left_v.clone().as_any().downcast_ref::<StringVar>(), right_v.clone().as_any().downcast_ref::<StringVar>()) {
                            if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) { self.sat.borrow_mut().add_clause(vec![neg(res.rho())]).is_ok() } else { left.value != right.value }
                        } else if let (Some(left), Some(right)) = (left_v.clone().as_any().downcast_ref::<EnumVar>(), right_v.clone().as_any().downcast_ref::<EnumVar>()) {
                            let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Inequality(left.var, right.var));
                            if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get_mut(*res_id)) {
                                res.add_ac_constraint(constraint_id);
                                true
                            } else {
                                self.ac.borrow_mut().assert(constraint_id).is_ok()
                            }
                        } else {
                            true
                        }
                    }
                    (Slot::Primitive(left), Slot::ObjectRef(right)) => {
                        if let Some(left) = left.clone().as_any().downcast_ref::<EnumVar>() {
                            let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Forbid(left.var, **right as i32));
                            if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get_mut(*res_id)) {
                                res.add_ac_constraint(constraint_id);
                                true
                            } else {
                                self.ac.borrow_mut().assert(constraint_id).is_ok()
                            }
                        } else if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                            self.sat.borrow_mut().add_clause(vec![neg(res.rho())]).is_ok()
                        } else {
                            false
                        }
                    }
                    (Slot::ObjectRef(left), Slot::Primitive(right)) => {
                        if let Some(right) = right.clone().as_any().downcast_ref::<EnumVar>() {
                            let constraint_id = self.ac.borrow_mut().new_constraint(ac3rm::Constraint::Forbid(right.var, **left as i32));
                            if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get_mut(*res_id)) {
                                res.add_ac_constraint(constraint_id);
                                true
                            } else {
                                self.ac.borrow_mut().assert(constraint_id).is_ok()
                            }
                        } else if let Some(res) = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)) {
                            self.sat.borrow_mut().add_clause(vec![neg(res.rho())]).is_ok()
                        } else {
                            false
                        }
                    }
                    _ => true,
                },
                BoolExpr::Lt { left, right, .. } => {
                    let left_lin = numeric_lin(left);
                    let right_lin = numeric_lin(right);
                    let lin_cnstr = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)).and_then(|res| Some(res.lin_guard()));
                    return self.lin.borrow_mut().new_ge(&left_lin, &right_lin, lin_cnstr).is_ok();
                }
                BoolExpr::Leq { left, right, .. } => {
                    let left_lin = numeric_lin(left);
                    let right_lin = numeric_lin(right);
                    let lin_cnstr = self.c_res.borrow().and_then(|res_id| resolvers.get(*res_id)).and_then(|res| Some(res.lin_guard()));
                    return self.lin.borrow_mut().new_gt(&left_lin, &right_lin, true, lin_cnstr).is_ok();
                }
                _ => panic!("Expected BoolExpr::Term, BoolExpr::Eq, BoolExpr::Lt, or BoolExpr::Leq"),
            },
        }
    }

    fn new_var(&self, class: Rc<dyn Class>, instances: &[ObjectId]) -> Result<Slot, RiddleError> {
        let vals = instances.iter().map(|id| **id as i32).collect::<Vec<_>>();
        let var = self.ac.borrow_mut().add_var(vals);
        let var = Rc::new(EnumVar::new(class, var));
        let resolvers = self.resolvers.borrow();
        let c_res = self.c_res.borrow().map_or(None, |res_id| resolvers.get(*res_id).map(|res| res.as_ref()));
        let rho = c_res.map_or(watchsat::TRUE_LIT, |res| pos(res.rho()));
        let cause = c_res.map(|res| res.id());
        let flaw_id = FlawId(self.flaws.borrow().len());
        self.add_flaw(EnumFlaw::new(self.slv.clone(), flaw_id, rho.var(), cause, var.clone()));
        Ok(Slot::Primitive(var))
    }

    fn new_disjunction(&self, _disjunction: Disjunction) {
        unimplemented!()
    }

    fn new_object(&self, class: Rc<dyn Class>) -> ObjectId {
        self.core.new_object(class)
    }
    fn get_object(&self, id: ObjectId) -> Option<Rc<Object>> {
        self.core.get_object(id)
    }
    fn new_atom(&self, predicate: Rc<Predicate>, fact: bool, args: HashMap<String, Slot>) -> AtomId {
        let atm = self.core.new_atom(predicate, fact, args);
        let resolvers = self.resolvers.borrow();
        let c_res = self.c_res.borrow().map_or(None, |res_id| resolvers.get(*res_id).map(|res| res.as_ref()));
        let rho = c_res.map_or(watchsat::TRUE_LIT, |res| pos(res.rho()));
        let cause = c_res.map(|res| res.id());
        let flaw_id = FlawId(self.flaws.borrow().len());
        let sigma = self.sat.borrow_mut().add_var();
        self.add_flaw(AtomFlaw::new(self.slv.clone(), flaw_id, rho.var(), cause, atm.clone()));
        self.atom_flaws.borrow_mut().push((flaw_id, sigma));
        if let Some(res) = c_res {
            // resolvers.get_mut(*res.id()).expect("Invalid resolver ID").add_requirement(flaw_id);
        }
        atm
    }
    fn get_atom(&self, id: AtomId) -> Option<Rc<Atom>> {
        self.core.get_atom(id)
    }
}

impl ToJson for SolverState {
    fn to_json(&self) -> Value {
        let mut slv = json!({
            "flaws": self.flaws.borrow().iter().map(|f| f.borrow().to_json()).collect::<Vec<_>>(),
            "resolvers": self.resolvers.borrow().iter().map(|r| r.to_json()).collect::<Vec<_>>(),
        });
        if let Some(current_flaw) = self.c_flaw.borrow().as_ref() {
            slv["current_flaw"] = json!(current_flaw.0);
        }
        if let Some(current_resolver) = self.c_res.borrow().as_ref() {
            slv["current_resolver"] = json!(current_resolver.0);
        }
        slv
    }
}

fn bool_lit(var: &Slot) -> Lit {
    if let Slot::Primitive(var) = var {
        var.clone().as_any().downcast_ref::<BoolVar>().expect("Expected BoolVar").lit
    } else {
        panic!("Expected BoolVar");
    }
}

fn numeric_lin(var: &Slot) -> Lin {
    if let Slot::Primitive(var) = var {
        var.clone().as_any().downcast_ref::<ArithVar>().expect("Expected ArithVar").lin.clone()
    } else {
        panic!("Expected ArithVar");
    }
}
