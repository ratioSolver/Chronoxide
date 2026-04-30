use crate::{
    ToJson,
    flaws::{Flaw, Resolver},
    solver::{SolverEvent, SolverState},
};
use consensus::{LBool, neg, pos};
use linspire::rational::Rational;
use riddle::serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{HashSet, VecDeque},
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;
use tracing::trace;

pub struct Graph {
    slv: Weak<SolverState>,
    flaws: Vec<Rc<dyn Flaw>>,
    resolvers: Vec<Rc<dyn Resolver>>,
    flaw_q: VecDeque<Rc<dyn Flaw>>,
    c_flaw: Option<Rc<dyn Flaw>>,
    c_res: Option<Rc<dyn Resolver>>,
    active_flaws: Rc<RefCell<HashSet<usize>>>,
    to_recompute: Rc<RefCell<HashSet<usize>>>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl Graph {
    pub(crate) fn new(slv: Weak<SolverState>, tx_event: broadcast::Sender<SolverEvent>) -> Self {
        Self {
            slv,
            flaws: Vec::new(),
            resolvers: Vec::new(),
            flaw_q: VecDeque::new(),
            c_flaw: None,
            c_res: None,
            active_flaws: Rc::new(RefCell::new(HashSet::new())),
            to_recompute: Rc::new(RefCell::new(HashSet::new())),
            tx_event,
        }
    }

    pub(crate) fn build_graph(&mut self) -> bool {
        trace!("Building graph...");
        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        while self.active_flaws.borrow().iter().any(|flaw| self.flaws.get(*flaw).expect("Invalid flaw ID").cost().is_infinite()) {
            if let Some(flaw) = self.flaw_q.pop_front() {
                trace!("Processing flaw: {:?}", flaw.id());
                let mut causal_constraint = Vec::new();
                causal_constraint.push(neg(flaw.phi()));
                for resolver in flaw.clone().compute_resolvers(self.resolvers.len()) {
                    self.add_resolver(resolver.clone());
                    causal_constraint.push(pos(resolver.rho()));
                    self.c_res.replace(resolver.clone());
                    match resolver.apply() {
                        Ok(_) => trace!("Applied resolver {:?} for flaw {:?} successfully", resolver.id(), flaw.id()),
                        Err(e) => trace!("Failed to apply resolver {:?} for flaw {:?} with error: {:?}", resolver.id(), flaw.id(), e),
                    }
                }
                self.c_res.take(); // Clear the current resolver after processing
                if !solver.sat.borrow_mut().add_clause(causal_constraint) {
                    trace!("Failed to add causal constraint for flaw {:?}. Problem is inconsistent.", flaw.id());
                    return false;
                }

                self.compute_flaw_cost(flaw.clone());
            } else {
                trace!("No more flaws to process, but some flaws are still active with infinite cost. Problem is inconsistent.");
                return false;
            }
        }
        trace!("Graph built successfully");
        true
    }

    fn compute_flaw_cost(&mut self, flaw: Rc<dyn Flaw>) {
        trace!("Computing cost for flaw: {:?}", flaw.id());
        let mut stack: Vec<(Rc<dyn Flaw>, HashSet<usize>)> = vec![(flaw, HashSet::new())];

        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        while let Some((flaw, mut visited)) = stack.pop() {
            let mut current_cost = Rational::POSITIVE_INFINITY;

            if solver.sat.borrow().value(flaw.phi()) != &LBool::False && visited.insert(flaw.id()) {
                for resolver_id in flaw.resolvers() {
                    let resolver = self.resolvers.get(resolver_id).expect("Invalid resolver ID").clone();
                    if solver.sat.borrow().value(resolver.rho()) != &LBool::False {
                        let resolver_cost = self.compute_resolver_cost(resolver.as_ref());
                        if resolver_cost < current_cost {
                            current_cost = resolver_cost;
                        }
                    }
                }
            }

            if flaw.cost() != current_cost {
                trace!("Updating cost for flaw {:?} from {} to {}", flaw.id(), flaw.cost(), current_cost);
                flaw.set_cost(current_cost);
                let _ = self.tx_event.send(SolverEvent::FlawCostUpdate({
                    let mut msg = flaw.to_json();
                    msg["id"] = format!("f{}", flaw.id()).into();
                    msg["cost"] = current_cost.to_json();
                    msg
                }));

                for support in flaw.supports() {
                    let support = self.resolvers.get(support).expect("Invalid flaw cause");
                    let support_flaw = self.flaws.get(support.flaw()).expect("Invalid flaw cause").clone();
                    stack.push((support_flaw, visited.clone()));
                }
            }
        }
    }

    fn compute_resolver_cost(&self, resolver: &dyn Resolver) -> Rational {
        resolver.requirements().iter().map(|flaw| self.flaws.get(*flaw).expect("Invalid resolver requirement").cost()).fold(resolver.intrinsic_cost(), |max_cost, c| if c > max_cost { c } else { max_cost })
    }

    pub fn add_flaw(&mut self, flaw: Rc<dyn Flaw>) {
        trace!("Adding flaw: {:?}", flaw.id());
        let _ = self.tx_event.send(SolverEvent::NewFlaw(flaw.to_json()));
        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        if solver.sat.borrow().value(flaw.phi()) == &LBool::True {
            let mut active_flaws = self.active_flaws.borrow_mut();
            active_flaws.insert(flaw.id());
            trace!("Active flaws count: {}", active_flaws.len());
        }
        self.flaws.push(flaw.clone());
        solver.sat.borrow_mut().add_listener(flaw.phi(), {
            let flaw_id = flaw.id();
            let tx_event = self.tx_event.clone();
            let active_flaws = self.active_flaws.clone();
            move |sat, var| {
                if sat.value(var) == &LBool::True {
                    let mut active_flaws = active_flaws.borrow_mut();
                    if active_flaws.insert(flaw_id) {
                        trace!("Flaw {:?} became active.", flaw_id);
                        trace!("Active flaws count: {}", active_flaws.len());
                    }
                }
                let _ = tx_event.send(SolverEvent::FlawStatusUpdate(json!({
                    "id": format!("f{}", flaw_id),
                    "status": sat.value(var).to_json()
                })));
            }
        });
        self.flaw_q.push_back(flaw);
    }

    pub fn add_resolver(&mut self, resolver: Rc<dyn Resolver>) {
        trace!("Adding resolver: {:?}", resolver.id());
        let _ = self.tx_event.send(SolverEvent::NewResolver(resolver.to_json()));
        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        if solver.sat.borrow().value(resolver.rho()) == &LBool::True {
            let mut active_flaws = self.active_flaws.borrow_mut();
            if active_flaws.remove(&resolver.flaw()) {
                trace!("Flaw {:?} resolved by resolver {:?}.", resolver.flaw(), resolver.id());
                trace!("Active flaws count: {}", active_flaws.len());
            }
        }
        self.resolvers.push(resolver.clone());
        solver.sat.borrow_mut().add_listener(resolver.rho(), {
            let resolver_id = resolver.id();
            let tx_event = self.tx_event.clone();
            let to_recompute = self.to_recompute.clone();
            move |sat, var| {
                if sat.value(var) == &LBool::False {
                    to_recompute.borrow_mut().insert(resolver.flaw());
                }
                let _ = tx_event.send(SolverEvent::ResolverStatusUpdate(json!({
                    "id": format!("r{}", resolver_id),
                    "status": sat.value(var).to_json()
                })));
            }
        });
    }

    pub(crate) fn set_current_flaw(&mut self, flaw: Option<Rc<dyn Flaw>>) {
        self.c_flaw.clone_from(&flaw);
        if let Some(flaw) = flaw {
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(json!({"id": format!("f{}", flaw.id())})));
        } else {
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Value::Null));
        }
    }

    pub(crate) fn set_current_resolver(&mut self, resolver: Option<Rc<dyn Resolver>>) {
        self.c_res.clone_from(&resolver);
        if let Some(resolver) = resolver {
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(json!({"id": format!("r{}", resolver.id())})));
        } else {
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(Value::Null));
        }
    }

    pub(crate) fn get_current_resolver(&self) -> Option<Rc<dyn Resolver>> {
        self.c_res.clone()
    }

    pub fn get_num_flaws(&self) -> usize {
        self.flaws.len()
    }

    pub fn get_num_resolvers(&self) -> usize {
        self.resolvers.len()
    }

    pub fn get_most_expensive_flaw(&self) -> Option<Rc<dyn Flaw>> {
        self.active_flaws.borrow().iter().filter_map(|id| self.flaws.get(*id).cloned()).max_by_key(|flaw| flaw.cost())
    }

    pub fn get_least_expensive_resolver(&self, flaw: &dyn Flaw) -> Option<Rc<dyn Resolver>> {
        flaw.resolvers().iter().filter_map(|id| self.resolvers.get(*id).cloned()).min_by_key(|resolver| self.compute_resolver_cost(resolver.as_ref()))
    }
}

impl ToJson for LBool {
    fn to_json(&self) -> Value {
        match self {
            LBool::True => true.into(),
            LBool::False => false.into(),
            LBool::Undef => Value::Null,
        }
    }
}

impl ToJson for Graph {
    fn to_json(&self) -> Value {
        let mut obj = json!({
            "flaws": self.flaws.iter().map(|f| f.to_json()).collect::<Vec<_>>(),
            "resolvers": self.resolvers.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
        });
        if let Some(current_flaw) = self.c_flaw.as_ref() {
            obj["current_flaw"] = current_flaw.id().into();
        }
        if let Some(current_resolver) = self.c_res.as_ref() {
            obj["current_resolver"] = current_resolver.id().into();
        }
        obj
    }
}
