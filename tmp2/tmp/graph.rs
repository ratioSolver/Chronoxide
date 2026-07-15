use crate::{
    ToJson,
    flaws::{Flaw, FlawId, Resolver, ResolverId},
    solver::{SolverEvent, SolverState},
};
use linarith::Rational;
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{HashSet, VecDeque},
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;
use tracing::trace;
use watchsat::{LBool, neg, pos};

pub struct Graph {
    slv: Weak<SolverState>,
    flaws: Vec<Rc<dyn Flaw>>,
    resolvers: Vec<Rc<dyn Resolver>>,
    flaw_q: VecDeque<FlawId>,
    active_flaws: Rc<RefCell<HashSet<FlawId>>>,
    to_recompute: Rc<RefCell<HashSet<FlawId>>>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl Graph {
    pub(crate) fn new(slv: Weak<SolverState>, tx_event: broadcast::Sender<SolverEvent>) -> Self {
        Self {
            slv,
            flaws: Vec::new(),
            resolvers: Vec::new(),
            flaw_q: VecDeque::new(),
            active_flaws: Rc::new(RefCell::new(HashSet::new())),
            to_recompute: Rc::new(RefCell::new(HashSet::new())),
            tx_event,
        }
    }

    pub(crate) fn build_graph(&mut self) -> bool {
        trace!("Building graph...");
        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        while self.active_flaws.borrow().iter().any(|flaw| self.flaws.get(**flaw).expect("Invalid flaw ID").cost().is_infinite()) {
            if let Some(flaw) = self.flaw_q.pop_front() {
                let flaw = self.flaws.get(*flaw).expect("Invalid flaw ID").clone();
                trace!("Processing flaw: {}", flaw);
                let mut causal_constraint = Vec::new();
                causal_constraint.push(neg(flaw.phi()));
                for resolver in flaw.clone().compute_resolvers(ResolverId(self.resolvers.len())) {
                    self.add_resolver(resolver.clone());
                    causal_constraint.push(pos(resolver.rho()));
                    solver.set_current_resolver(Some(resolver.clone()));
                    trace!("Applying resolver {}", resolver);
                    match resolver.apply() {
                        Ok(_) => trace!("Resolver applied successfully."),
                        Err(e) => {
                            trace!("Failed to apply resolver with error: {:?}", e);
                            return false;
                        }
                    }
                }
                solver.set_current_resolver(None);
                match solver.sat.borrow_mut().add_clause(causal_constraint) {
                    Ok(_) => trace!("Causal constraint added successfully"),
                    Err(e) => {
                        trace!("Failed to add causal constraint with error: {:?}", e);
                        return false;
                    }
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

    pub(crate) fn update_costs(&mut self) {
        trace!("Recomputing costs for flaws: {}", self.to_recompute.borrow().iter().map(|id| id.to_string()).collect::<Vec<_>>().join(", "));
        let to_recompute = self.to_recompute.borrow().clone();
        for flaw_id in to_recompute {
            if let Some(flaw) = self.flaws.get(*flaw_id).cloned() {
                self.compute_flaw_cost(flaw);
            }
        }
        self.to_recompute.borrow_mut().clear();
    }

    fn compute_flaw_cost(&mut self, flaw: Rc<dyn Flaw>) {
        trace!("Computing cost for flaw: {}", flaw.id());
        let mut stack: Vec<(Rc<dyn Flaw>, HashSet<FlawId>)> = vec![(flaw, HashSet::new())];

        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        while let Some((flaw, mut visited)) = stack.pop() {
            let mut current_cost = Rational::POSITIVE_INFINITY;

            if solver.sat.borrow().value(flaw.phi()) != LBool::False && visited.insert(flaw.id()) {
                for resolver_id in flaw.resolvers() {
                    let resolver = self.resolvers.get(*resolver_id).expect("Invalid resolver ID").clone();
                    if solver.sat.borrow().value(resolver.rho()) != LBool::False {
                        let resolver_cost = self.compute_resolver_cost(resolver.as_ref());
                        if resolver_cost < current_cost {
                            current_cost = resolver_cost;
                        }
                    }
                }
            }

            if flaw.cost() != current_cost {
                trace!("Updating cost for flaw {} from {} to {}", flaw.id(), flaw.cost(), current_cost);
                flaw.set_cost(current_cost);
                let _ = self.tx_event.send(SolverEvent::FlawCostUpdate({
                    let mut msg = flaw.to_json();
                    msg["id"] = format!("f{}", flaw.id()).into();
                    msg["cost"] = current_cost.to_json();
                    msg
                }));

                for support in flaw.supports() {
                    let support = self.resolvers.get(*support).expect("Invalid flaw cause");
                    let support_flaw = self.flaws.get(*support.flaw()).expect("Invalid flaw cause").clone();
                    stack.push((support_flaw, visited.clone()));
                }
            }
        }
    }

    fn compute_resolver_cost(&self, resolver: &dyn Resolver) -> Rational {
        resolver.requirements().iter().map(|flaw| self.flaws.get(**flaw).expect("Invalid resolver requirement").cost()).fold(resolver.intrinsic_cost(), |max_cost, c| if c > max_cost { c } else { max_cost })
    }

    pub fn add_flaw(&mut self, flaw: Rc<dyn Flaw>) {
        trace!("Adding flaw: {}", flaw);
        let _ = self.tx_event.send(SolverEvent::NewFlaw(flaw.to_json()));
        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        if solver.sat.borrow().value(flaw.phi()) == LBool::True {
            let mut active_flaws = self.active_flaws.borrow_mut();
            active_flaws.insert(flaw.id());
            trace!("Active flaws count: {}", active_flaws.len());
        }
        solver.sat.borrow_mut().add_listener(flaw.phi(), {
            let flaw_id = flaw.id();
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
                let _ = tx_event.send(SolverEvent::FlawStatusUpdate(json!({
                    "id": format!("f{}", flaw_id),
                    "status": val.to_json()
                })));
            }
        });
        self.flaw_q.push_back(flaw.id());
        self.flaws.push(flaw.clone());
    }

    pub fn add_resolver(&mut self, resolver: Rc<dyn Resolver>) {
        trace!("Adding resolver: {}", resolver);
        let _ = self.tx_event.send(SolverEvent::NewResolver(resolver.to_json()));
        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        if solver.sat.borrow().value(resolver.rho()) == LBool::True {
            let mut active_flaws = self.active_flaws.borrow_mut();
            if active_flaws.remove(&resolver.flaw()) {
                trace!("Flaw {} resolved by resolver {}.", resolver.flaw(), resolver.id());
                trace!("Active flaws count: {}", active_flaws.len());
            }
        }
        let solver_for_listener = solver.clone();
        let active_flaws = self.active_flaws.clone();
        solver.sat.borrow_mut().add_listener(resolver.rho(), {
            let resolver_id = resolver.id();
            let resolver_flaw = resolver.flaw();
            let resolver_ac_constraints = resolver.ac_constraints();
            let tx_event = self.tx_event.clone();
            let to_recompute = self.to_recompute.clone();
            move |_var, val| {
                match val {
                    LBool::True => {
                        if let Some(constrs) = &resolver_ac_constraints {
                            match solver_for_listener.ac.borrow_mut().assert_batch(&constrs) {
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
                let _ = tx_event.send(SolverEvent::ResolverStatusUpdate(json!({
                    "id": format!("r{}", resolver_id),
                    "status": val.to_json()
                })));
            }
        });
        self.resolvers.push(resolver);
    }

    pub fn get_flaw(&self, id: usize) -> Option<Rc<dyn Flaw>> {
        self.flaws.get(id).cloned()
    }

    pub fn get_num_flaws(&self) -> usize {
        self.flaws.len()
    }

    pub fn get_num_resolvers(&self) -> usize {
        self.resolvers.len()
    }

    pub fn get_most_expensive_flaw(&self) -> Option<Rc<dyn Flaw>> {
        self.active_flaws.borrow().iter().filter_map(|id| self.flaws.get(**id).cloned()).max_by_key(|flaw| flaw.cost())
    }

    pub fn get_least_expensive_resolver(&self, flaw: &dyn Flaw) -> Option<Rc<dyn Resolver>> {
        flaw.resolvers()
            .iter()
            .filter_map(|id| {
                let res = self.resolvers.get(**id).cloned();
                if let Some(resolver) = &res {
                    let solver = self.slv.upgrade().expect("SolverState has been dropped");
                    if solver.sat.borrow().value(resolver.rho()) == LBool::False {
                        return None;
                    }
                }
                res
            })
            .min_by_key(|resolver| self.compute_resolver_cost(resolver.as_ref()))
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
        json!({
            "flaws": self.flaws.iter().map(|f| f.to_json()).collect::<Vec<_>>(),
            "resolvers": self.resolvers.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
        })
    }
}
