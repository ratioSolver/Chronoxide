use crate::{
    ToJson,
    flaws::{Flaw, Resolver},
    solver::{SolverEvent, SolverState},
};
use consensus::LBool;
use linspire::rational::Rational;
use riddle::serde_json::{Value, json};
use std::{
    collections::{HashSet, VecDeque},
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;
use tracing::trace;

pub(crate) struct Graph {
    slv: Weak<SolverState>,
    flaws: Vec<Rc<dyn Flaw>>,
    resolvers: Vec<Rc<dyn Resolver>>,
    flaw_q: VecDeque<Rc<dyn Flaw>>,
    c_flaw: Option<Rc<dyn Flaw>>,
    c_res: Option<Rc<dyn Resolver>>,
    active_flaws: HashSet<usize>,
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
            active_flaws: HashSet::new(),
            tx_event,
        }
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
        if self.slv.upgrade().expect("SolverState has been dropped").sat.borrow().value(flaw.phi()) == &LBool::True {
            self.active_flaws.insert(flaw.id());
            trace!("Active flaws count: {}", self.active_flaws.len());
        }
        self.flaws.push(flaw.clone());
        self.flaw_q.push_back(flaw);
    }

    pub fn add_resolver(&mut self, resolver: Rc<dyn Resolver>) {
        trace!("Adding resolver: {:?}", resolver.id());
        let _ = self.tx_event.send(SolverEvent::NewResolver(resolver.to_json()));
        if self.slv.upgrade().expect("SolverState has been dropped").sat.borrow().value(resolver.rho()) == &LBool::True {
            if self.active_flaws.remove(&resolver.flaw()) {
                trace!("Flaw {:?} resolved by resolver {:?}.", resolver.flaw(), resolver.id());
                trace!("Active flaws count: {}", self.active_flaws.len());
            }
        }
        self.resolvers.push(resolver);
    }

    fn set_current_flaw(&mut self, flaw: Option<Rc<dyn Flaw>>) {
        self.c_flaw.clone_from(&flaw);
        if let Some(flaw) = flaw {
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(json!({"id": format!("f{}", flaw.id())})));
        } else {
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Value::Null));
        }
    }

    fn set_current_resolver(&mut self, resolver: Option<Rc<dyn Resolver>>) {
        self.c_res.clone_from(&resolver);
        if let Some(resolver) = resolver {
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(json!({"id": format!("r{}", resolver.id())})));
        } else {
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(Value::Null));
        }
    }
}
