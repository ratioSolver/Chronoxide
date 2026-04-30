use crate::{
    ToJson,
    flaws::{Flaw, Resolver},
    solver::{self, SolverEvent, SolverState},
};
use consensus::LBool;
use linspire::rational::Rational;
use riddle::serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::{HashSet, VecDeque},
    rc::{Rc, Weak},
};
use tokio::sync::broadcast;
use tracing::trace;

pub(crate) struct Graph {
    slv: Weak<SolverState>,
    flaws: RefCell<Vec<Rc<dyn Flaw>>>,
    resolvers: RefCell<Vec<Rc<dyn Resolver>>>,
    flaw_q: RefCell<VecDeque<Rc<dyn Flaw>>>,
    c_flaw: RefCell<Option<Rc<dyn Flaw>>>,
    c_res: RefCell<Option<Rc<dyn Resolver>>>,
    active_flaws: RefCell<HashSet<usize>>,
    tx_event: broadcast::Sender<SolverEvent>,
}

impl Graph {
    pub(crate) fn new(slv: Weak<SolverState>, tx_event: broadcast::Sender<SolverEvent>) -> Self {
        Self {
            slv,
            flaws: RefCell::new(Vec::new()),
            resolvers: RefCell::new(Vec::new()),
            flaw_q: RefCell::new(VecDeque::new()),
            c_flaw: RefCell::new(None),
            c_res: RefCell::new(None),
            active_flaws: RefCell::new(HashSet::new()),
            tx_event,
        }
    }

    fn compute_flaw_cost(&self, flaw: Rc<dyn Flaw>) {
        trace!("Computing cost for flaw: {:?}", flaw.id());
        let mut stack: Vec<(Rc<dyn Flaw>, HashSet<usize>)> = vec![(flaw, HashSet::new())];

        let solver = self.slv.upgrade().expect("SolverState has been dropped");
        let resolvers = self.resolvers.borrow();
        let flaws = self.flaws.borrow();
        while let Some((flaw, mut visited)) = stack.pop() {
            let mut current_cost = Rational::POSITIVE_INFINITY;

            if solver.sat.borrow().value(flaw.phi()) != &LBool::False && visited.insert(flaw.id()) {
                for resolver_id in flaw.resolvers() {
                    let resolver = self.resolvers.borrow().get(resolver_id).expect("Invalid resolver ID").clone();
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
                    let support = resolvers.get(support).expect("Invalid flaw cause");
                    let support_flaw = flaws.get(support.flaw()).expect("Invalid flaw cause").clone();
                    stack.push((support_flaw, visited.clone()));
                }
            }
        }
    }

    fn compute_resolver_cost(&self, resolver: &dyn Resolver) -> Rational {
        resolver.requirements().iter().map(|flaw| self.flaws.borrow().get(*flaw).expect("Invalid resolver requirement").cost()).fold(resolver.intrinsic_cost(), |max_cost, c| if c > max_cost { c } else { max_cost })
    }

    pub fn add_flaw(&self, flaw: Rc<dyn Flaw>) {
        trace!("Adding flaw: {:?}", flaw.id());
        let _ = self.tx_event.send(SolverEvent::NewFlaw(flaw.to_json()));
        if self.slv.upgrade().expect("SolverState has been dropped").sat.borrow().value(flaw.phi()) == &LBool::True {
            self.active_flaws.borrow_mut().insert(flaw.id());
            trace!("Active flaws count: {}", self.active_flaws.borrow().len());
        }
        self.flaws.borrow_mut().push(flaw.clone());
        self.flaw_q.borrow_mut().push_back(flaw);
    }

    pub fn add_resolver(&self, resolver: Rc<dyn Resolver>) {
        trace!("Adding resolver: {:?}", resolver.id());
        let _ = self.tx_event.send(SolverEvent::NewResolver(resolver.to_json()));
        if self.slv.upgrade().expect("SolverState has been dropped").sat.borrow().value(resolver.rho()) == &LBool::True {
            if self.active_flaws.borrow_mut().remove(&resolver.flaw()) {
                trace!("Flaw {:?} resolved by resolver {:?}.", resolver.flaw(), resolver.id());
                trace!("Active flaws count: {}", self.active_flaws.borrow().len());
            }
        }
        self.resolvers.borrow_mut().push(resolver);
    }

    fn set_current_flaw(&self, flaw: Option<Rc<dyn Flaw>>) {
        self.c_flaw.borrow_mut().clone_from(&flaw);
        if let Some(flaw) = flaw {
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(json!({"id": format!("f{}", flaw.id())})));
        } else {
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Value::Null));
        }
    }

    fn set_current_resolver(&self, resolver: Option<Rc<dyn Resolver>>) {
        self.c_res.borrow_mut().clone_from(&resolver);
        if let Some(resolver) = resolver {
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(json!({"id": format!("r{}", resolver.id())})));
        } else {
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(Value::Null));
        }
    }
}
