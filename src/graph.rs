use crate::{SolverError, SolverEvent, SolverState};
use semitone::{DlVar, Lit};
use serde_json::Value;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    ops::{Index, IndexMut},
};
use tokio::sync::broadcast;
use tracing::trace;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct FlawId(usize);

impl<T> Index<FlawId> for Vec<T> {
    type Output = T;
    fn index(&self, flw: FlawId) -> &Self::Output {
        &self[flw.0]
    }
}

impl<T> IndexMut<FlawId> for Vec<T> {
    fn index_mut(&mut self, flw: FlawId) -> &mut Self::Output {
        &mut self[flw.0]
    }
}

impl fmt::Display for FlawId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ϕ{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ResolverId(usize);

impl<T> Index<ResolverId> for Vec<T> {
    type Output = T;
    fn index(&self, res: ResolverId) -> &Self::Output {
        &self[res.0]
    }
}

impl<T> IndexMut<ResolverId> for Vec<T> {
    fn index_mut(&mut self, res: ResolverId) -> &mut Self::Output {
        &mut self[res.0]
    }
}

impl fmt::Display for ResolverId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ρ{}", self.0)
    }
}

pub trait Flaw {
    /// Expands this flaw by adding resolvers to the graph that can potentially solve it.
    fn expand(&mut self, slv: &SolverState) -> Result<(), SolverError>;

    /// Serializes the domain-specific payload of this flaw to JSON.
    fn to_json(&self) -> Value;
}

pub trait Resolver {
    /// The intrinsic cost of selecting this resolver, independent from the current state of the graph.
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(1)
    }

    /// Applies this resolver, adding its constraints, sub-flaws, or causal links to the solver state.
    fn apply(&mut self, _slv: &SolverState) -> Result<(), SolverError> {
        Ok(())
    }

    /// Serializes the domain-specific payload of this resolver to JSON.
    fn to_json(&self) -> Value {
        Value::Null
    }
}

pub struct Graph {
    flaws: Vec<Option<Box<dyn Flaw>>>,
    resolvers: Vec<Option<Box<dyn Resolver>>>,
    c_flaw: Option<(FlawId, Lit)>,
    c_res: Option<(ResolverId, Lit)>,

    lit_to_flaws: HashMap<Lit, Vec<FlawId>>,
    flaw_status: Vec<Option<bool>>,
    flaw_phi: Vec<Lit>,
    flaw_cost_var: Vec<DlVar>,
    flaw_causes: Vec<Vec<ResolverId>>,
    flaw_required_by: Vec<Vec<ResolverId>>,
    flaw_resolvers: Vec<Vec<ResolverId>>,
    flaw_cost: Vec<f64>,

    lit_to_resolvers: HashMap<Lit, Vec<ResolverId>>,
    resolver_status: Vec<Option<bool>>,
    resolver_rho: Vec<Lit>,
    resolver_cost_var: Vec<DlVar>,
    resolver_flaw: Vec<FlawId>,
    resolver_preconditions: Vec<Vec<FlawId>>,

    flaw_q: VecDeque<FlawId>,
    agenda: HashSet<FlawId>,

    tx_event: broadcast::Sender<SolverEvent>,
}

impl Graph {
    pub(super) fn new(tx_event: broadcast::Sender<SolverEvent>) -> Self {
        Self {
            flaws: Vec::new(),
            resolvers: Vec::new(),
            c_flaw: None,
            c_res: None,

            lit_to_flaws: HashMap::new(),
            flaw_status: Vec::new(),
            flaw_phi: Vec::new(),
            flaw_cost_var: Vec::new(),
            flaw_causes: Vec::new(),
            flaw_required_by: Vec::new(),
            flaw_resolvers: Vec::new(),
            flaw_cost: Vec::new(),

            lit_to_resolvers: HashMap::new(),
            resolver_status: Vec::new(),
            resolver_rho: Vec::new(),
            resolver_cost_var: Vec::new(),
            resolver_flaw: Vec::new(),
            resolver_preconditions: Vec::new(),

            flaw_q: VecDeque::new(),
            agenda: HashSet::new(),

            tx_event,
        }
    }

    /// Returns the currently processing flaw and its ϕ literal, if any.
    pub(super) fn current_flaw(&self) -> Option<(FlawId, Lit)> {
        self.c_flaw
    }

    /// Returns the currently processing resolver and its ρ literal, if any.
    pub(super) fn current_resolver(&self) -> Option<(ResolverId, Lit)> {
        self.c_res
    }

    /// Returns the currently active resolver as a cause vector (empty if at root level).
    pub(super) fn current_causes(&self) -> Vec<ResolverId> {
        self.c_res.map(|(r_id, _)| vec![r_id]).unwrap_or_default()
    }

    /// Adds a new flaw to the graph, returning its FlawId.
    pub fn add_flaw(&mut self, causes: Vec<ResolverId>, phi: Lit, status: Option<bool>, cost_var: DlVar, flw: Box<dyn Flaw>) -> FlawId {
        let flw_id = FlawId(self.flaws.len());
        trace!("Adding flaw: {} ({})", flw_id, phi);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewFlaw {
            flaw_id: flw_id,
            phi: phi.to_string(),
            causes: causes.clone(),
            required_by: causes.clone(),
            status,
            cost: f64::INFINITY,
            data: flw.to_json(),
        });

        self.flaws.push(Some(flw));
        self.flaw_phi.push(phi);
        self.flaw_status.push(status);
        if status == Some(true) {
            self.agenda.insert(flw_id);
            trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
        }
        self.flaw_cost_var.push(cost_var);
        for &cause in &causes {
            self.resolver_preconditions[cause].push(flw_id);
        }
        self.flaw_causes.push(causes);
        self.flaw_required_by.push(Vec::new());
        self.flaw_resolvers.push(Vec::new());
        self.flaw_cost.push(f64::INFINITY);

        self.lit_to_flaws.entry(phi).or_default().push(flw_id);

        flw_id
    }

    /// Returns the ϕ literal of the given flaw.
    pub(super) fn phi(&self, flw_id: FlawId) -> Lit {
        self.flaw_phi[flw_id]
    }

    pub(super) fn take_flaw(&mut self, flw_id: FlawId) -> Option<Box<dyn Flaw>> {
        self.c_flaw.replace((flw_id, self.flaw_phi[flw_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));
        self.flaws[flw_id].take()
    }

    pub(super) fn return_flaw(&mut self, flw: Box<dyn Flaw>) {
        let (flw_id, _) = self.c_flaw.take().expect("A flaw must be checked out when calling return_flaw");
        self.flaws[flw_id] = Some(flw);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
    }

    pub fn add_resolver(&mut self, rho: Lit, status: Option<bool>, cost: DlVar, res: Box<dyn Resolver>) -> ResolverId {
        let (flaw_id, _) = self.c_flaw.expect("Cannot add a resolver when no flaw is currently being processed");
        let res_id = ResolverId(self.resolvers.len());
        trace!("Adding resolver: {} ({}) for flaw {}", res_id, rho, flaw_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: res_id,
            flaw_id,
            rho: rho.to_string(),
            status,
            intrinsic_cost: res.intrinsic_cost().to_f64(),
            preconditions: Vec::new(),
            data: res.to_json(),
        });

        self.resolvers.push(Some(res));
        self.resolver_rho.push(rho);
        self.resolver_status.push(status);
        if status == Some(true) {
            self.agenda.remove(&flaw_id);
            trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id });
        }
        self.resolver_cost_var.push(cost);
        self.resolver_flaw.push(flaw_id);
        self.resolver_preconditions.push(Vec::new());
        self.flaw_resolvers[flaw_id].push(res_id);

        self.lit_to_resolvers.entry(rho).or_default().push(res_id);

        res_id
    }

    /// Returns the ρ literal of the given resolver.
    pub(super) fn rho(&self, res_id: ResolverId) -> Lit {
        self.resolver_rho[res_id]
    }

    /// Returns the ρ literals of the given resolvers.
    pub(super) fn rhos(&self, res_ids: &[ResolverId]) -> Vec<Lit> {
        res_ids.iter().map(|&r_id| self.resolver_rho[r_id]).collect()
    }

    pub(super) fn take_resolver(&mut self, res_id: ResolverId) -> Option<Box<dyn Resolver>> {
        self.c_res.replace((res_id, self.resolver_rho[res_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(res_id)));
        self.resolvers[res_id].take()
    }

    pub(super) fn return_resolver(&mut self, res: Box<dyn Resolver>) {
        let (res_id, _) = self.c_res.take().expect("A resolver must be checked out when calling return_resolver");
        self.resolvers[res_id] = Some(res);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
    }
}
