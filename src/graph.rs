use crate::{SolverError, SolverState};
use semitone::{DlVar, Lit};
use serde_json::Value;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    ops::{Index, IndexMut},
    rc::Rc,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct FlawId(usize);

impl FlawId {
    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0
    }
}

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ResolverId(usize);

impl ResolverId {
    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0
    }
}

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
    fn expand(&self, slv: &SolverState, flw_id: FlawId) -> Result<(), SolverError>;

    /// Serializes the domain-specific payload of this flaw to JSON.
    fn to_json(&self) -> Value;
}

pub trait Resolver {
    /// The intrinsic cost of selecting this resolver, independent from the current state of the graph.
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(1)
    }

    /// Applies this resolver, adding its constraints, sub-flaws, or causal links to the solver state.
    fn apply(&self, _slv: &SolverState, _res_id: ResolverId) -> Result<(), SolverError> {
        Ok(())
    }

    /// Serializes the domain-specific payload of this resolver to JSON.
    fn to_json(&self) -> Value {
        Value::Null
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FlawState {
    Queued,
    Expanding,
    Expanded,
}

pub(crate) struct FlawData {
    pub(crate) phi: Lit,
    pub(crate) cost_var: DlVar,
    pub(crate) state: FlawState,
    /// Sorted and deduplicated causal parents of this flaw.
    pub(crate) causes: Vec<ResolverId>,
    pub(crate) resolvers: Vec<ResolverId>,
    pub(crate) payload: Rc<dyn Flaw>,
}

pub(crate) struct ResolverData {
    pub(crate) rho: Lit,
    pub(crate) flaw: FlawId,
    pub(crate) cost_var: DlVar,
    pub(crate) intrinsic_cost: f64,
    /// Single-cause flaws directly required by this resolver.
    pub(crate) preconditions: Vec<FlawId>,
    /// Optional causal link target resolver (e.g., `UnificationResolver -> target_sigma_res`).
    pub(crate) causal_link: Option<ResolverId>,
    pub(crate) payload: Rc<dyn Resolver>,
}

/// Static AND/OR causal graph topology. Only mutated at decision level 0.
pub(crate) struct CausalGraph {
    flaws: Vec<FlawData>,
    resolvers: Vec<ResolverData>,
    lit_to_flaws: HashMap<Lit, Vec<FlawId>>,
    lit_to_resolvers: HashMap<Lit, Vec<ResolverId>>,
    /// FIFO queue of flaws in `FlawState::Queued` (preserves BFS expansion order).
    frontier: VecDeque<FlawId>,
}

impl CausalGraph {
    pub(crate) fn new() -> Self {
        Self {
            flaws: Vec::new(),
            resolvers: Vec::new(),
            lit_to_flaws: HashMap::new(),
            lit_to_resolvers: HashMap::new(),
            frontier: VecDeque::new(),
        }
    }

    pub(crate) fn add_flaw(&mut self, mut causes: Vec<ResolverId>, phi: Lit, cost_var: DlVar, payload: Rc<dyn Flaw>) -> FlawId {
        causes.sort_unstable();
        causes.dedup();

        let flw_id = FlawId(self.flaws.len());
        if let &[cause] = causes.as_slice() {
            self.resolvers[cause].preconditions.push(flw_id);
        }

        self.flaws.push(FlawData { phi, cost_var, state: FlawState::Queued, causes, resolvers: Vec::new(), payload });
        self.lit_to_flaws.entry(phi).or_default().push(flw_id);
        self.frontier.push_back(flw_id);

        flw_id
    }

    pub(crate) fn add_resolver(&mut self, flaw: FlawId, rho: Lit, cost_var: DlVar, payload: Rc<dyn Resolver>) -> ResolverId {
        debug_assert_eq!(self.flaws[flaw].state, FlawState::Expanding, "Resolvers can only be added while expanding their flaw");

        let res_id = ResolverId(self.resolvers.len());
        let intrinsic_cost = payload.intrinsic_cost().to_f64();

        self.resolvers.push(ResolverData { rho, flaw, cost_var, intrinsic_cost, preconditions: Vec::new(), causal_link: None, payload });
        self.flaws[flaw].resolvers.push(res_id);
        self.lit_to_resolvers.entry(rho).or_default().push(res_id);

        res_id
    }

    pub(crate) fn add_causal_link(&mut self, res: ResolverId, target: ResolverId) {
        assert!(self.resolvers[res].causal_link.is_none(), "Resolver {} already has a causal link", res);
        debug_assert!(self.resolvers[target].causal_link.is_none(), "Chained causal links are not supported");
        self.resolvers[res].causal_link = Some(target);
    }

    /// Transitions `flw_id` from `Queued` to `Expanding`, removing it from the frontier.
    pub(crate) fn begin_expand(&mut self, flw_id: FlawId) -> Rc<dyn Flaw> {
        debug_assert_eq!(self.flaws[flw_id].state, FlawState::Queued, "Flaw {} is not queued for expansion", flw_id);
        if let Some(pos) = self.frontier.iter().position(|&id| id == flw_id) {
            self.frontier.remove(pos);
        }
        self.flaws[flw_id].state = FlawState::Expanding;
        Rc::clone(&self.flaws[flw_id].payload)
    }

    /// Transitions `flw_id` from `Expanding` to `Expanded`.
    pub(crate) fn finish_expand(&mut self, flw_id: FlawId) {
        debug_assert_eq!(self.flaws[flw_id].state, FlawState::Expanding, "Flaw {} is not currently expanding", flw_id);
        self.flaws[flw_id].state = FlawState::Expanded;
    }

    #[inline]
    pub(crate) fn flaw_count(&self) -> usize {
        self.flaws.len()
    }

    #[inline]
    pub(crate) fn resolver_count(&self) -> usize {
        self.resolvers.len()
    }

    #[inline]
    pub(crate) fn flaw(&self, id: FlawId) -> &FlawData {
        &self.flaws[id]
    }

    #[inline]
    pub(crate) fn resolver(&self, id: ResolverId) -> &ResolverData {
        &self.resolvers[id]
    }

    pub(crate) fn flaw_ids(&self) -> impl Iterator<Item = FlawId> {
        (0..self.flaws.len()).map(FlawId)
    }

    pub(crate) fn resolver_ids(&self) -> impl Iterator<Item = ResolverId> {
        (0..self.resolvers.len()).map(ResolverId)
    }

    pub(crate) fn flaws_by_lit(&self, lit: Lit) -> &[FlawId] {
        self.lit_to_flaws.get(&lit).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(crate) fn resolvers_by_lit(&self, lit: Lit) -> &[ResolverId] {
        self.lit_to_resolvers.get(&lit).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(crate) fn rhos(&self, res_ids: &[ResolverId]) -> Vec<Lit> {
        res_ids.iter().map(|&r| self.resolvers[r].rho).collect()
    }

    #[inline]
    pub(crate) fn frontier(&self) -> &VecDeque<FlawId> {
        &self.frontier
    }

    #[inline]
    pub(crate) fn is_expanded(&self, id: FlawId) -> bool {
        self.flaws[id].state == FlawState::Expanded
    }

    /// Snapshot of all currently `Queued` flaws sharing `phi`, in insertion order.
    pub(crate) fn queued_flaws_for_phi(&self, phi: Lit) -> Vec<FlawId> {
        self.flaws_by_lit(phi).iter().copied().filter(|&f| self.flaws[f].state == FlawState::Queued).collect()
    }

    /// Returns `true` if every flaw sharing `phi` has finished expanding.
    pub(crate) fn is_phi_fully_expanded(&self, phi: Lit) -> bool {
        self.flaws_by_lit(phi).iter().all(|&f| self.flaws[f].state == FlawState::Expanded)
    }

    /// Dereferences an optional causal link to `(effective_resolver, total_intrinsic_cost)`.
    #[inline]
    pub(crate) fn effective_resolver(&self, r: ResolverId) -> (ResolverId, f64) {
        let data = &self.resolvers[r];
        if let Some(target) = data.causal_link { (target, data.intrinsic_cost + self.resolvers[target].intrinsic_cost) } else { (r, data.intrinsic_cost) }
    }

    /// Returns `true` if `anc` is a causal ancestor of `flw` along `causes`.
    pub(crate) fn is_ancestor(&self, anc: ResolverId, flw: FlawId) -> bool {
        let mut queue = VecDeque::from([flw]);
        let mut visited = HashSet::new();

        while let Some(f_id) = queue.pop_front() {
            if !visited.insert(f_id) {
                continue;
            }
            for &c_res in &self.flaws[f_id].causes {
                if c_res == anc {
                    return true;
                }
                queue.push_back(self.resolvers[c_res].flaw);
            }
        }

        false
    }
}
