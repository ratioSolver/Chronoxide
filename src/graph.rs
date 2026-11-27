use crate::{SolverError, SolverEvent, SolverState};
use semitone::{DlVar, Lit};
use serde_json::Value;
use std::{
    cmp::Ordering,
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

#[derive(Clone, Default)]
struct BitSet {
    words: Vec<u64>,
}

impl BitSet {
    #[inline]
    fn set(&mut self, idx: usize) {
        let word = idx >> 6;
        if word >= self.words.len() {
            self.words.resize(word + 1, 0);
        }
        self.words[word] |= 1u64 << (idx & 63);
    }

    #[inline]
    fn contains(&self, idx: usize) -> bool {
        let word = idx >> 6;
        word < self.words.len() && (self.words[word] & (1u64 << (idx & 63))) != 0
    }

    fn iter_ones(&self) -> impl Iterator<Item = usize> + '_ {
        self.words.iter().enumerate().flat_map(|(w_idx, &word)| BitIter { word, base: w_idx << 6 })
    }
}

struct BitIter {
    word: u64,
    base: usize,
}

impl Iterator for BitIter {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.word == 0 {
            return None;
        }
        let tz = self.word.trailing_zeros() as usize;
        self.word &= self.word - 1;
        Some(self.base + tz)
    }
}

pub trait Flaw {
    /// Expands this flaw by adding resolvers to the graph that can potentially solve it.
    fn expand(&self, slv: &SolverState) -> Result<(), SolverError>;

    /// Serializes the domain-specific payload of this flaw to JSON.
    fn to_json(&self) -> Value;
}

pub trait Resolver {
    /// The intrinsic cost of selecting this resolver, independent from the current state of the graph.
    fn intrinsic_cost(&self) -> rug::Rational {
        rug::Rational::from(1)
    }

    /// Applies this resolver, adding its constraints, sub-flaws, or causal links to the solver state.
    fn apply(&self, _slv: &SolverState) -> Result<(), SolverError> {
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
    flaw_expanded: Vec<bool>,
    flaw_phi: Vec<Lit>,
    flaw_cost_var: Vec<DlVar>,
    flaw_causes: Vec<Vec<ResolverId>>,
    flaw_resolvers: Vec<Vec<ResolverId>>,

    /// Lower-triangular h^2 pair-cost matrix (`flaw_pair_cost[hi.0][lo.0]` for `lo <= hi`).
    flaw_pair_cost: Vec<Vec<f64>>,
    h2_dirty: bool,

    lit_to_resolvers: HashMap<Lit, Vec<ResolverId>>,
    resolver_status: Vec<Option<bool>>,
    resolver_rho: Vec<Lit>,
    resolver_cost_var: Vec<DlVar>,
    resolver_intrinsic_cost: Vec<f64>,
    resolver_flaw: Vec<FlawId>,
    /// Single-cause flaws directly required by a resolver.
    resolver_preconditions: Vec<Vec<FlawId>>,
    /// Two-cause flaws (e.g., binary timeline peaks) jointly required by a pair of resolvers.
    pair_preconditions: HashMap<(ResolverId, ResolverId), Vec<FlawId>>,
    /// Causal link target resolver (`UnificationResolver -> target_sigma_res`).
    resolver_linked_to: Vec<Option<ResolverId>>,
    /// Direct impliers of a resolver (resolvers of caused flaws + causal links pointing here).
    resolver_impliers: Vec<Vec<ResolverId>>,
    /// Symmetric, downward-closed resolver mutex relation (structural + learned).
    res_mutex: Vec<BitSet>,
    /// Cache of agenda resolver pairs already probed at level 0.
    probed_pairs: HashSet<(ResolverId, ResolverId)>,

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
            flaw_expanded: Vec::new(),
            flaw_phi: Vec::new(),
            flaw_cost_var: Vec::new(),
            flaw_causes: Vec::new(),
            flaw_resolvers: Vec::new(),
            flaw_pair_cost: Vec::new(),
            h2_dirty: false,

            lit_to_resolvers: HashMap::new(),
            resolver_status: Vec::new(),
            resolver_rho: Vec::new(),
            resolver_cost_var: Vec::new(),
            resolver_intrinsic_cost: Vec::new(),
            resolver_flaw: Vec::new(),
            resolver_preconditions: Vec::new(),
            pair_preconditions: HashMap::new(),
            resolver_linked_to: Vec::new(),
            resolver_impliers: Vec::new(),
            res_mutex: Vec::new(),
            probed_pairs: HashSet::new(),

            flaw_q: VecDeque::new(),
            agenda: HashSet::new(),

            tx_event,
        }
    }

    #[inline]
    fn norm_pair(f1: FlawId, f2: FlawId) -> (FlawId, FlawId) {
        if f1 <= f2 { (f1, f2) } else { (f2, f1) }
    }

    #[inline]
    fn norm_res_pair(r1: ResolverId, r2: ResolverId) -> (ResolverId, ResolverId) {
        if r1 <= r2 { (r1, r2) } else { (r2, r1) }
    }

    #[inline]
    fn pair_cost(&self, f1: FlawId, f2: FlawId) -> f64 {
        let (lo, hi) = Self::norm_pair(f1, f2);
        self.flaw_pair_cost[hi.0][lo.0]
    }

    #[inline]
    fn set_pair_cost(&mut self, f1: FlawId, f2: FlawId, cost: f64) {
        let (lo, hi) = Self::norm_pair(f1, f2);
        self.flaw_pair_cost[hi.0][lo.0] = cost;
    }

    #[inline]
    pub(super) fn is_res_mutex(&self, r1: ResolverId, r2: ResolverId) -> bool {
        self.res_mutex[r1].contains(r2.0)
    }

    #[inline]
    pub(super) fn is_flaw_res_mutex(&self, flw: FlawId, res: ResolverId) -> bool {
        self.flaw_causes[flw].iter().any(|&c| self.is_res_mutex(c, res))
    }

    #[inline]
    pub(super) fn is_flaw_mutex(&self, f1: FlawId, f2: FlawId) -> bool {
        f1 != f2 && self.flaw_causes[f1].iter().any(|&c1| self.flaw_causes[f2].iter().any(|&c2| self.is_res_mutex(c1, c2)))
    }

    /// Marks `r1` and `r2` as mutually exclusive and closes the relation downward across all impliers.
    pub(super) fn add_res_mutex(&mut self, r1: ResolverId, r2: ResolverId) {
        if r1 == r2 || self.is_res_mutex(r1, r2) {
            return;
        }
        let c1 = self.implier_closure(r1);
        let c2 = self.implier_closure(r2);
        for &a in &c1 {
            for &b in &c2 {
                if a != b && !self.is_res_mutex(a, b) {
                    self.res_mutex[a].set(b.0);
                    self.res_mutex[b].set(a.0);
                    self.h2_dirty = true;
                }
            }
        }
    }

    /// Extracts conflict-driven resolver mutexes from a learned binary clause `l1 ∨ l2` (`¬(¬l1 ∧ ¬l2)`).
    pub(super) fn learn_binary_clause(&mut self, l1: Lit, l2: Lit) {
        let mut rs1 = self.lit_to_resolvers.get(&!l1).cloned().unwrap_or_default();
        if let Some(fs1) = self.lit_to_flaws.get(&!l1) {
            for &f in fs1 {
                rs1.extend_from_slice(&self.flaw_resolvers[f]);
            }
        }
        if rs1.is_empty() {
            return;
        }
        let mut rs2 = self.lit_to_resolvers.get(&!l2).cloned().unwrap_or_default();
        if let Some(fs2) = self.lit_to_flaws.get(&!l2) {
            for &f in fs2 {
                rs2.extend_from_slice(&self.flaw_resolvers[f]);
            }
        }
        for r1 in rs1 {
            for &r2 in &rs2 {
                self.add_res_mutex(r1, r2);
            }
        }
    }

    fn implier_closure(&self, root: ResolverId) -> Vec<ResolverId> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![root];
        while let Some(r) = stack.pop() {
            if seen.insert(r) {
                out.push(r);
                stack.extend_from_slice(&self.resolver_impliers[r]);
            }
        }
        out
    }

    fn inherit_res_mutexes(&mut self, child: ResolverId, parent: ResolverId) {
        let others: Vec<usize> = self.res_mutex[parent].iter_ones().collect();
        for other in others {
            if other != child.0 {
                self.res_mutex[child].set(other);
                self.res_mutex[other].set(child.0);
            }
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
    pub fn add_flaw(&mut self, mut causes: Vec<ResolverId>, phi: Lit, status: Option<bool>, cost_var: DlVar, flw: Box<dyn Flaw>) -> FlawId {
        causes.sort_unstable();
        causes.dedup();

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
        self.flaw_expanded.push(false);
        if status == Some(true) {
            self.agenda.insert(flw_id);
            trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
        }
        self.flaw_cost_var.push(cost_var);
        self.flaw_resolvers.push(Vec::new());
        self.flaw_pair_cost.push(vec![f64::INFINITY; flw_id.0 + 1]);

        match causes.as_slice() {
            &[r] => self.resolver_preconditions[r].push(flw_id),
            &[r1, r2] => self.pair_preconditions.entry(Self::norm_res_pair(r1, r2)).or_default().push(flw_id),
            _ => {}
        }

        self.flaw_causes.push(causes);
        self.lit_to_flaws.entry(phi).or_default().push(flw_id);
        self.flaw_q.push_back(flw_id);
        self.h2_dirty = true;

        flw_id
    }

    pub(super) fn phi(&self, flw_id: FlawId) -> Lit {
        self.flaw_phi[flw_id]
    }

    pub(super) fn flaw_status(&self, flw_id: FlawId) -> Option<bool> {
        self.flaw_status[flw_id]
    }

    pub(super) fn flaw_cost_var(&self, flw_id: FlawId) -> DlVar {
        self.flaw_cost_var[flw_id]
    }

    pub(super) fn flaw_resolvers(&self, flw_id: FlawId) -> &[ResolverId] {
        &self.flaw_resolvers[flw_id]
    }

    pub(super) fn flaw_expanded(&self, flw_id: FlawId) -> bool {
        self.flaw_expanded[flw_id]
    }

    pub(super) fn has_active_unexpanded_flaw(&self) -> bool {
        self.agenda.iter().any(|&f_id| !self.flaw_expanded[f_id])
    }

    pub(super) fn take_flaw(&mut self, flw_id: FlawId) -> Option<Box<dyn Flaw>> {
        if let Some(pos) = self.flaw_q.iter().position(|&id| id == flw_id) {
            self.flaw_q.remove(pos);
        }
        self.flaw_expanded[flw_id] = true;
        self.c_flaw.replace((flw_id, self.flaw_phi[flw_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(flw_id)));
        self.flaws[flw_id].take()
    }

    pub(super) fn return_flaw(&mut self, flw: Box<dyn Flaw>) {
        let (flw_id, _) = self.c_flaw.take().expect("A flaw must be currently being processed to return it");
        self.flaws[flw_id] = Some(flw);
        self.h2_dirty = true;
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
    }

    /// Adds a new resolver to the graph, returning its ResolverId.
    pub fn add_resolver(&mut self, rho: Lit, status: Option<bool>, cost: DlVar, res: Box<dyn Resolver>) -> ResolverId {
        let (flaw_id, _) = self.c_flaw.expect("Cannot add a resolver when no flaw is currently being processed");
        let res_id = ResolverId(self.resolvers.len());
        let intrinsic_cost = res.intrinsic_cost().to_f64();
        trace!("Adding resolver: {} ({}) for flaw {}", res_id, rho, flaw_id);

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewResolver {
            resolver_id: res_id,
            flaw_id,
            rho: rho.to_string(),
            status,
            intrinsic_cost,
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
        self.resolver_intrinsic_cost.push(intrinsic_cost);
        self.resolver_flaw.push(flaw_id);
        self.resolver_preconditions.push(Vec::new());
        self.resolver_linked_to.push(None);
        self.resolver_impliers.push(Vec::new());
        self.res_mutex.push(BitSet::default());

        // Inherit mutexes from parent flaw's causes and register as their implier.
        let causes = self.flaw_causes[flaw_id].clone();
        for c in causes {
            self.resolver_impliers[c].push(res_id);
            self.inherit_res_mutexes(res_id, c);
        }
        // Sibling resolvers of the same flaw are mutually exclusive.
        let siblings = self.flaw_resolvers[flaw_id].clone();
        for sib in siblings {
            self.add_res_mutex(res_id, sib);
        }

        self.flaw_resolvers[flaw_id].push(res_id);
        self.lit_to_resolvers.entry(rho).or_default().push(res_id);
        self.h2_dirty = true;

        res_id
    }

    pub(super) fn resolver_status(&self, res_id: ResolverId) -> Option<bool> {
        self.resolver_status[res_id]
    }

    pub(super) fn rho(&self, res_id: ResolverId) -> Lit {
        self.resolver_rho[res_id]
    }

    pub(super) fn rhos(&self, res_ids: &[ResolverId]) -> Vec<Lit> {
        res_ids.iter().map(|&r_id| self.resolver_rho[r_id]).collect()
    }

    pub(super) fn resolver_cost_var(&self, res_id: ResolverId) -> DlVar {
        self.resolver_cost_var[res_id]
    }

    pub(super) fn resolver_intrinsic_cost(&self, res_id: ResolverId) -> rug::Rational {
        self.resolvers[res_id].as_ref().expect("Resolver should exist in graph").intrinsic_cost()
    }

    pub(super) fn take_resolver(&mut self, res_id: ResolverId) -> Option<Box<dyn Resolver>> {
        self.c_res.replace((res_id, self.resolver_rho[res_id]));
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(res_id)));
        self.resolvers[res_id].take()
    }

    /// Adds a causal link from the current resolver to `target_res` (unidirectional mutex inheritance).
    pub(super) fn add_causal_link(&mut self, target_res: ResolverId) -> Result<(Lit, Lit), SolverError> {
        let (res_id, rho) = self.c_res.ok_or(SolverError::RuntimeError(String::from("No current resolver to add causal link from")))?;
        assert!(self.resolver_linked_to[res_id].is_none(), "Resolver {} already has a causal link", res_id);
        debug_assert!(self.resolver_linked_to[target_res].is_none(), "Chained causal links are not supported");

        self.resolver_linked_to[res_id] = Some(target_res);
        self.resolver_impliers[target_res].push(res_id);
        self.inherit_res_mutexes(res_id, target_res);
        self.h2_dirty = true;

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::NewCausalLink { flaw_id: self.resolver_flaw[target_res], resolver_id: res_id });

        Ok((rho, self.resolver_rho[target_res]))
    }

    pub(super) fn return_resolver(&mut self, res: Box<dyn Resolver>) {
        let (res_id, _) = self.c_res.take().expect("A resolver must be currently being processed to return it");
        self.resolvers[res_id] = Some(res);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
    }

    /// Collects unprobed, non-mutex resolver pairs across distinct flaws currently in `agenda`.
    pub(super) fn agenda_resolver_pairs(&self) -> Vec<(ResolverId, ResolverId)> {
        let agenda: Vec<FlawId> = self.agenda.iter().copied().collect();
        let mut pairs = Vec::new();
        for (i, &f1) in agenda.iter().enumerate() {
            for &f2 in &agenda[(i + 1)..] {
                for &r1 in &self.flaw_resolvers[f1] {
                    if !self.is_resolver_alive(r1) {
                        continue;
                    }
                    for &r2 in &self.flaw_resolvers[f2] {
                        if !self.is_resolver_alive(r2) || self.is_res_mutex(r1, r2) {
                            continue;
                        }
                        let key = Self::norm_res_pair(r1, r2);
                        if !self.probed_pairs.contains(&key) {
                            pairs.push(key);
                        }
                    }
                }
            }
        }
        pairs
    }

    pub(super) fn mark_probed(&mut self, r1: ResolverId, r2: ResolverId) -> bool {
        self.probed_pairs.insert(Self::norm_res_pair(r1, r2))
    }

    #[inline]
    fn effective_resolver(&self, r: ResolverId) -> (ResolverId, f64) {
        if let Some(target) = self.resolver_linked_to[r] { (target, self.resolver_intrinsic_cost[r] + self.resolver_intrinsic_cost[target]) } else { (r, self.resolver_intrinsic_cost[r]) }
    }

    #[inline]
    fn is_resolver_alive(&self, r: ResolverId) -> bool {
        if self.resolver_status[r] == Some(false) {
            return false;
        }
        if let Some(target) = self.resolver_linked_to[r]
            && (self.resolver_status[target] == Some(false) || self.flaw_status[self.resolver_flaw[target]] == Some(false))
        {
            return false;
        }
        true
    }

    fn resolver_prec_cost(&self, eff: ResolverId) -> f64 {
        let p = &self.resolver_preconditions[eff];
        let mut max_c = 0.0_f64;
        for (i, &p1) in p.iter().enumerate() {
            for &p2 in &p[i..] {
                let c = self.pair_cost(p1, p2);
                if c == f64::INFINITY {
                    return f64::INFINITY;
                }
                if c > max_c {
                    max_c = c;
                }
            }
        }
        max_c
    }

    fn resolver_pair_cost(&self, r1: ResolverId, r2: ResolverId, p1_cost: f64, p2_cost: f64, cur_best: f64) -> f64 {
        if r1 != r2 && self.is_res_mutex(r1, r2) {
            return f64::INFINITY;
        }
        let (s1, w1) = self.effective_resolver(r1);
        let (s2, w2) = self.effective_resolver(r2);
        if s1 != s2 && self.is_res_mutex(s1, s2) {
            return f64::INFINITY;
        }

        let base_w = w1.max(w2);
        let mut max_prec = p1_cost.max(p2_cost);
        if base_w + max_prec >= cur_best {
            return f64::INFINITY;
        }

        if s1 != s2 {
            let p1 = &self.resolver_preconditions[s1];
            let p2 = &self.resolver_preconditions[s2];
            for &f1 in p1 {
                for &f2 in p2 {
                    max_prec = max_prec.max(self.pair_cost(f1, f2));
                    if base_w + max_prec >= cur_best {
                        return f64::INFINITY;
                    }
                }
            }
            if let Some(pp) = self.pair_preconditions.get(&Self::norm_res_pair(s1, s2)) {
                for (i, &pf) in pp.iter().enumerate() {
                    for &pf2 in &pp[i..] {
                        max_prec = max_prec.max(self.pair_cost(pf, pf2));
                    }
                    for &f1 in p1 {
                        max_prec = max_prec.max(self.pair_cost(pf, f1));
                    }
                    for &f2 in p2 {
                        max_prec = max_prec.max(self.pair_cost(pf, f2));
                    }
                    if base_w + max_prec >= cur_best {
                        return f64::INFINITY;
                    }
                }
            }
        }

        base_w + max_prec
    }

    /// Lazily recomputes the full h^2 matrix by monotone fixed-point relaxation from ∞.
    fn ensure_h2(&mut self) {
        if !self.h2_dirty {
            return;
        }
        self.h2_dirty = false;

        #[cfg(feature = "server")]
        let old_diag: Vec<f64> = (0..self.flaws.len()).map(|i| self.flaw_pair_cost[i][i]).collect();

        for row in &mut self.flaw_pair_cost {
            row.fill(f64::INFINITY);
        }

        let mut alive: Vec<(ResolverId, FlawId, ResolverId, f64)> = Vec::new();
        for f_idx in 0..self.flaws.len() {
            let f = FlawId(f_idx);
            if !self.flaw_expanded[f] || self.flaw_status[f] == Some(false) {
                continue;
            }
            let r_list = &self.flaw_resolvers[f];
            if let Some(&r) = r_list.iter().find(|&&r| self.resolver_status[r] == Some(true)) {
                if self.is_resolver_alive(r) {
                    let (eff, w) = self.effective_resolver(r);
                    alive.push((r, f, eff, w));
                }
            } else {
                for &r in r_list {
                    if self.is_resolver_alive(r) {
                        let (eff, w) = self.effective_resolver(r);
                        alive.push((r, f, eff, w));
                    }
                }
            }
        }

        let mut prec_costs = vec![f64::INFINITY; alive.len()];
        loop {
            let mut changed = false;
            for (i, &(_, _, eff, _)) in alive.iter().enumerate() {
                prec_costs[i] = self.resolver_prec_cost(eff);
            }

            for i in 0..alive.len() {
                let p1 = prec_costs[i];
                if p1 == f64::INFINITY {
                    continue;
                }
                let (r1, f1, _, w1) = alive[i];
                let diag = w1 + p1;
                if diag < self.pair_cost(f1, f1) {
                    self.set_pair_cost(f1, f1, diag);
                    changed = true;
                }

                for j in (i + 1)..alive.len() {
                    let p2 = prec_costs[j];
                    if p2 == f64::INFINITY {
                        continue;
                    }
                    let (r2, f2, _, _) = alive[j];
                    let cur = self.pair_cost(f1, f2);
                    let c = self.resolver_pair_cost(r1, r2, p1, p2, cur);
                    if c < cur {
                        self.set_pair_cost(f1, f2, c);
                        changed = true;
                    }
                }
            }

            if !changed {
                break;
            }
        }

        #[cfg(feature = "server")]
        for (i, old_c) in old_diag.into_iter().enumerate() {
            let new_c = self.flaw_pair_cost[i][i];
            if new_c != old_c {
                let _ = self.tx_event.send(SolverEvent::FlawCostUpdate { flaw_id: FlawId(i), cost: new_c });
            }
        }
    }

    pub(super) fn propagate(&mut self, lits: &[Lit]) {
        // 1. Update resolver status first so newly activated flaws with an already-active resolver are not added to the agenda.
        for &lit in lits {
            if let Some(res_ids) = self.lit_to_resolvers.get(&lit) {
                for &res_id in res_ids {
                    self.resolver_status[res_id] = Some(true);
                    self.h2_dirty = true;
                    let flaw_id = self.resolver_flaw[res_id];
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: Some(true) });
                    if self.agenda.remove(&flaw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id });
                    }
                }
            }
            if let Some(res_ids) = self.lit_to_resolvers.get(&!lit) {
                for &res_id in res_ids {
                    self.resolver_status[res_id] = Some(false);
                    self.h2_dirty = true;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: Some(false) });
                }
            }
        }
        // 2. Update flaw status and synchronize the agenda.
        for &lit in lits {
            if let Some(flw_ids) = self.lit_to_flaws.get(&lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[flw_id] = Some(true);
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: Some(true) });
                    if !self.flaw_resolvers[flw_id].iter().any(|&r| self.resolver_status[r] == Some(true)) && self.agenda.insert(flw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                    }
                }
            }
            if let Some(flw_ids) = self.lit_to_flaws.get(&!lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[flw_id] = Some(false);
                    self.h2_dirty = true;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: Some(false) });
                    if self.agenda.remove(&flw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id: flw_id });
                    }
                }
            }
        }
    }

    pub(super) fn cancel_until(&mut self, lits: &[Lit]) {
        if lits.is_empty() {
            return;
        }
        self.h2_dirty = true;

        for &lit in lits {
            if let Some(flw_ids) = self.lit_to_flaws.get(&lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[flw_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: None });
                    if self.agenda.remove(&flw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::SolvedFlaw { flaw_id: flw_id });
                    }
                }
            }
            if let Some(flw_ids) = self.lit_to_flaws.get(&!lit) {
                for &flw_id in flw_ids {
                    self.flaw_status[flw_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::FlawStatusUpdate { flaw_id: flw_id, status: None });
                }
            }
        }
        for &lit in lits {
            if let Some(res_ids) = self.lit_to_resolvers.get(&lit) {
                for &res_id in res_ids {
                    self.resolver_status[res_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: None });
                    let flw_id = self.resolver_flaw[res_id];
                    if self.flaw_status[flw_id] == Some(true) && !self.flaw_resolvers[flw_id].iter().any(|&r| self.resolver_status[r] == Some(true)) && self.agenda.insert(flw_id) {
                        trace!("Agenda size: {}, {{{}}}", self.agenda.len(), self.agenda.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(", "));
                        #[cfg(feature = "server")]
                        let _ = self.tx_event.send(SolverEvent::ToSolveFlaw { flaw_id: flw_id });
                    }
                }
            }
            if let Some(res_ids) = self.lit_to_resolvers.get(&!lit) {
                for &res_id in res_ids {
                    self.resolver_status[res_id] = None;
                    #[cfg(feature = "server")]
                    let _ = self.tx_event.send(SolverEvent::ResolverStatusUpdate { resolver_id: res_id, status: None });
                }
            }
        }
    }

    /// h^2 termination criterion: every pair of flaws in `agenda` must be jointly solvable (`h^2(f1, f2) < ∞`).
    pub(super) fn has_estimated_solution(&mut self) -> bool {
        self.ensure_h2();
        let agenda: Vec<FlawId> = self.agenda.iter().copied().collect();
        for (i, &f1) in agenda.iter().enumerate() {
            for &f2 in &agenda[i..] {
                if self.pair_cost(f1, f2) == f64::INFINITY {
                    return false;
                }
            }
        }
        true
    }

    pub(super) fn pop_flaw(&mut self) -> Option<FlawId> {
        self.ensure_h2();
        let mut best_idx = None;
        let mut best_priority = 0;

        for (idx, &f_id) in self.flaw_q.iter().enumerate() {
            if self.flaw_status[f_id] == Some(false) {
                continue;
            }
            let priority = if self.flaw_status[f_id] == Some(true) {
                2
            } else if self.agenda.iter().any(|&ag| self.is_flaw_mutex(f_id, ag)) || self.has_jointly_finite_ancestor(f_id) {
                0
            } else {
                1
            };

            if best_idx.is_none() || priority > best_priority {
                best_priority = priority;
                best_idx = Some(idx);
            }
        }

        best_idx.and_then(|idx| self.flaw_q.remove(idx))
    }

    /// Returns true if `anc` is a causal ancestor of `flw` along `flaw_causes`.
    pub(super) fn is_ancestor(&self, anc: ResolverId, flw: FlawId) -> bool {
        let mut queue = VecDeque::from([flw]);
        let mut visited = HashSet::new();

        while let Some(f_id) = queue.pop_front() {
            if !visited.insert(f_id) {
                continue;
            }
            for &c_res in &self.flaw_causes[f_id] {
                if c_res == anc {
                    return true;
                }
                queue.push_back(self.resolver_flaw[c_res]);
            }
        }

        false
    }

    fn has_jointly_finite_ancestor(&self, target: FlawId) -> bool {
        let mut queue = Vec::new();
        let mut visited = HashSet::new();

        for &res_id in &self.flaw_causes[target] {
            queue.push(self.resolver_flaw[res_id]);
        }

        while let Some(f_id) = queue.pop() {
            if !visited.insert(f_id) {
                continue;
            }
            if self.pair_cost(f_id, f_id) < f64::INFINITY && self.agenda.iter().all(|&ag| self.is_flaw_mutex(f_id, ag) || self.pair_cost(f_id, ag) < f64::INFINITY) {
                return true;
            }
            for &res_id in &self.flaw_causes[f_id] {
                queue.push(self.resolver_flaw[res_id]);
            }
        }

        false
    }

    pub(super) fn pick_branching_literal(&mut self) -> Option<Lit> {
        for &f_id in &self.flaw_q {
            if self.flaw_status[f_id].is_none() {
                let lit = !self.flaw_phi[f_id];
                trace!("Branching on unexpanded flaw {}: {}", f_id, lit);
                #[cfg(feature = "server")]
                let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(f_id)));
                return Some(lit);
            }
        }

        if self.agenda.is_empty() {
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentFlaw(None));
            #[cfg(feature = "server")]
            let _ = self.tx_event.send(SolverEvent::CurrentResolver(None));
            return None;
        }

        self.ensure_h2();
        let agenda: Vec<FlawId> = self.agenda.iter().copied().collect();

        let mut worst_pair = (agenda[0], agenda[0]);
        let mut worst_cost = self.pair_cost(agenda[0], agenda[0]);
        for (i, &f1) in agenda.iter().enumerate() {
            for &f2 in &agenda[i..] {
                let c = self.pair_cost(f1, f2);
                if c.total_cmp(&worst_cost) == Ordering::Greater {
                    worst_cost = c;
                    worst_pair = (f1, f2);
                }
            }
        }

        let (f1, f2) = worst_pair;
        let best_flaw_id = if f1 == f2 {
            f1
        } else {
            let avail = |f: FlawId| self.flaw_resolvers[f].iter().filter(|&&r| self.is_resolver_alive(r)).count();
            match avail(f1).cmp(&avail(f2)) {
                Ordering::Less => f1,
                Ordering::Greater => f2,
                Ordering::Equal => {
                    if self.pair_cost(f1, f1).total_cmp(&self.pair_cost(f2, f2)) != Ordering::Less {
                        f1
                    } else {
                        f2
                    }
                }
            }
        };

        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentFlaw(Some(best_flaw_id)));

        let mut best_res_id = None;
        let mut best_score = f64::INFINITY;
        let mut best_diag = f64::INFINITY;

        for &r1 in &self.flaw_resolvers[best_flaw_id] {
            if !self.is_resolver_alive(r1) {
                continue;
            }
            let (s1, w1) = self.effective_resolver(r1);
            let p1 = self.resolver_prec_cost(s1);
            let diag = w1 + p1;
            let mut score = diag;

            if score < f64::INFINITY {
                for &other in &agenda {
                    if other == best_flaw_id {
                        continue;
                    }
                    let mut min_with_other = f64::INFINITY;
                    for &r2 in &self.flaw_resolvers[other] {
                        if !self.is_resolver_alive(r2) {
                            continue;
                        }
                        let (s2, _) = self.effective_resolver(r2);
                        let p2 = self.resolver_prec_cost(s2);
                        if p2 == f64::INFINITY {
                            continue;
                        }
                        let c = self.resolver_pair_cost(r1, r2, p1, p2, min_with_other);
                        if c < min_with_other {
                            min_with_other = c;
                        }
                    }
                    if min_with_other > score {
                        score = min_with_other;
                    }
                }
            }

            if best_res_id.is_none() || score.total_cmp(&best_score) == Ordering::Less || (score.total_cmp(&best_score) == Ordering::Equal && diag.total_cmp(&best_diag) == Ordering::Less) {
                best_score = score;
                best_diag = diag;
                best_res_id = Some(r1);
            }
        }

        let best_res_id = best_res_id.expect("There should be at least one resolver for the flaw");
        let lit = self.resolver_rho[best_res_id];
        trace!("Branching on flaw {} (pair_cost={}) with resolver {} ({}, score={})", best_flaw_id, worst_cost, best_res_id, lit, best_score);
        #[cfg(feature = "server")]
        let _ = self.tx_event.send(SolverEvent::CurrentResolver(Some(best_res_id)));
        Some(lit)
    }
}
