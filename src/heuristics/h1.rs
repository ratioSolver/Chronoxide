use crate::{
    graph::{CausalGraph, FlawId, ResolverId},
    heuristics::Heuristic,
    mutex::MutexTable,
    search::SearchState,
};
use semitone::Lit;
use std::{cmp::Ordering, collections::HashSet, marker::PhantomData};

pub(crate) trait Combine {
    fn combine(acc: f64, val: f64) -> f64;
}

#[cfg(feature = "h_max")]
pub(crate) struct Max;

#[cfg(feature = "h_max")]
impl Combine for Max {
    #[inline]
    fn combine(acc: f64, val: f64) -> f64 {
        acc.max(val)
    }
}

#[cfg(feature = "h_add")]
pub(crate) struct Add;

#[cfg(feature = "h_add")]
impl Combine for Add {
    #[inline]
    fn combine(acc: f64, val: f64) -> f64 {
        acc + val
    }
}

#[cfg(feature = "h_max")]
pub(crate) type HMax = H1<Max>;

#[cfg(feature = "h_add")]
pub(crate) type HAdd = H1<Add>;

/// Single-flaw relaxed cost heuristic (`h_max` or `h_add`).
pub(crate) struct H1<C: Combine> {
    costs: Vec<f64>,
    dirty: bool,
    _mode: PhantomData<C>,
}

impl<C: Combine> H1<C> {
    fn prec_cost(&self, graph: &CausalGraph, eff: ResolverId) -> f64 {
        let mut acc = 0.0_f64;
        for &p in &graph.resolver(eff).preconditions {
            let c = self.costs[p];
            if c == f64::INFINITY {
                return f64::INFINITY;
            }
            acc = C::combine(acc, c);
        }
        acc
    }

    fn resolver_cost(&self, graph: &CausalGraph, search: &SearchState, res: ResolverId) -> f64 {
        if !search.is_resolver_alive(graph, res) {
            return f64::INFINITY;
        }
        let (eff, intrinsic) = graph.effective_resolver(res);
        let prec = self.prec_cost(graph, eff);
        if prec == f64::INFINITY { f64::INFINITY } else { intrinsic + prec }
    }

    fn has_finite_ancestor(&self, graph: &CausalGraph, target: FlawId) -> bool {
        let mut stack: Vec<FlawId> = graph.flaw(target).causes.iter().map(|&r| graph.resolver(r).flaw).collect();
        let mut visited = HashSet::new();

        while let Some(f_id) = stack.pop() {
            if !visited.insert(f_id) {
                continue;
            }
            if self.costs[f_id] < f64::INFINITY {
                return true;
            }
            for &c_res in &graph.flaw(f_id).causes {
                stack.push(graph.resolver(c_res).flaw);
            }
        }

        false
    }
}

impl<C: Combine> Heuristic for H1<C> {
    fn new() -> Self {
        Self { costs: Vec::new(), dirty: true, _mode: PhantomData }
    }

    fn invalidate(&mut self) {
        self.dirty = true;
    }

    fn ensure_fresh(&mut self, graph: &CausalGraph, _mutex: &MutexTable, search: &SearchState) -> Vec<(FlawId, f64)> {
        if !self.dirty {
            return Vec::new();
        }
        self.dirty = false;

        let n = graph.flaw_count();
        #[cfg(feature = "server")]
        let old_costs = {
            let mut old = self.costs.clone();
            old.resize(n, f64::INFINITY);
            old
        };

        self.costs.resize(n, f64::INFINITY);
        self.costs.fill(f64::INFINITY);

        // Collect all alive resolvers belonging to expanded, non-false flaws.
        let mut alive: Vec<(FlawId, ResolverId, f64)> = Vec::new();
        for f in graph.flaw_ids() {
            if !graph.is_expanded(f) || search.flaw_val(f) == Some(false) {
                continue;
            }
            let r_list = &graph.flaw(f).resolvers;
            if let Some(&r) = r_list.iter().find(|&&r| search.res_val(r) == Some(true)) {
                if search.is_resolver_alive(graph, r) {
                    let (eff, intrinsic) = graph.effective_resolver(r);
                    alive.push((f, eff, intrinsic));
                }
            } else {
                for &r in r_list {
                    if search.is_resolver_alive(graph, r) {
                        let (eff, intrinsic) = graph.effective_resolver(r);
                        alive.push((f, eff, intrinsic));
                    }
                }
            }
        }

        // Monotone fixed-point relaxation from ∞.
        loop {
            let mut changed = false;
            for &(f, eff, intrinsic) in &alive {
                let prec = self.prec_cost(graph, eff);
                if prec == f64::INFINITY {
                    continue;
                }
                let cost = intrinsic + prec;
                if cost < self.costs[f] {
                    self.costs[f] = cost;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        #[cfg(feature = "server")]
        {
            graph
                .flaw_ids()
                .filter_map(|f| {
                    let new_c = self.costs[f];
                    (new_c != old_costs[f]).then_some((f, new_c))
                })
                .collect()
        }
        #[cfg(not(feature = "server"))]
        {
            Vec::new()
        }
    }

    #[inline]
    fn flaw_cost(&self, flw: FlawId) -> f64 {
        self.costs.get(flw.index()).copied().unwrap_or(f64::INFINITY)
    }

    fn is_resolver_finite(&self, graph: &CausalGraph, _mutex: &MutexTable, search: &SearchState, res: ResolverId) -> bool {
        self.resolver_cost(graph, search, res) < f64::INFINITY
    }

    fn has_estimated_solution(&self, _graph: &CausalGraph, _mutex: &MutexTable, search: &SearchState) -> bool {
        search.agenda().iter().all(|&f| self.costs[f] < f64::INFINITY)
    }

    fn pick_phi_to_expand(&self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> Option<Lit> {
        let mut best_flaw = None;
        let mut best_priority = 0u8;

        for &f in graph.frontier() {
            if search.flaw_val(f) == Some(false) {
                continue;
            }
            let priority = if search.flaw_val(f) == Some(true) {
                2
            } else if search.agenda().iter().any(|&ag| mutex.is_flaw_mutex(graph, f, ag)) || self.has_finite_ancestor(graph, f) {
                0
            } else {
                1
            };

            if best_flaw.is_none() || priority > best_priority {
                best_priority = priority;
                best_flaw = Some(f);
            }
        }

        best_flaw.map(|f| graph.flaw(f).phi)
    }

    fn pick_branch(&self, graph: &CausalGraph, _mutex: &MutexTable, search: &SearchState) -> Option<(FlawId, ResolverId)> {
        let best_flaw = search.agenda().iter().copied().max_by(|&f1, &f2| self.costs[f1].total_cmp(&self.costs[f2]).then_with(|| f2.cmp(&f1)))?;

        let mut best_res = None;
        let mut best_cost = f64::INFINITY;
        for &r in &graph.flaw(best_flaw).resolvers {
            if !search.is_resolver_alive(graph, r) {
                continue;
            }
            let cost = self.resolver_cost(graph, search, r);
            if best_res.is_none() || cost.total_cmp(&best_cost) == Ordering::Less {
                best_cost = cost;
                best_res = Some(r);
            }
        }

        let best_res = best_res.expect("Active flaw in agenda must have at least one alive resolver");
        Some((best_flaw, best_res))
    }
}
