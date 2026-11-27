use crate::{
    graph::{CausalGraph, FlawId, ResolverId},
    heuristics::{Heuristic, norm_flaw_pair},
    mutex::MutexTable,
    search::SearchState,
};
use semitone::Lit;
use std::{cmp::Ordering, collections::HashSet};

/// Pairwise relaxed cost heuristic (`h^2`).
pub(crate) struct H2 {
    /// Lower-triangular flaw pair-cost matrix: `pair_costs[hi.index()][lo.index()]` for `lo <= hi`.
    pair_costs: Vec<Vec<f64>>,
    dirty: bool,
}

impl H2 {
    #[inline]
    fn pair_cost(&self, f1: FlawId, f2: FlawId) -> f64 {
        let (lo, hi) = norm_flaw_pair(f1, f2);
        self.pair_costs[hi.index()][lo.index()]
    }

    #[inline]
    fn set_pair_cost(&mut self, f1: FlawId, f2: FlawId, cost: f64) {
        let (lo, hi) = norm_flaw_pair(f1, f2);
        self.pair_costs[hi.index()][lo.index()] = cost;
    }

    /// Computes the maximum `h^2` cost over all pairs of preconditions of an effective resolver.
    fn prec_cost(&self, graph: &CausalGraph, eff: ResolverId) -> f64 {
        let precs = &graph.resolver(eff).preconditions;
        let mut max_c = 0.0_f64;
        for (i, &p1) in precs.iter().enumerate() {
            for &p2 in &precs[i..] {
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

    /// Computes the joint `h^2` cost of applying `r1` and `r2`, pruning early against `cur_best`.
    fn resolver_pair_cost(&self, graph: &CausalGraph, mutex: &MutexTable, r1: ResolverId, r2: ResolverId, p1_cost: f64, p2_cost: f64, cur_best: f64) -> f64 {
        if r1 != r2 && mutex.is_res_mutex(r1, r2) {
            return f64::INFINITY;
        }
        let (s1, w1) = graph.effective_resolver(r1);
        let (s2, w2) = graph.effective_resolver(r2);
        if s1 != s2 && mutex.is_res_mutex(s1, s2) {
            return f64::INFINITY;
        }

        let base_w = w1.max(w2);
        let mut max_prec = p1_cost.max(p2_cost);
        if base_w + max_prec >= cur_best {
            return f64::INFINITY;
        }

        if s1 != s2 {
            let p1 = &graph.resolver(s1).preconditions;
            let p2 = &graph.resolver(s2).preconditions;
            for &f1 in p1 {
                for &f2 in p2 {
                    max_prec = max_prec.max(self.pair_cost(f1, f2));
                    if base_w + max_prec >= cur_best {
                        return f64::INFINITY;
                    }
                }
            }
        }

        base_w + max_prec
    }

    /// Returns `true` if `target` has an ancestor that is jointly solvable with every compatible flaw in `agenda`.
    fn has_jointly_finite_ancestor(&self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState, target: FlawId) -> bool {
        let mut stack: Vec<FlawId> = graph.flaw(target).causes.iter().map(|&r| graph.resolver(r).flaw).collect();
        let mut visited = HashSet::new();

        while let Some(f_id) = stack.pop() {
            if !visited.insert(f_id) {
                continue;
            }
            if self.pair_cost(f_id, f_id) < f64::INFINITY && search.agenda().iter().all(|&ag| mutex.is_flaw_mutex(graph, f_id, ag) || self.pair_cost(f_id, ag) < f64::INFINITY) {
                return true;
            }
            for &c_res in &graph.flaw(f_id).causes {
                stack.push(graph.resolver(c_res).flaw);
            }
        }

        false
    }
}

impl Heuristic for H2 {
    fn new() -> Self {
        Self { pair_costs: Vec::new(), dirty: true }
    }

    fn invalidate(&mut self) {
        self.dirty = true;
    }

    fn ensure_fresh(&mut self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> Vec<(FlawId, f64)> {
        if !self.dirty {
            return Vec::new();
        }
        self.dirty = false;

        let n = graph.flaw_count();
        #[cfg(feature = "server")]
        let old_diag: Vec<f64> = (0..n).map(|i| self.pair_costs.get(i).map_or(f64::INFINITY, |row| row[i])).collect();

        while self.pair_costs.len() < n {
            self.pair_costs.push(vec![f64::INFINITY; self.pair_costs.len() + 1]);
        }
        for row in &mut self.pair_costs {
            row.fill(f64::INFINITY);
        }

        // Collect all alive resolvers belonging to expanded, non-false flaws.
        let mut alive: Vec<(ResolverId, FlawId, ResolverId, f64)> = Vec::new();
        for f in graph.flaw_ids() {
            if !graph.is_expanded(f) || search.flaw_val(f) == Some(false) {
                continue;
            }
            let r_list = &graph.flaw(f).resolvers;
            if let Some(&r) = r_list.iter().find(|&&r| search.res_val(r) == Some(true)) {
                if search.is_resolver_alive(graph, r) {
                    let (eff, intrinsic) = graph.effective_resolver(r);
                    alive.push((r, f, eff, intrinsic));
                }
            } else {
                for &r in r_list {
                    if search.is_resolver_alive(graph, r) {
                        let (eff, intrinsic) = graph.effective_resolver(r);
                        alive.push((r, f, eff, intrinsic));
                    }
                }
            }
        }

        // Monotone fixed-point relaxation from ∞.
        let mut prec_costs = vec![f64::INFINITY; alive.len()];
        loop {
            let mut changed = false;
            for (i, &(_, _, eff, _)) in alive.iter().enumerate() {
                prec_costs[i] = self.prec_cost(graph, eff);
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
                    if f1 == f2 {
                        continue;
                    }
                    let cur = self.pair_cost(f1, f2);
                    let c = self.resolver_pair_cost(graph, mutex, r1, r2, p1, p2, cur);
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
        {
            graph
                .flaw_ids()
                .filter_map(|f| {
                    let new_c = self.pair_costs[f.index()][f.index()];
                    (new_c != old_diag[f.index()]).then_some((f, new_c))
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
        let idx = flw.index();
        self.pair_costs.get(idx).map_or(f64::INFINITY, |row| row[idx])
    }

    fn is_resolver_finite(&self, graph: &CausalGraph, _mutex: &MutexTable, search: &SearchState, res: ResolverId) -> bool {
        if !search.is_resolver_alive(graph, res) {
            return false;
        }
        let (eff, _) = graph.effective_resolver(res);
        self.prec_cost(graph, eff) < f64::INFINITY
    }

    fn has_estimated_solution(&self, _graph: &CausalGraph, _mutex: &MutexTable, search: &SearchState) -> bool {
        let agenda: Vec<FlawId> = search.agenda().iter().copied().collect();
        for (i, &f1) in agenda.iter().enumerate() {
            for &f2 in &agenda[i..] {
                if self.pair_cost(f1, f2) == f64::INFINITY {
                    return false;
                }
            }
        }
        true
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
            } else if search.agenda().iter().any(|&ag| mutex.is_flaw_mutex(graph, f, ag)) || self.has_jointly_finite_ancestor(graph, mutex, search, f) {
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

    fn pick_branch(&self, graph: &CausalGraph, mutex: &MutexTable, search: &SearchState) -> Option<(FlawId, ResolverId)> {
        let mut agenda: Vec<FlawId> = search.agenda().iter().copied().collect();
        if agenda.is_empty() {
            return None;
        }
        agenda.sort_unstable();

        // Select the hardest pair (f1, f2) in the agenda.
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

        // Between f1 and f2, pick the flaw with fewer alive resolvers (fail-first), breaking ties by higher diagonal cost.
        let (f1, f2) = worst_pair;
        let best_flaw = if f1 == f2 {
            f1
        } else {
            let alive_count = |f: FlawId| graph.flaw(f).resolvers.iter().filter(|&&r| search.is_resolver_alive(graph, r)).count();
            match alive_count(f1).cmp(&alive_count(f2)) {
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

        // Pick the resolver minimizing the worst joint h^2 cost against every other flaw in the agenda.
        let mut best_res = None;
        let mut best_score = f64::INFINITY;
        let mut best_diag = f64::INFINITY;

        for &r1 in &graph.flaw(best_flaw).resolvers {
            if !search.is_resolver_alive(graph, r1) {
                continue;
            }
            let (s1, w1) = graph.effective_resolver(r1);
            let p1 = self.prec_cost(graph, s1);
            let diag = w1 + p1;
            let mut score = diag;

            if score < f64::INFINITY {
                for &other in &agenda {
                    if other == best_flaw {
                        continue;
                    }
                    let mut min_with_other = f64::INFINITY;
                    for &r2 in &graph.flaw(other).resolvers {
                        if !search.is_resolver_alive(graph, r2) {
                            continue;
                        }
                        let (s2, _) = graph.effective_resolver(r2);
                        let p2 = self.prec_cost(graph, s2);
                        if p2 == f64::INFINITY {
                            continue;
                        }
                        let c = self.resolver_pair_cost(graph, mutex, r1, r2, p1, p2, min_with_other);
                        if c < min_with_other {
                            min_with_other = c;
                        }
                    }
                    if min_with_other > score {
                        score = min_with_other;
                    }
                }
            }

            if best_res.is_none() || score.total_cmp(&best_score) == Ordering::Less || (score.total_cmp(&best_score) == Ordering::Equal && diag.total_cmp(&best_diag) == Ordering::Less) {
                best_score = score;
                best_diag = diag;
                best_res = Some(r1);
            }
        }

        let best_res = best_res.expect("Active flaw in agenda must have at least one alive resolver");
        Some((best_flaw, best_res))
    }
}
