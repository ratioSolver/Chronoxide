use crate::graph::{CausalGraph, FlawId, ResolverId};
use semitone::Lit;
use std::collections::HashSet;

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

/// Monotone, symmetric, downward-closed mutual exclusion relation over resolvers.
pub(crate) struct MutexTable {
    res_mutex: Vec<BitSet>,
    /// Direct impliers of each resolver `r`: every `r'` such that `r' → r`
    /// (resolvers of flaws caused by `r` and causal links pointing to `r`).
    impliers: Vec<Vec<ResolverId>>,
}

impl MutexTable {
    pub(crate) fn new() -> Self {
        Self { res_mutex: Vec::new(), impliers: Vec::new() }
    }

    /// Registers a newly created resolver:
    /// 1) records it as an implier of each cause and inherits their mutexes,
    /// 2) marks it mutually exclusive with all existing sibling resolvers of the same flaw.
    pub(crate) fn on_new_resolver(&mut self, res: ResolverId, causes: &[ResolverId], siblings: &[ResolverId]) {
        debug_assert_eq!(res.index(), self.res_mutex.len(), "MutexTable out of sync with CausalGraph");
        self.res_mutex.push(BitSet::default());
        self.impliers.push(Vec::new());

        for &cause in causes {
            self.impliers[cause].push(res);
            self.inherit_mutexes(res, cause);
        }
        for &sib in siblings {
            self.add_mutex(res, sib);
        }
    }

    /// Records a causal link `res → target` (unidirectional mutex inheritance).
    /// Returns `true` if any new mutex pair was added.
    pub(crate) fn on_causal_link(&mut self, res: ResolverId, target: ResolverId) -> bool {
        self.impliers[target].push(res);
        self.inherit_mutexes(res, target)
    }

    /// Marks `r1` and `r2` as mutually exclusive and closes the relation downward across all impliers.
    /// Returns `true` if at least one new mutex pair was recorded.
    pub(crate) fn add_mutex(&mut self, r1: ResolverId, r2: ResolverId) -> bool {
        if r1 == r2 || self.is_res_mutex(r1, r2) {
            return false;
        }

        let c1 = self.implier_closure(r1);
        let c2 = self.implier_closure(r2);
        let mut changed = false;

        for &a in &c1 {
            let a_idx = a.index();
            for &b in &c2 {
                let b_idx = b.index();
                if a_idx != b_idx && !self.res_mutex[a_idx].contains(b_idx) {
                    self.res_mutex[a_idx].set(b_idx);
                    self.res_mutex[b_idx].set(a_idx);
                    changed = true;
                }
            }
        }

        changed
    }

    /// Extracts conflict-driven resolver mutexes from a learned binary clause `l1 ∨ l2` (`¬(¬l1 ∧ ¬l2)`).
    /// Returns `true` if at least one new mutex pair was recorded.
    pub(crate) fn learn_binary_clause(&mut self, graph: &CausalGraph, l1: Lit, l2: Lit) -> bool {
        if l1 == Lit::FALSE || l2 == Lit::FALSE {
            return false;
        }

        let rs1 = resolvers_implying(graph, !l1);
        if rs1.is_empty() {
            return false;
        }
        let rs2 = resolvers_implying(graph, !l2);
        if rs2.is_empty() {
            return false;
        }

        let mut changed = false;
        for &r1 in &rs1 {
            for &r2 in &rs2 {
                changed |= self.add_mutex(r1, r2);
            }
        }
        changed
    }

    #[inline]
    pub(crate) fn is_res_mutex(&self, r1: ResolverId, r2: ResolverId) -> bool {
        self.res_mutex[r1].contains(r2.index())
    }

    #[inline]
    pub(crate) fn is_flaw_res_mutex(&self, graph: &CausalGraph, flw: FlawId, res: ResolverId) -> bool {
        graph.flaw(flw).causes.iter().any(|&c| self.is_res_mutex(c, res))
    }

    #[inline]
    pub(crate) fn is_flaw_mutex(&self, graph: &CausalGraph, f1: FlawId, f2: FlawId) -> bool {
        f1 != f2 && graph.flaw(f1).causes.iter().any(|&c1| graph.flaw(f2).causes.iter().any(|&c2| self.is_res_mutex(c1, c2)))
    }

    fn inherit_mutexes(&mut self, child: ResolverId, parent: ResolverId) -> bool {
        let closure = self.implier_closure(child);
        let parent_mutexes: Vec<usize> = self.res_mutex[parent].iter_ones().collect();
        let mut changed = false;

        for a in closure {
            let a_idx = a.index();
            for &b_idx in &parent_mutexes {
                if a_idx != b_idx && !self.res_mutex[a_idx].contains(b_idx) {
                    self.res_mutex[a_idx].set(b_idx);
                    self.res_mutex[b_idx].set(a_idx);
                    changed = true;
                }
            }
        }

        changed
    }

    fn implier_closure(&self, root: ResolverId) -> Vec<ResolverId> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![root];

        while let Some(r) = stack.pop() {
            if seen.insert(r) {
                out.push(r);
                stack.extend_from_slice(&self.impliers[r]);
            }
        }

        out
    }
}

/// Collects all resolvers whose activation implies `lit` (either `rho == lit` or `flaw.phi == lit`).
fn resolvers_implying(graph: &CausalGraph, lit: Lit) -> Vec<ResolverId> {
    let mut out = graph.resolvers_by_lit(lit).to_vec();
    for &f in graph.flaws_by_lit(lit) {
        out.extend_from_slice(&graph.flaw(f).resolvers);
    }
    out.sort_unstable();
    out.dedup();
    out
}
