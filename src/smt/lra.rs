use crate::smt::{
    rational::{InfRational, Rational},
    sat::Lit,
};
use std::collections::{BTreeMap, HashMap, HashSet};

pub(super) struct LraTheory {
    ints: Vec<bool>,                                                         // Distinguish between integer and real variables
    reals: Vec<InfRational>,                                                 // Current assignments of real variables
    lbs: Vec<InfRational>,                                                   // Current assignments of lower bounds
    ubs: Vec<InfRational>,                                                   // Current assignments of upper bounds
    pub(super) lin_to_slack: HashMap<BTreeMap<usize, rug::Rational>, usize>, // Mapping from linear constraints to their corresponding slack variable
    pub(super) tableau: BTreeMap<usize, BTreeMap<usize, rug::Rational>>,     // Tableau for linear constraints
    t_watches: Vec<HashSet<usize>>,                                          // For each variable, the set of tableau rows that watch it (i.e., contain it in their expression)
    bound_trail: Vec<BoundUpdate>,                                           // Trail of bound updates for backtracking
    trail_lim: Vec<usize>,                                                   // Indices in the trail where decisions were made
}

impl LraTheory {
    pub(super) fn new() -> Self {
        LraTheory {
            ints: Vec::new(),
            reals: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            lin_to_slack: HashMap::new(),
            tableau: BTreeMap::new(),
            bound_trail: Vec::new(),
            t_watches: Vec::new(),
            trail_lim: Vec::new(),
        }
    }

    pub(super) fn mk_int(&mut self) -> usize {
        let var_index = self.ints.len();
        self.ints.push(true);
        self.reals.push(InfRational::new(Rational::Finite(rug::Rational::from(0)), rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(InfRational::new(Rational::NegativeInf, rug::Rational::from(0))); // Initialize lower bound to -inf
        self.ubs.push(InfRational::new(Rational::PositiveInf, rug::Rational::from(0))); // Initialize upper bound to +inf
        self.t_watches.push(HashSet::new());
        var_index
    }

    pub(super) fn mk_real(&mut self) -> usize {
        let var_index = self.reals.len();
        self.ints.push(false);
        self.reals.push(InfRational::new(Rational::Finite(rug::Rational::from(0)), rug::Rational::from(0))); // Initialize with 0
        self.lbs.push(InfRational::new(Rational::NegativeInf, rug::Rational::from(0))); // Initialize lower bound to -inf
        self.ubs.push(InfRational::new(Rational::PositiveInf, rug::Rational::from(0))); // Initialize upper bound to +inf
        self.t_watches.push(HashSet::new());
        var_index
    }

    pub(super) fn value(&self, var: usize) -> &InfRational {
        self.reals.get(var).expect("Variable index out of bounds")
    }

    pub(super) fn lb(&self, var: usize) -> &InfRational {
        self.lbs.get(var).expect("Variable index out of bounds")
    }

    pub(super) fn ub(&self, var: usize) -> &InfRational {
        self.ubs.get(var).expect("Variable index out of bounds")
    }

    pub(super) fn set_lb(&mut self, lit: Lit, var: usize, new_lb: InfRational) -> bool {
        if &new_lb < self.lb(var) {
            return true;
        }
        if &new_lb > self.ub(var) {
            return false;
        }
        self.bound_trail.push(BoundUpdate::LowerBound { var, val: self.lbs[var].clone() });
        self.lbs[var] = new_lb.clone();

        if self.value(var) < &new_lb && !self.is_basic(var) {
            self.update(var, new_lb);
        }
        true
    }

    pub(super) fn set_ub(&mut self, lit: Lit, var: usize, new_ub: InfRational) -> bool {
        if &new_ub > self.ub(var) {
            return true;
        }
        if &new_ub < self.lb(var) {
            return false;
        }
        self.bound_trail.push(BoundUpdate::UpperBound { var, val: self.ubs[var].clone() });
        self.ubs[var] = new_ub.clone();

        if self.value(var) > &new_ub && !self.is_basic(var) {
            self.update(var, new_ub);
        }
        true
    }

    fn is_basic(&self, var: usize) -> bool {
        self.tableau.contains_key(&var)
    }

    fn update(&mut self, var: usize, new_value: InfRational) {
        assert!(!self.is_basic(var), "Cannot directly update a basic variable");
        assert!(&new_value >= self.lb(var) && &new_value <= self.ub(var), "New value must be within bounds");

        for &watch in &self.t_watches[var] {
            let delta = (&new_value - self.value(var)) * &self.tableau[&watch][&var];
            self.reals[watch] += delta;
        }

        self.reals[var] = new_value;
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.bound_trail.len());
    }

    pub(super) fn backtrack_until(&mut self, level: usize) {
        if level < self.trail_lim.len() {
            let target_len = self.trail_lim[level];

            while self.bound_trail.len() > target_len {
                let undo_action = self.bound_trail.pop().unwrap();
                match undo_action {
                    BoundUpdate::LowerBound { var, val: old_value } => {
                        self.lbs[var] = old_value;
                    }
                    BoundUpdate::UpperBound { var, val: old_value } => {
                        self.ubs[var] = old_value;
                    }
                }
            }

            self.trail_lim.truncate(level);
        }
    }
}

enum BoundUpdate {
    LowerBound { var: usize, val: InfRational },
    UpperBound { var: usize, val: InfRational },
}
