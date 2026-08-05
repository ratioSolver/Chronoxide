use crate::smt::{
    rational::{InfRational, Rational},
    sat::Lit,
};
use rug::Rational as RugRational;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    mem,
};

pub(super) struct LraTheory {
    ints: Vec<bool>,                                                       // true = integer variable, false = real variable
    reals: Vec<InfRational>,                                               // Current assignments
    lbs: Vec<(Option<Lit>, InfRational)>,                                  // Current lower bounds
    ubs: Vec<(Option<Lit>, InfRational)>,                                  // Current upper bounds
    pub(super) lin_to_slack: HashMap<BTreeMap<usize, RugRational>, usize>, // Mapping from linear constraints to their slack variable
    pub(super) tableau: BTreeMap<usize, BTreeMap<usize, RugRational>>,     // Tableau: basic variable -> linear expression over non-basic variables
    t_watches: Vec<HashSet<usize>>,                                        // For each variable, the set of tableau rows containing it
    bound_trail: Vec<BoundUpdate>,                                         // Trail of bound updates for backtracking
    trail_lim: Vec<usize>,                                                 // Trail limits
}

impl LraTheory {
    pub(super) fn new() -> Self {
        Self {
            ints: Vec::new(),
            reals: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            lin_to_slack: HashMap::new(),
            tableau: BTreeMap::new(),
            t_watches: Vec::new(),
            bound_trail: Vec::new(),
            trail_lim: Vec::new(),
        }
    }

    pub(super) fn mk_int(&mut self) -> usize {
        self.mk_var(true)
    }

    pub(super) fn mk_real(&mut self) -> usize {
        self.mk_var(false)
    }

    fn mk_var(&mut self, is_int: bool) -> usize {
        let var = self.reals.len();

        self.ints.push(is_int);
        self.reals.push(Self::zero());
        self.lbs.push((None, Self::negative_inf()));
        self.ubs.push((None, Self::positive_inf()));
        self.t_watches.push(HashSet::new());

        var
    }

    fn zero() -> InfRational {
        InfRational::new(Rational::Finite(RugRational::from(0)), RugRational::from(0))
    }

    fn negative_inf() -> InfRational {
        InfRational::new(Rational::NegativeInf, RugRational::from(0))
    }

    fn positive_inf() -> InfRational {
        InfRational::new(Rational::PositiveInf, RugRational::from(0))
    }

    pub(super) fn value(&self, var: usize) -> &InfRational {
        self.reals.get(var).expect("variable index out of bounds")
    }

    pub(super) fn lb(&self, var: usize) -> &InfRational {
        &self.lbs.get(var).expect("variable index out of bounds").1
    }

    pub(super) fn ub(&self, var: usize) -> &InfRational {
        &self.ubs.get(var).expect("variable index out of bounds").1
    }

    pub(super) fn is_int(&self, var: usize) -> bool {
        *self.ints.get(var).expect("variable index out of bounds")
    }

    pub(super) fn set_lb(&mut self, lit: Lit, var: usize, new_lb: InfRational) -> bool {
        assert!(var < self.reals.len(), "variable index out of bounds: {var}");

        if &new_lb <= self.lb(var) {
            return true;
        }

        if &new_lb > self.ub(var) {
            return false;
        }

        let (Some(c_lit), val) = self.lbs[var].clone() else {
            panic!("lower bound should have a guard literal");
        };
        self.bound_trail.push(BoundUpdate::LowerBound { lit: c_lit, var, val });

        self.lbs[var] = (Some(lit), new_lb.clone());

        if self.value(var) < &new_lb && !self.is_basic(var) {
            self.update(var, new_lb);
        }

        true
    }

    pub(super) fn set_ub(&mut self, lit: Lit, var: usize, new_ub: InfRational) -> bool {
        assert!(var < self.reals.len(), "variable index out of bounds: {var}");

        if &new_ub >= self.ub(var) {
            return true;
        }

        if &new_ub < self.lb(var) {
            return false;
        }

        let (Some(c_lit), val) = self.ubs[var].clone() else {
            panic!("upper bound should have a guard literal");
        };
        self.bound_trail.push(BoundUpdate::UpperBound { lit: c_lit, var, val });

        self.ubs[var] = (Some(lit), new_ub.clone());

        if self.value(var) > &new_ub && !self.is_basic(var) {
            self.update(var, new_ub);
        }

        true
    }

    fn is_basic(&self, var: usize) -> bool {
        self.tableau.contains_key(&var)
    }

    fn update(&mut self, var: usize, new_value: InfRational) {
        assert!(var < self.reals.len(), "variable index out of bounds: {var}");
        assert!(!self.is_basic(var), "cannot directly update a basic variable");
        assert!(&new_value >= self.lb(var) && &new_value <= self.ub(var), "new value must be within bounds");

        let old_value = self.reals[var].clone();
        let delta_var = &new_value - &old_value;

        if delta_var == Self::zero() {
            return;
        }

        let watched_rows: Vec<usize> = self.t_watches[var].iter().copied().collect();

        for row_var in watched_rows {
            let coeff = self.tableau[&row_var][&var].clone();
            let delta = &delta_var * &coeff;
            self.reals[row_var] += delta;
        }

        self.reals[var] = new_value;
    }

    pub fn check(&mut self) -> Result<(), Vec<Lit>> {
        loop {
            // we search for a basic variable whose value is not within its bounds..
            let var = self.tableau.iter().find_map(|(&var, _)| {
                if self.value(var) < self.lb(var) {
                    Some((var, self.lb(var).clone()))
                } else if self.value(var) > self.ub(var) {
                    Some((var, self.ub(var).clone()))
                } else {
                    None
                }
            });
            if let Some((leaving, val)) = var {
                // .. if we find one, we try to pivot it with a non-basic variable that can take it back within bounds
                if self.value(leaving) < &val {
                    let entering = self.tableau[&leaving].iter().find_map(|(&v, coeff)| if coeff.is_positive() && self.value(v) < self.ub(v) || coeff.is_negative() && self.value(v) > self.lb(v) { Some(v) } else { None });
                    if let Some(entering) = entering {
                        self.pivot_and_update(entering, leaving, val.clone());
                    } else {
                        let mut conflict = Vec::new();
                        for (vr, vl) in &self.tableau[&leaving] {
                            if vl.is_positive() {
                                conflict.push(self.ubs[*vr].0.expect("upper bound should have a guard literal"));
                            } else if vl.is_negative() {
                                conflict.push(self.lbs[*vr].0.expect("lower bound should have a guard literal"));
                            }
                        }
                        conflict.push(self.lbs[leaving].0.expect("lower bound should have a guard literal"));
                        return Err(conflict);
                    }
                }
                if self.value(leaving) > &val {
                    let entering = self.tableau[&leaving].iter().find_map(|(&v, coeff)| if coeff.is_positive() && self.value(v) > self.lb(v) || coeff.is_negative() && self.value(v) < self.ub(v) { Some(v) } else { None });
                    if let Some(entering) = entering {
                        self.pivot_and_update(entering, leaving, val);
                    } else {
                        let mut conflict = Vec::new();
                        for (vr, vl) in &self.tableau[&leaving] {
                            if vl.is_positive() {
                                conflict.push(self.lbs[*vr].0.expect("lower bound should have a guard literal"));
                            } else if vl.is_negative() {
                                conflict.push(self.ubs[*vr].0.expect("upper bound should have a guard literal"));
                            }
                        }
                        conflict.push(self.ubs[leaving].0.expect("upper bound should have a guard literal"));
                        return Err(conflict);
                    }
                }
            } else {
                return Ok(()); // all basic variables are within bounds, we are done
            }
        }
    }

    fn pivot(&mut self, entering: usize, leaving: usize) {
        assert!(entering < self.reals.len(), "variable index out of bounds: {entering}");
        assert!(leaving < self.reals.len(), "variable index out of bounds: {leaving}");
        assert!(self.is_basic(leaving), "leaving variable must be basic");
        assert!(!self.is_basic(entering), "entering variable must be non-basic");

        let leaving_row_vars: Vec<usize> = self.tableau[&leaving].keys().copied().collect();

        for var in leaving_row_vars {
            self.t_watches[var].remove(&leaving);
        }

        let mut new_row = self.tableau.remove(&leaving).expect("leaving variable must have a tableau row");

        let pivot_coeff = new_row.remove(&entering).expect("entering variable must occur in leaving row");
        assert!(!pivot_coeff.is_zero(), "pivot coefficient must be non-zero");

        let minus_pivot = -pivot_coeff.clone();

        for coeff in new_row.values_mut() {
            *coeff /= &minus_pivot;
        }

        new_row.insert(leaving, pivot_coeff.recip());

        let affected_rows: Vec<usize> = mem::take(&mut self.t_watches[entering]).into_iter().collect();

        for row_var in affected_rows {
            if row_var == leaving {
                continue;
            }

            let Some(row) = self.tableau.get_mut(&row_var) else {
                continue;
            };

            let Some(coeff_entering) = row.remove(&entering) else {
                continue;
            };

            for (v, coeff_new_row) in &new_row {
                let delta = coeff_new_row * coeff_entering.clone();

                if delta.is_zero() {
                    continue;
                }

                if let Some(old_coeff) = row.get_mut(v) {
                    *old_coeff += delta;

                    if old_coeff.is_zero() {
                        row.remove(v);
                        self.t_watches[*v].remove(&row_var);
                    }
                } else {
                    row.insert(*v, delta);
                    self.t_watches[*v].insert(row_var);
                }
            }
        }

        for v in new_row.keys().copied() {
            self.t_watches[v].insert(entering);
        }

        self.tableau.insert(entering, new_row);
    }

    fn pivot_and_update(&mut self, entering: usize, leaving: usize, new_value: InfRational) {
        assert!(entering < self.reals.len(), "variable index out of bounds: {entering}");
        assert!(leaving < self.reals.len(), "variable index out of bounds: {leaving}");
        assert!(self.is_basic(leaving), "leaving variable must be basic");
        assert!(!self.is_basic(entering), "entering variable must be non-basic");
        assert!(&new_value >= self.lb(leaving) && &new_value <= self.ub(leaving), "new value for leaving variable must be within bounds");

        let pivot_coeff = self.tableau[&leaving][&entering].clone();
        assert!(!pivot_coeff.is_zero(), "pivot coefficient must be non-zero");

        let theta = (&new_value - self.value(leaving)) / &pivot_coeff;

        self.reals[leaving] = new_value;
        self.reals[entering] += &theta;

        let affected_rows: Vec<usize> = self.t_watches[entering].iter().copied().collect();

        for row_var in affected_rows {
            if row_var == leaving {
                continue;
            }

            let Some(row) = self.tableau.get(&row_var) else {
                continue;
            };

            let Some(coeff) = row.get(&entering) else {
                continue;
            };

            self.reals[row_var] += &theta * coeff;
        }

        self.pivot(entering, leaving);
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.bound_trail.len());
    }

    pub(super) fn backtrack_until(&mut self, level: usize) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];

        while self.bound_trail.len() > target_len {
            let update = self.bound_trail.pop().expect("trail should contain an update");

            match update {
                BoundUpdate::LowerBound { lit, var, val } => {
                    self.lbs[var] = (Some(lit), val);
                }
                BoundUpdate::UpperBound { lit, var, val } => {
                    self.ubs[var] = (Some(lit), val);
                }
            }
        }

        self.trail_lim.truncate(level);
    }
}

enum BoundUpdate {
    LowerBound { lit: Lit, var: usize, val: InfRational },
    UpperBound { lit: Lit, var: usize, val: InfRational },
}
