use crate::InfRational;
use std::collections::{BTreeMap, HashSet};

/// Represents a variable in the linear solver.
///
/// It maintains the current value of the variable, as well as the set of active
/// lower and upper bounds with their associated reasons (constraints).
pub(super) struct Var {
    /// The current value assigned to the variable.
    val: InfRational,
    /// A map from lower bound values to the set of reasons (constraint indices) that imply them.
    lbs: BTreeMap<InfRational, HashSet<usize>>,
    /// A map from upper bound values to the set of reasons (constraint indices) that imply them.
    ubs: BTreeMap<InfRational, HashSet<usize>>,
    /// The set of row indices in the tableau where this variable appears.
    rows: HashSet<usize>,
}

impl Var {
    /// Creates a new variable with value 0 and no bounds ((-∞, +∞)).
    pub fn new() -> Self {
        Self {
            val: InfRational::from_integer(0),
            lbs: BTreeMap::new(),
            ubs: BTreeMap::new(),
            rows: HashSet::new(),
        }
    }

    /// Returns the current value of the variable.
    pub fn value(&self) -> InfRational {
        self.val
    }

    /// Returns the active lower bound of the variable.
    ///
    /// This returns the smallest lower bound currently stored.
    pub fn lb(&self) -> InfRational {
        match self.lbs.iter().next() {
            Some((lb, _)) => *lb,
            None => InfRational::NEGATIVE_INFINITY,
        }
    }

    /// Returns the active upper bound of the variable.
    ///
    /// This returns the largest upper bound currently stored.
    pub fn ub(&self) -> InfRational {
        match self.ubs.iter().next_back() {
            Some((ub, _)) => *ub,
            None => InfRational::POSITIVE_INFINITY,
        }
    }

    /// Adds a lower bound to the variable.
    ///
    /// # Arguments
    ///
    /// * `lb` - The lower bound value.
    /// * `reason` - The index of the constraint explaining this bound.
    ///              If `None`, it treats the bound as a global update and removes weaker lower bounds.
    ///
    /// # Panics
    ///
    /// Panics if the new lower bound is greater than the current upper bound.
    pub(super) fn set_lb(&mut self, lb: InfRational, reason: Option<usize>) {
        assert!(lb <= self.ub());
        match reason {
            Some(r) => {
                // we add a new lower bound `lb` with the given reason..
                self.lbs.entry(lb).or_default().insert(r);
            }
            None => {
                // we remove all the lower bounds that are less than `lb`..
                let to_remove: Vec<InfRational> = self.lbs.keys().cloned().take_while(|&b| b < lb).collect();
                for b in to_remove {
                    self.lbs.remove(&b);
                }
            }
        }
    }

    /// Removes a reason for a specific lower bound.
    ///
    /// If the bound has no more reasons associated with it, it is removed.
    ///
    /// # Panics
    ///
    /// Panics if the bound `lb` is not present.
    pub(super) fn unset_lb(&mut self, lb: InfRational, reason: usize) {
        assert!(self.lbs.contains_key(&lb));
        if let Some(reasons) = self.lbs.get_mut(&lb) {
            reasons.remove(&reason);
            if reasons.is_empty() {
                self.lbs.remove(&lb);
            }
        }
    }

    /// Adds an upper bound to the variable.
    ///
    /// # Arguments
    ///
    /// * `ub` - The upper bound value.
    /// * `reason` - The index of the constraint explaining this bound.
    ///              If `None`, it treats the bound as a global update and removes weaker upper bounds.
    ///
    /// # Panics
    ///
    /// Panics if the new upper bound is less than the current lower bound.
    pub(super) fn set_ub(&mut self, ub: InfRational, reason: Option<usize>) {
        assert!(ub >= self.lb());
        match reason {
            Some(r) => {
                // we add a new upper bound `ub` with the given reason..
                self.ubs.entry(ub).or_default().insert(r);
            }
            None => {
                // we remove all the upper bounds that are greater than `ub`..
                let to_remove: Vec<InfRational> = self.ubs.keys().cloned().rev().take_while(|&b| b > ub).collect();
                for b in to_remove {
                    self.ubs.remove(&b);
                }
            }
        }
    }

    /// Removes a reason for a specific upper bound.
    ///
    /// If the bound has no more reasons associated with it, it is removed.
    ///
    /// # Panics
    ///
    /// Panics if the bound `ub` is not present.
    pub(super) fn unset_ub(&mut self, ub: InfRational, reason: usize) {
        assert!(self.ubs.contains_key(&ub));
        if let Some(reasons) = self.ubs.get_mut(&ub) {
            reasons.remove(&reason);
            if reasons.is_empty() {
                self.ubs.remove(&ub);
            }
        }
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} [{}, {}]", self.val, self.lb(), self.ub())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_var() {
        let v = Var::new();
        assert_eq!(v.value(), InfRational::from_integer(0));
        assert_eq!(v.lb(), InfRational::NEGATIVE_INFINITY);
        assert_eq!(v.ub(), InfRational::POSITIVE_INFINITY);
    }

    #[test]
    fn test_lb() {
        let mut v = Var::new();
        let val1 = InfRational::from_integer(10);
        let val2 = InfRational::from_integer(20);

        v.set_lb(val1, Some(1));
        assert_eq!(v.lb(), val1);

        v.set_lb(val2, Some(2));
        assert_eq!(v.lb(), val1);

        v.unset_lb(val1, 1);
        assert_eq!(v.lb(), val2);

        v.unset_lb(val2, 2);
        assert_eq!(v.lb(), InfRational::NEGATIVE_INFINITY);
    }

    #[test]
    fn test_ub() {
        let mut v = Var::new();
        let val1 = InfRational::from_integer(10);
        let val2 = InfRational::from_integer(20);

        v.set_ub(val2, Some(1));
        assert_eq!(v.ub(), val2);

        v.set_ub(val1, Some(2));
        assert_eq!(v.ub(), val2);

        v.unset_ub(val2, 1);
        assert_eq!(v.ub(), val1);

        v.unset_ub(val1, 2);
        assert_eq!(v.ub(), InfRational::POSITIVE_INFINITY);
    }

    #[test]
    #[should_panic]
    fn test_invalid_lb() {
        let mut v = Var::new();
        v.set_ub(InfRational::from_integer(10), Some(1));
        v.set_lb(InfRational::from_integer(11), Some(2));
    }

    #[test]
    #[should_panic]
    fn test_invalid_ub() {
        let mut v = Var::new();
        v.set_lb(InfRational::from_integer(10), Some(1));
        v.set_ub(InfRational::from_integer(9), Some(2));
    }
}
