use crate::smt::sat_solver::Lit;
use std::collections::{HashMap, HashSet};

pub(super) struct EnumTheory {
    pub initial_domains: Vec<HashSet<i32>>,
    pub active_domains: Vec<HashSet<i32>>,

    trail: Vec<(usize, i32)>,
    trail_lim: Vec<usize>,

    removal_reasons: HashMap<(usize, i32), Lit>,
}

impl EnumTheory {
    pub fn new() -> Self {
        Self {
            initial_domains: Vec::new(),
            active_domains: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            removal_reasons: HashMap::new(),
        }
    }

    pub fn mk_var(&mut self, domain: HashSet<i32>) -> usize {
        let id = self.initial_domains.len();
        self.initial_domains.push(domain.clone());
        self.active_domains.push(domain);
        id
    }

    pub fn push(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    pub fn cancel_until(&mut self, level: usize) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];
        while self.trail.len() > target_len {
            let (var, val) = self.trail.pop().expect("Enum trail underflow");
            self.active_domains[var].insert(val);
            self.removal_reasons.remove(&(var, val));
        }
        self.trail_lim.truncate(level);
    }

    pub fn set_eq(&mut self, lit: Option<Lit>, var: usize, val: i32, is_eq: bool) -> Result<bool, Vec<Lit>> {
        if is_eq {
            if !self.active_domains[var].contains(&val) {
                // CONFLITTO: `val` era già stato escluso dal dominio.
                let mut conflict = Vec::with_capacity(2);
                if let Some(l) = lit {
                    conflict.push(!l);
                }
                if let Some(&reason) = self.removal_reasons.get(&(var, val)) {
                    conflict.push(!reason);
                }
                return Err(conflict);
            }

            let to_remove: Vec<i32> = self.active_domains[var].iter().filter(|&&v| v != val).copied().collect();

            if to_remove.is_empty() {
                return Ok(false);
            }

            for v in to_remove {
                self.active_domains[var].remove(&v);
                self.trail.push((var, v));
                if let Some(l) = lit {
                    self.removal_reasons.insert((var, v), l);
                }
            }
            Ok(true)
        } else {
            if !self.active_domains[var].contains(&val) {
                return Ok(false); // Già rimosso in precedenza
            }

            self.active_domains[var].remove(&val);
            self.trail.push((var, val));
            if let Some(l) = lit {
                self.removal_reasons.insert((var, val), l);
            }

            if self.active_domains[var].is_empty() {
                let mut conflict = Vec::new();
                if let Some(l) = lit {
                    conflict.push(!l);
                }

                for &v in &self.initial_domains[var] {
                    if v != val {
                        if let Some(&reason) = self.removal_reasons.get(&(var, v)) {
                            if !conflict.contains(&!reason) {
                                conflict.push(!reason);
                            }
                        }
                    }
                }
                return Err(conflict);
            }
            Ok(true)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::sat_solver::Lit;

    fn setup_enum() -> (EnumTheory, usize) {
        let mut theory = EnumTheory::new();
        let domain: HashSet<i32> = vec![1, 2, 3].into_iter().collect();
        let var = theory.mk_var(domain);
        (theory, var)
    }

    #[test]
    fn test_enum_exhaustive_denial_conflict() {
        let (mut theory, var) = setup_enum();

        let lit1 = Lit::new(1, false); // SAT deduce: var != 1
        let lit2 = Lit::new(2, false); // SAT deduce: var != 2
        let lit3 = Lit::new(3, false); // SAT deduce: var != 3

        assert_eq!(theory.set_eq(Some(lit1), var, 1, false), Ok(true));
        assert_eq!(theory.set_eq(Some(lit2), var, 2, false), Ok(true));

        let res3 = theory.set_eq(Some(lit3), var, 3, false);
        assert!(res3.is_err());

        let conflict = res3.unwrap_err();

        assert_eq!(conflict.len(), 3);
        assert!(conflict.contains(&!lit1));
        assert!(conflict.contains(&!lit2));
        assert!(conflict.contains(&!lit3));
    }

    #[test]
    fn test_enum_positive_contradiction() {
        let (mut theory, var) = setup_enum();

        let lit_deny = Lit::new(1, false);
        let lit_assert = Lit::new(2, false);

        assert_eq!(theory.set_eq(Some(lit_deny), var, 1, false), Ok(true));

        let res_assert = theory.set_eq(Some(lit_assert), var, 1, true);
        assert!(res_assert.is_err());

        let conflict = res_assert.unwrap_err();

        assert!(conflict.contains(&!lit_assert));
        assert!(conflict.contains(&!lit_deny));
    }

    #[test]
    fn test_enum_positive_assignment_removes_others() {
        let (mut theory, var) = setup_enum();

        let lit_set_1 = Lit::new(1, false);
        let lit_set_2 = Lit::new(2, false);

        assert_eq!(theory.set_eq(Some(lit_set_1), var, 1, true), Ok(true));
        assert_eq!(theory.active_domains[var].len(), 1);
        assert!(theory.active_domains[var].contains(&1));

        let res_set_2 = theory.set_eq(Some(lit_set_2), var, 2, true);
        assert!(res_set_2.is_err());

        let conflict = res_set_2.unwrap_err();

        assert!(conflict.contains(&!lit_set_2));
        assert!(conflict.contains(&!lit_set_1));
    }

    #[test]
    fn test_enum_backtracking_recovers_domain() {
        let (mut theory, var) = setup_enum();
        let lit1 = Lit::new(1, false);

        theory.push();

        assert_eq!(theory.set_eq(Some(lit1), var, 1, false), Ok(true));
        assert_eq!(theory.active_domains[var].len(), 2);

        theory.cancel_until(0);

        assert_eq!(theory.active_domains[var].len(), 3);
        assert!(!theory.removal_reasons.contains_key(&(var, 1)));

        assert_eq!(theory.set_eq(Some(lit1), var, 1, false), Ok(true));
    }
}
