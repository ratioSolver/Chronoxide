use crate::{InfRational, Lin};
use std::collections::{BTreeMap, HashMap, HashSet};

pub struct Constraint {
    lbs: HashMap<usize, InfRational>,
    ubs: HashMap<usize, InfRational>,
}

struct Var {
    val: InfRational,
    lbs: BTreeMap<InfRational, HashSet<usize>>,
    ubs: BTreeMap<InfRational, HashSet<usize>>,
    rows: HashSet<usize>,
}

impl Var {
    pub fn new() -> Self {
        Self {
            val: InfRational::from_integer(0),
            lbs: BTreeMap::new(),
            ubs: BTreeMap::new(),
            rows: HashSet::new(),
        }
    }

    pub fn value(&self) -> InfRational {
        self.val
    }

    pub fn lb(&self) -> Option<&InfRational> {
        self.lbs.keys().next_back()
    }

    pub fn ub(&self) -> Option<&InfRational> {
        self.ubs.keys().next()
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} [{}, {}]",
            self.val,
            match self.lb() {
                Some(lb) => lb.to_string(),
                None => "-∞".to_string(),
            },
            match self.ub() {
                Some(ub) => ub.to_string(),
                None => "∞".to_string(),
            }
        )
    }
}

pub struct Solver {
    vars: Vec<Var>,
    tableau: BTreeMap<usize, Lin>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            vars: Vec::new(),
            tableau: BTreeMap::new(),
        }
    }

    pub fn new_var(&mut self) -> usize {
        let var = Var::new();
        self.vars.push(var);
        self.vars.len() - 1
    }

    pub fn value(&self, v: usize) -> InfRational {
        self.vars[v].value()
    }

    pub fn lb(&self, v: usize) -> InfRational {
        match self.vars[v].lb() {
            Some(lb) => lb.clone(),
            None => InfRational::NEGATIVE_INFINITY,
        }
    }

    pub fn ub(&self, v: usize) -> InfRational {
        match self.vars[v].ub() {
            Some(ub) => ub.clone(),
            None => InfRational::POSITIVE_INFINITY,
        }
    }

    pub fn lb_lin(&self, l: &Lin) -> InfRational {
        let mut lb = InfRational::from_rational(*l.known_term());
        for (v, coeff) in l.vars() {
            if coeff >= 0 {
                lb += coeff * self.lb(*v);
            } else {
                lb += coeff * self.ub(*v);
            }
            if lb == InfRational::NEGATIVE_INFINITY {
                break;
            }
        }
        lb
    }

    pub fn ub_lin(&self, l: &Lin) -> InfRational {
        let mut ub = InfRational::from_rational(*l.known_term());
        for (v, coeff) in l.vars() {
            if coeff >= 0 {
                ub += coeff * self.ub(*v);
            } else {
                ub += coeff * self.lb(*v);
            }
            if ub == InfRational::POSITIVE_INFINITY {
                break;
            }
        }
        ub
    }

    pub fn new_lt(&mut self, lhs: &Lin, rhs: &Lin, strict: bool, reason: Option<&Constraint>) {
        let mut expr = lhs - rhs;
        // Remove basic variables from the expression and substitute with their tableau expressions
        for v in expr.vars().keys().cloned().collect::<Vec<usize>>() {
            if let Some(row) = self.tableau.get(&v) {
                expr.substitute(v, row);
            }
        }

        unimplemented!()
    }
}

impl std::fmt::Display for Solver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Variables:")?;
        for (i, var) in self.vars.iter().enumerate() {
            writeln!(f, "  x{}: {}", i, var)?;
        }
        writeln!(f, "Tableau:")?;
        for (v, lin) in &self.tableau {
            writeln!(f, "  x{} = {}", v, lin)?;
        }
        Ok(())
    }
}
