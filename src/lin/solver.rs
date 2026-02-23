use crate::{InfRational, Lin, lin::var::Var};
use std::collections::{BTreeMap, HashMap};

type Callback = Box<dyn Fn(&Solver, usize)>;

struct Updates {
    lbs: HashMap<usize, InfRational>,
    ubs: HashMap<usize, InfRational>,
}

pub struct Solver {
    vars: Vec<Var>,
    updates: Vec<Updates>,
    tableau: BTreeMap<usize, Lin>,
    listeners: HashMap<usize, Vec<Callback>>,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Self {
        Self { vars: Vec::new(), updates: Vec::new(), tableau: BTreeMap::new(), listeners: HashMap::new() }
    }

    pub fn new_var(&mut self) -> usize {
        let var_id = self.vars.len();
        self.vars.push(Var::new());
        var_id
    }

    pub fn new_update(&mut self) -> usize {
        let update_id = self.updates.len();
        self.updates.push(Updates { lbs: HashMap::new(), ubs: HashMap::new() });
        update_id
    }

    pub fn value(&self, v: usize) -> InfRational {
        self.vars[v].value()
    }

    pub fn lb(&self, v: usize) -> InfRational {
        self.vars[v].lb()
    }

    pub fn ub(&self, v: usize) -> InfRational {
        self.vars[v].ub()
    }

    pub fn lin_lb(&self, l: &Lin) -> InfRational {
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

    pub fn lin_ub(&self, l: &Lin) -> InfRational {
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

    pub fn new_lt(&mut self, lhs: &Lin, rhs: &Lin, strict: bool, reason: Option<usize>) {
        let mut expr = lhs - rhs;
        // Remove basic variables from the expression and substitute with their tableau expressions
        for v in expr.vars().keys().cloned().collect::<Vec<usize>>() {
            if let Some(row) = self.tableau.get(&v) {
                expr.substitute(v, row);
            }
        }

        unimplemented!()
    }

    fn set_lb(&mut self, v: usize, lb: InfRational, reason: Option<usize>) {
        if lb > self.vars[v].ub() {
            panic!("Infeasible lower bound");
        }
        unimplemented!()
    }

    fn set_ub(&mut self, v: usize, ub: InfRational, reason: Option<usize>) {
        if ub < self.vars[v].lb() {
            panic!("Infeasible upper bound");
        }
        unimplemented!()
    }

    fn notify(&self, var: usize) {
        if let Some(listeners) = self.listeners.get(&var) {
            for listener in listeners {
                listener(self, var);
            }
        }
    }

    pub fn add_listener<F>(&mut self, var: usize, listener: F)
    where
        F: Fn(&Solver, usize) + 'static,
    {
        self.listeners.entry(var).or_default().push(Box::new(listener));
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
