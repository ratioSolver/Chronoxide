use crate::smt::{ast::BoolExpr, rational::Rational};
use std::collections::{BTreeMap, HashMap};

pub(super) struct LraTheory {
    ints: Vec<bool>,                                              // Distinguish between integer and real variables
    reals: Vec<rug::Rational>,                                    // Current assignments of real variables
    lbs: Vec<Rational>,                                           // Current assignments of lower bounds
    ubs: Vec<Rational>,                                           // Current assignments of upper bounds
    lin_to_slack: HashMap<BTreeMap<usize, rug::Rational>, usize>, // Mapping from linear constraints to their corresponding slack variable
    tableau: BTreeMap<usize, BTreeMap<usize, rug::Rational>>,     // Tableau for linear constraints
    bound_trail: Vec<BoolExpr>,                                   // Trail of bound updates for backtracking
    trail_lim: Vec<usize>,                                        // Indices in the trail where decisions were made
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
            trail_lim: Vec::new(),
        }
    }

    pub(super) fn mk_int(&mut self) -> usize {
        let var_index = self.ints.len();
        self.ints.push(true);
        self.reals.push(rug::Rational::from(0)); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        var_index
    }

    pub(super) fn mk_real(&mut self) -> usize {
        let var_index = self.reals.len();
        self.ints.push(false);
        self.reals.push(rug::Rational::from(0)); // Initialize with 0
        self.lbs.push(Rational::NegativeInf); // Initialize lower bound to -inf
        self.ubs.push(Rational::PositiveInf); // Initialize upper bound to +inf
        var_index
    }

    pub(super) fn value(&self, var: usize) -> &rug::Rational {
        self.reals.get(var).expect("Variable index out of bounds")
    }

    pub(super) fn lb(&self, var: usize) -> &Rational {
        self.lbs.get(var).expect("Variable index out of bounds")
    }

    pub(super) fn ub(&self, var: usize) -> &Rational {
        self.ubs.get(var).expect("Variable index out of bounds")
    }
}
