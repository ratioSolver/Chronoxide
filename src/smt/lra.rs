use crate::smt::{ast::BoolExpr, rational::Rational};
use std::collections::{BTreeMap, HashMap};

pub(super) struct LraTheory {
    ints: Vec<bool>,                                              // Distinguish between integer and real variables
    reals: Vec<Rational>,                                         // Current assignments of real variables
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
}
