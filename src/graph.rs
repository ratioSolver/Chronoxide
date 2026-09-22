#[cfg(all(feature = "h_add", feature = "h_max"))]
compile_error!("Features 'h_add' and 'h_max' are mutually exclusive. Please enable only one of them.");
#[cfg(not(any(feature = "h_add", feature = "h_max")))]
compile_error!("Please enable one of the features 'h_add' or 'h_max'.");

use semitone::{
    Lit,
    ast::DlVar,
    rational::{InfRational, Rational},
};
use std::{collections::VecDeque, fmt, ops::Deref};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct FlawId(usize);

impl Deref for FlawId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for FlawId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "f{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct ResolverId(usize);

impl Deref for ResolverId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for ResolverId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}

pub trait Flaw {
    /// Unique identifier of this flaw in the graph.
    fn id(&self) -> FlawId;
    /// Causes for this flaw to exist in the graph.
    fn causes(&self) -> Vec<ResolverId>;

    fn phi(&self) -> Lit;
    fn cost(&self) -> DlVar;

    fn required_by(&self) -> Vec<ResolverId> {
        self.causes()
    }

    /// Resolvers that can potentially solve this flaw.
    fn resolvers(&self) -> Vec<ResolverId>;
}

pub trait Resolver {
    /// Unique identifier of this resolver in the graph.
    fn id(&self) -> ResolverId;
    /// Flaw that this resolver is attempting to solve.
    fn flaw(&self) -> FlawId;

    fn rho(&self) -> Lit;
    fn cost(&self) -> DlVar;

    /// The intrinsic cost of selecting this resolver, independent from the current state of the graph.
    fn intrinsic_cost(&self) -> InfRational;

    /// Preconditions that must be satisfied for this resolver to be applicable.
    fn preconditions(&self) -> Vec<FlawId>;
}

enum Update {
    Flaw(FlawId, f64),
    Resolver(ResolverId, f64),
}

pub struct Graph {
    flaws: Vec<Box<dyn Flaw>>,
    resolvers: Vec<Box<dyn Resolver>>,

    h_flaw: Vec<f64>,
    h_resolver: Vec<f64>,

    trail: Vec<Update>,
    trail_lim: Vec<usize>,
}

impl Graph {
    pub(super) fn new() -> Self {
        Self {
            flaws: Vec::new(),
            resolvers: Vec::new(),

            h_flaw: Vec::new(),
            h_resolver: Vec::new(),

            trail: Vec::new(),
            trail_lim: Vec::new(),
        }
    }

    pub(super) fn push(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    pub(super) fn cancel_until(&mut self, level: usize) {
        if level >= self.trail_lim.len() {
            return;
        }

        let target_len = self.trail_lim[level];
        while self.trail.len() > target_len {
            let update = self.trail.pop().unwrap();
            match update {
                Update::Flaw(f, old_cost) => self.h_flaw[*f] = old_cost,
                Update::Resolver(r, old_cost) => self.h_resolver[*r] = old_cost,
            }
        }
        self.trail_lim.truncate(level);
    }

    pub(super) fn propagate(&mut self, initial_flaw_id: FlawId) {
        let mut queue = VecDeque::new();
        queue.push_back(initial_flaw_id);

        let mut in_queue = vec![false; self.flaws.len()];
        in_queue[*initial_flaw_id] = true;

        while let Some(f_id) = queue.pop_front() {
            in_queue[*f_id] = false;

            let old_cost = self.h_flaw[*f_id];
            let c_cost = self.compute_flaw_cost(f_id);

            if c_cost < old_cost {
                self.trail.push(Update::Flaw(f_id, old_cost));
                self.h_flaw[*f_id] = c_cost;

                for &r_id in self.flaws[*f_id].required_by().iter() {
                    let parent_flaw_id = self.resolvers[*r_id].flaw();
                    let r_old_cost = self.h_resolver[*r_id];
                    let r_new_cost = self.compute_resolver_cost(r_id);

                    if r_new_cost < r_old_cost {
                        self.trail.push(Update::Resolver(r_id, r_old_cost));
                        self.h_resolver[*r_id] = r_new_cost;

                        if !in_queue[*parent_flaw_id] {
                            queue.push_back(parent_flaw_id);
                            in_queue[*parent_flaw_id] = true;
                        }
                    }
                }
            }
        }
    }

    fn compute_flaw_cost(&self, flaw_id: FlawId) -> f64 {
        let flaw = &self.flaws[*flaw_id];
        let mut min_cost = f64::INFINITY;

        for &resolver_id in flaw.resolvers().iter() {
            let resolver_cost = self.h_resolver[*resolver_id];
            if resolver_cost < min_cost {
                min_cost = resolver_cost;
            }
        }

        min_cost
    }

    fn compute_resolver_cost(&self, resolver_id: ResolverId) -> f64 {
        let resolver = &self.resolvers[*resolver_id];
        let intrinsic_cost = match resolver.intrinsic_cost().rational_part() {
            Rational::Finite(cost) => cost.to_f64(),
            _ => unreachable!("Resolver intrinsic cost is infinite, which should not happen."),
        };

        #[cfg(feature = "h_add")]
        let precondition_cost: f64 = resolver.preconditions().iter().map(|&f_id| self.h_flaw[*f_id]).sum();
        #[cfg(feature = "h_max")]
        let precondition_cost: f64 = resolver.preconditions().iter().fold(0.0_f64, |acc, &f_id| acc.max(self.h_flaw[*f_id]));

        intrinsic_cost + precondition_cost
    }
}
