use crate::{
    ToJson,
    flaws::{Flaw, FlawData, FlawId, Resolver, ResolverData, ResolverId},
    objects::EnumVar,
    solver::SolverError,
    solver_state::SolverState,
};
use linarith::Rational;
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};
use watchsat::{VarId, neg};

pub(crate) struct EnumFlaw {
    flw: FlawData,
    var: Rc<EnumVar>,
    rhos: RefCell<HashMap<i32, VarId>>,
}

impl EnumFlaw {
    pub(crate) fn new(slv: Weak<SolverState>, id: FlawId, phi: VarId, cause: Option<ResolverId>, var: Rc<EnumVar>) -> Box<Self> {
        Box::new(Self {
            flw: FlawData::new(slv, id, phi, cause.into_iter().collect()),
            var,
            rhos: RefCell::new(HashMap::new()),
        })
    }
}

impl Flaw for EnumFlaw {
    fn solver(&self) -> Rc<SolverState> {
        self.flw.solver()
    }
    fn id(&self) -> FlawId {
        self.flw.id()
    }
    fn phi(&self) -> VarId {
        self.flw.phi()
    }
    fn causes(&self) -> Vec<ResolverId> {
        self.flw.causes()
    }
    fn supports(&self) -> Vec<ResolverId> {
        self.flw.supports()
    }
    fn resolvers(&self) -> Vec<ResolverId> {
        self.flw.resolvers()
    }
    fn is_expanded(&self) -> bool {
        self.flw.is_expanded()
    }

    fn compute_resolvers(&mut self) {
        let solver = self.solver();
        let vals = solver.ac.borrow().val(self.var.var);
        let num_vals = vals.len();
        for val in vals {
            let res_id = ResolverId(self.solver().get_resolvers_len());
            let rho = solver.sat.borrow_mut().add_var();
            let res = EnumResolver::new(self.flw.slv.clone(), res_id, self.id(), rho, self.var.clone(), val, Rational::new(1, num_vals as i64));
            solver.add_resolver(self, res);
        }
        let c_solver = self.solver().clone();
        solver.ac.borrow_mut().set_listener(self.var.var, {
            let rhos = self.rhos.clone();
            move |_var, c_vals| {
                for (val, rho) in rhos.borrow().iter() {
                    if !c_vals.contains(val) {
                        c_solver.enqueue(neg(*rho));
                    }
                }
            }
        });

        self.flw.set_expanded();
    }

    fn add_resolver(&mut self, resolver_id: ResolverId) {
        self.flw.add_resolver(resolver_id);
    }

    fn cost(&self) -> Rational {
        self.flw.cost()
    }
    fn set_cost(&mut self, cost: Rational) {
        self.flw.set_cost(cost);
    }
}

impl ToJson for EnumFlaw {
    fn to_json(&self) -> Value {
        json!({
            "kind": "enum",
            "var": format!("{:?}", self.var.var),
        })
    }
}

struct EnumResolver {
    res: ResolverData,
    var: Rc<EnumVar>,
    val: i32,
    ac_constraints: RefCell<Vec<ac3rm::ConstraintId>>,
}

impl EnumResolver {
    fn new(slv: Weak<SolverState>, id: ResolverId, flaw: FlawId, rho: VarId, var: Rc<EnumVar>, val: i32, intrinsic_cost: Rational) -> Box<Self> {
        Box::new(Self {
            res: ResolverData::new(slv, id, flaw, rho, intrinsic_cost),
            var,
            val,
            ac_constraints: RefCell::new(vec![]),
        })
    }
}

impl Resolver for EnumResolver {
    fn solver(&self) -> Rc<SolverState> {
        self.res.solver()
    }
    fn id(&self) -> ResolverId {
        self.res.id()
    }
    fn flaw(&self) -> FlawId {
        self.res.flaw()
    }
    fn rho(&self) -> VarId {
        self.res.rho()
    }
    fn intrinsic_cost(&self) -> Rational {
        self.res.intrinsic_cost()
    }

    fn apply(&self) -> Result<(), SolverError> {
        self.ac_constraints.borrow_mut().push(self.solver().ac.borrow_mut().new_constraint(ac3rm::Constraint::Set(self.var.var, self.val)));
        Ok(())
    }
    fn requirements(&self) -> Vec<FlawId> {
        self.res.requirements()
    }

    fn ac_constraints(&self) -> Option<Vec<ac3rm::ConstraintId>> {
        Some(self.ac_constraints.borrow().clone())
    }
}

impl ToJson for EnumResolver {
    fn to_json(&self) -> Value {
        json!({
            "val": self.val,
        })
    }
}
