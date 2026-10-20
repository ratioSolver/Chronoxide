use crate::{SolverState, bool_expr, graph::Graph};
use riddle::{
    core::Core,
    env::{Env, ObjectId, Slot, Var},
    scope::{Type, common_type},
};
use semitone::{
    SeMiTONE,
    ast::{ArithExpr, BoolExpr, EnumExpr},
};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

pub struct BoolVar {
    var_type: Weak<dyn Type>,
    pub(crate) lit: BoolExpr,
}

impl BoolVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, lit: BoolExpr) -> Self {
        Self { var_type: Rc::downgrade(&var_type), lit }
    }
}

impl Var for BoolVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped")
    }
}

pub struct ArithVar {
    var_type: Weak<dyn Type>,
    pub(crate) lin: ArithExpr,
}

impl ArithVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, lin: ArithExpr) -> Self {
        Self { var_type: Rc::downgrade(&var_type), lin }
    }
}

impl Var for ArithVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped")
    }
}

pub struct StringVar {
    var_type: Weak<dyn Type>,
    pub(crate) value: String,
}

impl StringVar {
    pub(crate) fn new(var_type: Rc<dyn Type>, value: String) -> Self {
        Self { var_type: Rc::downgrade(&var_type), value }
    }
}

impl Var for StringVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped")
    }
}

pub struct EnumVar {
    slv: Weak<SolverState>,
    var_type: Weak<dyn Type>,
    variables: RefCell<HashMap<String, Slot>>,
    pub(crate) var: EnumExpr,
}

impl EnumVar {
    pub(crate) fn new(slv: Weak<SolverState>, var_type: Rc<dyn Type>, var: EnumExpr) -> Self {
        Self { slv, var_type: Rc::downgrade(&var_type), variables: RefCell::new(HashMap::new()), var }
    }

    fn link<E>(&self, slv: &SolverState, smt: &mut SeMiTONE, graph: &mut Graph, inst_slots: &[(ObjectId, Slot)], extract: impl Fn(&Slot) -> Option<E>, eq: impl Fn(&E) -> BoolExpr) -> Option<()> {
        for (inst, slot) in inst_slots {
            let value = extract(slot)?;
            let selected = slv.track_expr(smt, graph, self.var.eq(**inst as i32)).ok()?;
            let same = slv.track_expr(smt, graph, eq(&value)).ok()?;
            slv.add_clause(smt, graph, vec![!selected, same]).ok()?;
        }
        Some(())
    }
}

impl Var for EnumVar {
    fn var_type(&self) -> Rc<dyn Type> {
        self.var_type.upgrade().expect("Type has been dropped")
    }

    fn into_env(self: Rc<Self>) -> Option<Rc<dyn Env>> {
        Some(self)
    }
}

impl Env for EnumVar {
    fn parent(&self) -> Option<Rc<dyn Env>> {
        None
    }

    fn get_slots(&self) -> HashMap<String, Slot> {
        self.variables.borrow().clone()
    }

    fn get(&self, name: &str) -> Option<Slot> {
        let cached = self.variables.borrow().get(name).cloned();
        if cached.is_some() {
            return cached;
        }

        let slv = self.slv.upgrade()?;
        let c_class = self.var_type.upgrade()?.as_class()?;

        let mut inst_slots = Vec::new();
        let mut slot_types = Vec::new();
        for inst in c_class.instances() {
            let slot = slv.get_object(inst)?.get(name)?;
            let slot_tp = match &slot {
                Slot::Primitive(p) => p.var_type(),
                Slot::ObjectRef(id) => slv.get_object(*id)?.var_type(),
                Slot::AtomRef(_) => return None,
            };
            inst_slots.push((inst, slot));
            slot_types.push(slot_tp);
        }

        let (_, first_slot) = inst_slots.first()?;
        if inst_slots.iter().all(|(_, s)| first_slot == s) {
            let slot = first_slot.clone();
            self.variables.borrow_mut().insert(name.to_string(), slot.clone());
            return Some(slot);
        }

        let tp = common_type(&slot_types)?;

        let mut smt = slv.smt.borrow_mut();
        let mut graph = slv.graph.borrow_mut();

        let slot = match tp.name() {
            "bool" => {
                let r = smt.new_bool();
                self.link(
                    &slv,
                    &mut smt,
                    &mut graph,
                    &inst_slots,
                    |s| match s {
                        Slot::Primitive(p) => bool_expr(p),
                        _ => None,
                    },
                    |b| r.eq(b),
                )?;
                Slot::Primitive(Rc::new(BoolVar::new(tp, r)))
            }
            "int" | "real" => {
                let r = if tp.name() == "int" { smt.new_int() } else { smt.new_real() };
                self.link(
                    &slv,
                    &mut smt,
                    &mut graph,
                    &inst_slots,
                    |s| match s {
                        Slot::Primitive(p) => p.downcast::<ArithVar>().map(|v| v.lin.clone()),
                        _ => None,
                    },
                    |a| r.eq(a),
                )?;
                Slot::Primitive(Rc::new(ArithVar::new(tp, r)))
            }
            "string" => return None,
            _ => {
                let tp_class = tp.as_class()?;
                let domain = tp_class.instances().iter().map(|id| **id as i32).collect::<Vec<_>>();
                if domain.is_empty() {
                    return None;
                }
                let r = smt.new_enum(domain);
                let value = |s: &Slot| match s {
                    Slot::ObjectRef(id) => Some(EnumExpr::Const(**id as i32)),
                    Slot::Primitive(p) => p.downcast::<EnumVar>().map(|v| v.var.clone()),
                    Slot::AtomRef(_) => None,
                };
                self.link(&slv, &mut smt, &mut graph, &inst_slots, value, |e| r.eq(e))?;
                Slot::Primitive(Rc::new(EnumVar::new(self.slv.clone(), tp_class, r)))
            }
        };

        self.variables.borrow_mut().insert(name.to_string(), slot.clone());
        Some(slot)
    }

    fn set(&self, name: String, value: Slot) {
        self.variables.borrow_mut().insert(name, value);
    }
}
