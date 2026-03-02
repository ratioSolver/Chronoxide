use crate::{
    RiddleError, Solver,
    env::{classes::Class, objects::Object},
};
use linspire::rational::rat;
use riddle::language::{Expr, Field, MethodDef, PredicateDef, Statement};
use std::rc::Rc;

pub mod classes;
pub mod objects;

pub trait Scope {
    fn solver(&self) -> Rc<Solver>;
    fn parent(&self) -> Option<Rc<dyn Scope>>;

    fn get_field(&self, name: &str) -> Option<Field>;
    fn get_method(&self, name: &str) -> Option<MethodDef>;
    fn get_class(&self, name: &str) -> Option<Rc<dyn Class>>;
    fn get_predicate(&self, name: &str) -> Option<PredicateDef>;
}

pub trait Env {
    fn parent(&self) -> Option<Rc<dyn Env>>;
    fn get(&self, name: &str) -> Option<Rc<dyn Object>>;
}

pub trait EnvExt {
    fn get_as<T: Object + 'static>(&self, name: &str) -> Option<Rc<T>>;
}

impl<E: Env + ?Sized> EnvExt for E {
    fn get_as<T: Object + 'static>(&self, name: &str) -> Option<Rc<T>> {
        self.get(name)?.as_any().downcast::<T>().ok()
    }
}

pub fn execute(scp: Rc<dyn Scope>, env: Rc<dyn Env>, stmt: &Statement) -> Result<(), RiddleError> {
    match stmt {
        _ => unimplemented!(),
    }
}

pub fn evaluate(scp: Rc<dyn Scope>, env: Rc<dyn Env>, expr: &Expr) -> Result<Rc<dyn Object>, RiddleError> {
    match expr {
        Expr::Bool(bool) => Ok(scp.solver().new_bool_const(*bool)),
        Expr::Int(int) => Ok(scp.solver().new_int_const(*int)),
        Expr::Real(num, den) => Ok(scp.solver().new_real_const(rat(*num, *den))),
        Expr::String(string) => Ok(scp.solver().new_string(string)),
        Expr::QualifiedId { ids } => {
            let env = env.get(ids[0].as_str()).ok_or_else(|| RiddleError::TypeError(format!("Identifier '{}' not found", ids[0])))?;
            for id in &ids[1..] {
                env = env.as_any().downcast_ref::<dyn Env>().ok_or_else(|| RiddleError::TypeError(format!("Identifier '{}' is not an environment", id)))?.get(id.as_str()).ok_or_else(|| RiddleError::TypeError(format!("Identifier '{}' not found in '{}'", id, ids[..ids.len() - 1].join("."))))?;
            }
            Ok(obj.new_instance())
        }
        _ => unimplemented!(),
    }
}
