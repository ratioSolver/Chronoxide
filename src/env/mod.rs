use std::rc::Rc;

use crate::env::objects::Object;

pub mod classes;
pub mod method;
pub mod objects;

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
