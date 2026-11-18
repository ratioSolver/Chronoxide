use crate::{SolverError, SolverState};
use serde_json::Value;
use std::{
    fmt,
    ops::{Index, IndexMut},
};

pub(super) mod bool_flaw;
pub(super) mod clause_flaw;
pub(super) mod disjunction_flaw;
pub(super) mod enum_flaw;
