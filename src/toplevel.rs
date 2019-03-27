//! The toplevel environment of values bound to names.

use gc::{Gc, GcCell};

use crate::{
    value::Value,
    builtins,
    binding_analysis::DeBruijn,
    ir::Environment,
    util::FnWrap as W,
};

pub static BINDINGS: &[&str] = &["eq"];

fn add(env: &Gc<GcCell<Environment>>, val: Value, at: usize) {
    env.borrow_mut().set(DeBruijn { up: 0, id: at}, val);
}

pub fn top_level() -> Gc<GcCell<Environment>> {
    let env = Environment::root();

    add(&env, Value::new_builtin2(W(builtins::eq)), 0);

    env
}
