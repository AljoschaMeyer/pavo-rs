//! The values manipulated at runtime.
use std::ops::Deref;

use gc::Gc;
use gc_derive::{Trace, Finalize};

use crate::{
    context::{Computation, Context, PavoResult},
    gc_foreign::Vector,
    util::FnWrap as W,
    ir::Closure,
};

// Runtime representation of an arbitrary pavo value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    Fun(Fun),
    Array(Vector<Value>),
}

impl Value {
    pub fn new_nil() -> Value {
        Value::Nil
    }

    pub fn new_bool(b: bool) -> Value {
        Value::Bool(b)
    }

    pub fn new_int_usize(n: usize) -> Value {
        Value::new_int(n as i64)
    }

    pub fn new_int(n: i64) -> Value {
        Value::Int(n)
    }

    pub fn new_array(arr: Vector<Value>) -> Value {
        Value::Array(arr)
    }

    pub fn new_builtin2(fun: W<fn(&Value, &Value, &mut Context) -> PavoResult>) -> Value {
        Value::Fun(Fun::Builtin2(fun))
    }

    pub fn new_builtin_many(fun: W<fn(&[Value], &mut Context) -> PavoResult>) -> Value {
        Value::Fun(Fun::BuiltinMany(fun))
    }

    pub fn new_closure(c: Gc<Closure>) -> Value {
        Value::Fun(Fun::Closure(c))
    }

    pub fn truthy(&self) -> bool {
        match self {
            Value::Nil | Value::Bool(false) => false,
            _ => true,
        }
    }
}

impl Default for Value {
    fn default() -> Self {
        Self::new_nil()
    }
}

#[derive(Debug, Clone, Eq, PartialOrd, Ord, Trace, Finalize)]
pub enum Fun {
    Builtin2(#[unsafe_ignore_trace] W<fn(&Value, &Value, &mut Context) -> PavoResult>),
    BuiltinMany(#[unsafe_ignore_trace] W<fn(&[Value], &mut Context) -> PavoResult>),
    Closure(Gc<Closure>), // TODO manually impl PartialEq to go for GcEquality only
}

impl PartialEq for Fun {
    // Compare closures by pointer equality
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Fun::Builtin2(a), Fun::Builtin2(b)) => a == b,
            (Fun::BuiltinMany(a), Fun::BuiltinMany(b)) => a == b,
            (Fun::Closure(a), Fun::Closure(b)) => std::ptr::eq(a.deref(), b.deref()),
            (Fun::Builtin2(..), _) => false,
            (Fun::BuiltinMany(..), _) => false,
            (Fun::Closure(..), _) => false,
        }
    }
}

impl Computation for Value {
    fn compute(&self, args: &[Value], cx: &mut Context) -> PavoResult {
        match self {
            Value::Fun(ref fun) => match fun {
                Fun::Builtin2(W(fun)) => {
                    fun(
                        args.get(0).unwrap_or(&Value::new_nil()),
                        args.get(1).unwrap_or(&Value::new_nil()),
                        cx
                    )
                }
                Fun::BuiltinMany(W(fun)) => {
                    fun(args, cx)
                }
                Fun::Closure(c) => c.compute(args, cx)
            }

            _ => Err(Value::new_nil()), // TODO type error
        }
    }
}
