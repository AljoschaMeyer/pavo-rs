//! The values manipulated at runtime.

use gc_derive::{Trace, Finalize};

use crate::{
    context::{Computation, Context, PavoResult},
    gc_foreign::Vector,
    util::FnWrap as W,
};

// Runtime representation of an arbitrary pavo value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
enum _Value {
    Nil,
    Bool(bool),
    Fun(Fun),
    Array(Vector<Value>),
}

impl _Value {
    fn new_nil() -> _Value {
        _Value::Nil
    }

    fn new_bool(b: bool) -> _Value {
        _Value::Bool(b)
    }

    fn new_array(arr: Vector<Value>) -> _Value {
        _Value::Array(arr)
    }

    pub fn new_builtin2(fun: W<fn(&Value, &Value, &mut Context) -> PavoResult>) -> _Value {
        _Value::Fun(Fun::Builtin2(fun))
    }

    pub fn new_builtin_many(fun: W<fn(&[Value], &mut Context) -> PavoResult>) -> _Value {
        _Value::Fun(Fun::BuiltinMany(fun))
    }

    fn truthy(&self) -> bool {
        match self {
            _Value::Nil | _Value::Bool(false) => false,
            _ => true,
        }
    }
}

impl Default for _Value {
    fn default() -> Self {
        Self::new_nil()
    }
}

/// Opaque runtime representation of an arbitrary pavo value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
pub struct Value(_Value);

impl Value {
    pub fn new_nil() -> Value {
        Value(_Value::new_nil())
    }

    pub fn new_bool(b: bool) -> Value {
        Value(_Value::new_bool(b))
    }

    pub fn new_array(arr: Vector<Value>) -> Value {
        Value(_Value::new_array(arr))
    }

    pub fn new_builtin2(fun: W<fn(&Value, &Value, &mut Context) -> PavoResult>) -> Value {
        Value(_Value::new_builtin2(fun))
    }

    pub fn new_builtin_many(fun: W<fn(&[Value], &mut Context) -> PavoResult>) -> Value {
        Value(_Value::new_builtin_many(fun))
    }

    pub fn truthy(&self) -> bool {
        self.0.truthy()
    }

    pub fn pavo_eq(&self, other: &Value) -> PavoResult {
        Ok(Value::new_bool(self == other))
    }
}

/// The default value is `nil`.
impl Default for Value {
    /// Return a value representing `nil`.
    fn default() -> Self {
        Value(_Value::default())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
enum Fun {
    Builtin2(#[unsafe_ignore_trace] W<fn(&Value, &Value, &mut Context) -> PavoResult>),
    BuiltinMany(#[unsafe_ignore_trace] W<fn(&[Value], &mut Context) -> PavoResult>),
}

impl Computation for Value {
    fn compute(&self, args: &[Value], cx: &mut Context) -> PavoResult {
        match self.0 {
            _Value::Fun(ref fun) => match fun {
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
            }

            _ => Err(Value::new_nil()), // TODO type error
        }
    }
}
