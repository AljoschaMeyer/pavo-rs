//! The values manipulated at runtime.

use gc_derive::{Trace, Finalize};

use crate::context::{Computation, Context, PavoResult};

// Runtime representation of an arbitrary pavo value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
enum _Value {
    Nil,
    Bool(bool),
    Fun(Fun),
}

impl _Value {
    fn new_nil() -> _Value {
        _Value::Nil
    }

    fn new_bool(b: bool) -> _Value {
        _Value::Bool(b)
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

    pub fn truthy(&self) -> bool {
        self.0.truthy()
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
    #[unsafe_ignore_trace]
    Builtin2(fn(Value, Value) -> PavoResult),
}

impl Computation for Value {
    fn compute(&self, args: &[Value], _: &mut Context) -> PavoResult {
        match self.0 {
            // _Value::Fun(Fun::Builtin2(the_fun)) => {
            //     let mut iter = args.into_iter().chain(std::iter::repeat(Value::new_nil())).take(2);
            //     return the_fun(iter.next().unwrap(), iter.next().unwrap());
            // }
            _ => Err(Value::new_nil()), // TODO type error
        }
    }
}
