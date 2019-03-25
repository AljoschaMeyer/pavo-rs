//! The values manipulated at runtime.

use gc_derive::{Trace, Finalize};

use crate::context::{Computation, Context, PavoResult, DbgTrace};

// Runtime representation of an arbitrary pavo value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
enum _Value {
    Nil,
    Bool(bool),
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

impl Computation for Value {
    fn compute<Args: IntoIterator<Item = Value>>(&self, _: Args, _: &mut Context) -> PavoResult {
        match self.0 {
            _ => Err((Value::new_nil(), DbgTrace))
        }
    }
}
