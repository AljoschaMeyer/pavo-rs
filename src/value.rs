//! The values manipulated at runtime.

use gc_derive::{Trace, Finalize};

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
}

/// The default value is `nil`.
impl Default for Value {
    /// Return a value representing `nil`.
    fn default() -> Self {
        Value(_Value::default())
    }
}
