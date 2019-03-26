// Shared state across the evaluation of a pavo computation.

use crate::value::Value;

/// Debug information attached to thrown values.
///
/// This is not accessible to the pavo program at all (it's not part of the language semantics), but
/// it can be presented to the programmer.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DbgTrace;

/// The outcome of a pavo computation: Either the computation succesfully produces a `Value` (`Ok`),
/// or it throws one (`Err`). In the latter case, a trace of debug information is attached, to be
/// presented to the programmer.
pub type PavoResult = Result<Value, (Value, DbgTrace)>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
/// Global state that can be accessed and mutated over the course of a pavo computation.
pub struct Context;

impl Context {
    pub fn new() -> Context {
        Context
    }
}

/// A trait for values that represent a pavo computation.
pub trait Computation {
    /// Perform the computation (i.e. run some pavo code).
    ///
    /// `self` is the static representation of the computation that is executed.
    /// `args` are the input values to the computation.
    /// `cx` is the `Context` in which the computation happens.
    fn compute(&self, args: &[Value], cx: &mut Context) -> PavoResult;
}
