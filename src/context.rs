// Shared state across the evaluation of a pavo computation.

use crate::gc_foreign::Vector;
use crate::value::Value;
use crate::builtins::as_arr;

/// The outcome of a pavo computation: Either the computation succesfully produces a `Value` (`Ok`),
/// or it throws one (`Err`).
pub type PavoResult = Result<Value, Value>;

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
    fn compute(&self, args: &[Value], cx: &mut Context) -> PavoResult {
        self.compute_vector(Vector(args.into()), cx)
    }

    fn compute_vector(&self, args: Vector<Value>, cx: &mut Context) -> PavoResult {
        self.compute(&args.0.iter().map(Clone::clone).collect::<Vec<Value>>()[..], cx)
    }

    fn compute_value(&self, args: &Value, cx: &mut Context) -> PavoResult {
        self.compute_vector(as_arr(args)?, cx)
    }
}

impl Computation for fn(&mut Context) -> PavoResult {
    fn compute(&self, _: &[Value], cx: &mut Context) -> PavoResult {
        self(cx)
    }
}

impl Computation for fn(&Value, &mut Context) -> PavoResult {
    fn compute(&self, args: &[Value], cx: &mut Context) -> PavoResult {
        self(args.get(0).unwrap_or(&Value::new_nil()), cx)
    }
}

impl Computation for fn(&Value, &Value, &mut Context) -> PavoResult {
    fn compute(&self, args: &[Value], cx: &mut Context) -> PavoResult {
        self(
            args.get(0).unwrap_or(&Value::new_nil()),
            args.get(1).unwrap_or(&Value::new_nil()),
            cx
        )
    }
}

impl Computation for fn(&Value, &Value, &Value, &mut Context) -> PavoResult {
    fn compute(&self, args: &[Value], cx: &mut Context) -> PavoResult {
        self(
            args.get(0).unwrap_or(&Value::new_nil()),
            args.get(1).unwrap_or(&Value::new_nil()),
            args.get(2).unwrap_or(&Value::new_nil()),
            cx
        )
    }
}
