# Pavo Tutorial

A series of post building up both the pavo language and this particular implementation from zero. Originally posted to ssb, beginning with message %4YgCw65KkFlRmryWPusvgWGHY69AEFN4AqXkwVSPV24=.sha256

---

## Introduction

Pavo is a dynamically typed programming language. Variables bindings don't have statically known types, instead all values carry their type with them at runtime. The initial, tiny subset of pavo we start with only has a single type: `nil`. There's only a single expression, the `nil` literal. Here are a few pavo programs:

```pavo
// This is a line comment.
nil
```

```pavo
// Expressions can be wrapped in parentheses without changing their meaning.
(nil)
```

```pavo
// A pavo program is a sequence of statements. The only current type of statements are expressions.
nil;
((nil));
nil
```

All of these programs evaluate to - you guessed it - `nil`. In the next post, I'll describe the architecture of our initial pavo interpreter.

---

## Overall Architecture

[current code base](https://github.com/AljoschaMeyer/pavo-rs/tree/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc)

So, we want to run these `nil` programs and obtain `nil` as a result. But we want to architect this interpreter in a way that we can then extend with all the upcoming features of the language. To this end, we split the code into six major parts:

```rust
// The types that make up the pavo syntax trees.
mod syntax;
// A parser to turn well-formed source code into a syntax tree.
mod parse;
// Definition of the pavo runtime values.
mod value;
// The context in which a pavo computation is evaluated.
mod context;
// An intermediate representation used during compilation from syntax trees into executable vm code.
mod ir;
// A virtual machine executing the instructions into which this implementation compiles pavo code.
mod vm;
```

AST nodes are defined as rust enums [here](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/syntax.rs) and include source code locations. For parsing, we are hand-writing a [recursive descent parser](https://en.wikipedia.org/wiki/Recursive_descent_parser) using the parser combinator crate [nom](https://crates.io/crates/nom) (version 4.x.x). The parser implementation is [here](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/parse.rs).

All runtime values are instances of the [`Value`](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/value.rs) enum:

```rust
// Runtime representation of an arbitrary pavo value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
enum _Value {
    Nil,
}
```

Notice the `#[derive(Trace, Finalize)]` attributes. Those are from the [gc](https://crates.io/crates/gc) crate (version 0.3.x) which provides garbage collection. `nil`s are not heap-allocated, so we don't have to deal with garbage collection yet. But the crate will make this very easy, it provides a `Gc<T>` smart pointer similar to `Arc<T>` that handles garbage collection for us. It can only accept types that implement the `Trace` and `Finalize` traits we just derived. `Trace` keeps track of the roots in the [tracing garbage collection](https://en.wikipedia.org/wiki/Tracing_garbage_collection) the pointer employs, and `Finalize` is a gc-specific destructor similar to `Drop`.

The generic description of how values are turned into other values (i.e. what makes up a pavo computation) is given in [context.rs](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/context.rs). The module doesn't *do* anything yet, it just provides important definitions:

```rust
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

/// A trait for values that represent a pavo computation.
pub trait Computation {
    /// Perform the computation (i.e. run some pavo code).
    ///
    /// `self` is the static representation of the computation that is executed.
    /// `args` are the input values to the computation.
    /// `cx` is the `Context` in which the computation happens.
    fn compute<Args: IntoIterator<Item = Value>>(&self, _: Args, cx: &mut Context) -> PavoResult;
}
```

The pavo interpreter works by parsing some code into a syntax tree and then compiling it into a sequence of instructions for a virtual machine, defined [in this file](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/vm.rs). In this initial subset of pavo, the state of the vm consists of the [vm code](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/vm.rs#L16), an array of [`registers`](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/vm.rs#L37) where `Value`s can be temporarily stored, and a [program counter](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/vm.rs#L35) (`pc`) indicating which instruction to run next. All the vm then needs to do is to [read and execute instructions in a loop](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/vm.rs#L106).

Here's our initial instruction set:

```rust
// A single instruction of vm code.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Instruction {
    // Write the given literal `Value` to the address.
    Literal(Value, Addr),
    // Return the value at the address.
    Return(Addr),
}
```

An `Addr` at this point just points to a register:

```rust

/// Addresses a storage slot where a computation can write `Value`s to (or from where to read them).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Addr {
    /// Address of a register in a `LocalState`.
    Register(usize),
}
```

Later, addresses will be able to refer to variables stored on the heap (in the environment of a closure).

That's pretty much it. Since the vm operates on pavo `Value`s directly, it is (and will stay) fairly simple. The more interesting part is compiling from pavo source ASTs into vm instructions. To help with this, there's the [intermediate representation](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/ir.rs) (*ir*).

The ir represents programs as [basic blocks](https://en.wikipedia.org/wiki/Basic_block) of statements. The [statements themselves](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/ir.rs#L44) are very similar to the instructions of the virtual machine. The main difference is that the vm stores instructions as a sequence, whereas the ir [stores](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/ir.rs#L16) them as a [control flow graph](https://en.wikipedia.org/wiki/Control-flow_graph). Compiling [ir into vm code](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/ir.rs#L71) is mostly about flattening the instructions into a vector. This isn't implemented yet, we'll wait with that until we added actual control flow to the language. The translation from [ast into ir](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/ir.rs#L52) is slightly more interesting, but not at the moment. Right now, it just converts sequences of expressions into sequences of `Literal` instructions.

Putting it all together: To run a pavo program, we

- [parse](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/parse.rs#L94) the source code into an [AST](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/syntax.rs)
- we [transform](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/ir.rs#L52) the AST into an intermediate representation of [basic blocks](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/ir.rs#L17)
- we [transform](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/ir.rs#L71) the ir into [vm code](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/vm.rs#L14)
- we [interpret](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/vm.rs#L103) the code

Or in [code](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/lib.rs#L19):

```rust
pub fn execute_pavo<'s>(src: &'s str) -> Result<PavoResult, Err<LocatedSpan<CompleteStr<'s>>>> {
    parse::script(LocatedSpan::new(CompleteStr(src)))
        .map(|(_, ast)| {
            let mut cx = Context::new();
            let ir_chunk = ir::ast_to_ir(&ast);
            let vm_chunk = ir::ir_to_vm(ir_chunk);
            return vm_chunk.compute(vec![], &mut cx);
        })
}

assert_eq!(execute_pavo("nil").unwrap(), Ok(Value::new_nil())); // It works!
```

That was quite a lot of effort for language whose only value is `nil`. But we should be able to keep extending this architecture until we have a fully-featured programming language. In the next post, we'll tackle basic control flow expressions.

---

## Control Flow

We'll add control flow via (mostly) conventional `if`/`else` expression. But for those, we first need to implement boolean values.
