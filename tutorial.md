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
// An intermediate representation of pavo code that gets interpreted.
mod ir;
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

The pavo interpreter works by parsing some code into a syntax tree and then compiling it into a sequence of intermediate representation instructions. In this initial subset of pavo, the state of the interpreter consists of the [ir instructions], an array of `registers` where `Value`s can be temporarily stored, and a program counter (`pc`) indicating which instruction to run next. All the interpreter then needs to do is to read and execute instructions in a loop.

Here's our initial instruction set:

```rust
/// A single instruction of the ir.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Instruction {
    /// Do nothing but evaluate to the given value and store it in the given location.
    Literal(Value, Addr),
    /// Jump to the given basic block. If the usize is `BB_RETURN`, return from the function instead.
    Jump(usize),
    /// Jump to the first basic block if the value at the Addr is truthy, else to the second one.
    CondJump(Addr, usize, usize),
}

// If this is given as an unconditional jump address, return from the function instead.
const BB_RETURN: usize = std::usize::MAX;
```

An `Addr` at this point just points to a register:

```rust
// Addresses a storage slot where a computation can write `Value`s to (or from where to read them).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Addr {
    // Address of a register in a `LocalState`.
    //
    // Register 0 is used for passing data from one statement to the next.
    // Additional registers are used when multiple values need to be kept in memory simutaneously,
    // e.g. all the arguments that are passed to a function call.
    Register(usize),
}
```

Later, addresses will be able to refer to variables stored on the heap (in the environment of a closure).

When executing code, there is some `LocalState` involved:

```rust
// The local state upon which the instructions to operate. It is local to each invocation of
// `Computation::compute`.
struct LocalState {
    // Index into the graph of instructions that indicates which instruction to execute next.
    // "pc" stands for "program counter".
    //
    // First usize is the basic block, second one the offset in the basic block.
    pc: (usize, usize),
    // Temporary storage slots for `Value`s.
    registers: Box<[Value]>,
}
```

The interpreter runs instructions in a loop, continuously incrementing the program counter.

```rust
fn compute<Args: IntoIterator<Item = Value>>(&self, _: Args, _: &mut Context) -> PavoResult {
    let mut state = LocalState::new(self);

    loop {
        state.pc.1 += 1;
        match &self.basic_blocks[state.pc.0][state.pc.1 - 1] {
            Literal(val, dst) => dst.store(val.clone(), &mut state),

            Jump(block) => {
                if *block == BB_RETURN {
                    // register 0 holds the evaluation result of the previously executed statement
                    return Ok(Addr::reg(0).load(&state));
                } else {
                    state.pc = (*block, 0);
                }
            }

            CondJump(cond, then_block, else_block) => {
                if cond.load(&state).truthy() {
                    state.pc = (*then_block, 0);
                } else {
                    state.pc = (*else_block, 0);
                }
            }
        }
    }
}
```

That's pretty much it. Since the interpreter operates on pavo `Value`s directly, it is (and will stay) fairly simple.

Putting it all together: To run a pavo program, we

- [parse](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/parse.rs#L94) the source code into an [AST](https://github.com/AljoschaMeyer/pavo-rs/blob/1c53f9db61bc9fc2b775a8263e3aaaa3467fb4fc/src/syntax.rs)
- we transform the AST into an intermediate representation of basic blocks
- we interpret the ir instructions

Or in code:

```rust
pub fn execute_pavo<'s>(src: &'s str) -> Result<PavoResult, Err<LocatedSpan<CompleteStr<'s>>>> {
    parse::script(LocatedSpan::new(CompleteStr(src)))
        .map(|(_, ast)| {
            let mut cx = Context::new();
            let ir_chunk = ir::ast_to_ir(&ast);
            return ir_chunk.compute(vec![], &mut cx);
        })
}

assert_eq!(execute_pavo("nil").unwrap(), Ok(Value::new_nil())); // It works!
```

That was quite a lot of effort for language whose only value is `nil`. But we should be able to keep extending this architecture until we have a fully-featured programming language. In the next post, we'll tackle basic control flow expressions.

---

## Control Flow

We'll add control flow via (mostly) conventional `if`/`else` statements. For those to make sense, we first implement boolean values.

```rust
enum _Value {
    Nil,
    Bool(bool),
}
```

The literals for bools are `true` and `false`, these also denote the two values of type `bool`.

An if-expression consists of the keyword `if`, followed by a *condition* (an expression), followed by a sequence of statements delimited by curly braces, optionally followed by the keyword `else` and another block of brace-delimited statements. The `else` keyword may also be followed by a *blocky expression* instead (without the need for curly braces). The only *blocky expressions* at this point are if-expressions. An `if` expression without an `else` clause is treated as if it had an `else` clause of zero statements.

Execution of an if-expression begins by evaluating the *condition*. If it is *truthy* (neither `nil` nor `false`), then evaluate the following block. The if-expression evaluates to the same value as the last statement of the block. If the condition is not truthy, then evaluate the else-block instead. The if-expression evaluates to the same value as the last statement of the block (or to the value of the blocky expression). Empty blocks evaluate to `nil`.

In general, any semicolon-separated sequence of statements evaluates to the value to which the last of those statements evaluated, and the empty sequence of statements evaluates to `nil`.

```pavo
// evaluates to nil
if true {
  if false {}
} else if true {
  false
}
```

The instruction set already covers everything we need (jumps and conditional jumps), all that remains is compiling the pavo syntax into ir. To help with managing basic blocks, we define a helper struct, the `BBB` (BasicBlockBuilder):

```rust
// BasicBlockBuilder, a helper for constructing the graph of basic blocks.
//
// It provides a stateful api. There's the `current` block on which to work, and methods to modify
// it.
struct BBB {
    // All basic blocks generated so far.
    blocks: Vec<Vec<Instruction>>,
    // Index of the currently active block.
    current: usize,
}

impl BBB {
    fn new() -> BBB {
        BBB {
            blocks: vec![vec![]],
            current: 0,
        }
    }

    // Create a new, empty basic block, and return it's id.
    fn new_block(&mut self) -> usize {
        self.blocks.push(vec![]);
        return self.blocks.len() - 1;
    }

    // Set the block on which the BBB operates.
    fn set_active_block(&mut self, bb: usize) {
        self.current = bb;
    }

    // Append an instruction to the currently active block.
    fn append(&mut self, inst: Instruction) {
        self.blocks[self.current].push(inst);
    }

    // Consume the builder to create an IrChunk.
    fn into_ir(self) -> IrChunk {
        IrChunk {
            basic_blocks: self.blocks,
            num_registers: 1,
        }
    }
}
```

With this helper, the translation of code is fairly straightforward, though slightly verbose:

```rust
// Convert a sequence of statements into instructions and basic blocks, using the given BBB.
// As the last instruction, jump to the basic block `jump_to`.
fn block_to_ir(block: &Box<[Statement]>, jump_to: usize, bbb: &mut BBB) {
    for statement in block.iter() {
        statement_to_ir(statement, bbb);
    }

    if block.len() == 0 {
        bbb.append(Literal(Value::new_nil(), Addr::reg(0)));
    }

    bbb.append(Jump(jump_to));
}

// Convert a single statement into instructions and basic blocks, using the given BBB..
fn statement_to_ir(statement: &Statement, bbb: &mut BBB) {
    match statement.1 {
        _Statement::Expression(ref exp) => exp_to_ir(exp, bbb),
    }
}

// Convert a single expression into instructions and basic blocks, using the given BBB..
fn exp_to_ir(exp: &Expression, bbb: &mut BBB) {
    match exp.1 {
        _Expression::Nil => {
            bbb.append(Literal(Value::new_nil(), Addr::reg(0)));
        }
        _Expression::Bool(b) => {
            bbb.append(Literal(Value::new_bool(b), Addr::reg(0)));
        }
        _Expression::If(ref cond, ref then_block, ref else_block) => {
            exp_to_ir(cond, bbb);

            let bb_then = bbb.new_block();
            let bb_else = bbb.new_block();
            let bb_cont = bbb.new_block();

            bbb.append(CondJump(Addr::reg(0), bb_then, bb_else));

            bbb.set_active_block(bb_then);
            block_to_ir(then_block, bb_cont, bbb);

            bbb.set_active_block(bb_else);
            block_to_ir(else_block, bb_cont, bbb);

            bbb.set_active_block(bb_cont);
        }
    }
}
```

With all of this defined, translating an ast into ir only takes three lines of additional code:

```rust
let mut bbb = BBB::new();
block_to_ir(ast, BB_RETURN, &mut bbb);
return bbb.into_ir();
```

Wheew, that was quite a lot of code, but now we've got the very fundamentals of the interpreter done. Next, we'll add a few more control flow constructs to the language.

---

The next control flow constructs are fairly straightforward to add. The short-circuiting `&&` and `||` operators can be desugared into `if` expressions:

```rust
_Expression::Land(lhs, rhs) => {
    // `a && b` desugars to `if a { if b { true } else { false } } else { false }`
    let desugared = Expression::if_(
        lhs,
        vec![Statement::exp(Expression::if_(
            rhs,
            vec![Statement::exp(Expression::bool_(true))],
            vec![Statement::exp(Expression::bool_(false))]
        ))],
        vec![Statement::exp(Expression::bool_(false))],
    );
    exp_to_ir(desugared, bbb)
}

// `a || b` desugars to `if a { true } else if b { true } else { false }`
```

The more interesting part about these operators is that they introduce some parsing issues: We need to deal with left-recursion and with operator precedence (`&&` has higher precedence than `||`). To solve this, we refactor the grammar as explained [here](http://www.engr.mun.ca/~theo/Misc/exp_parsing.htm#classic), stealing the code to do so from [here](https://github.com/Geal/nom/issues/445#issuecomment-297421046):

```rust
// 100 is the precedence level
// `&&`
named!(exp_binop_100(Span) -> Expression, do_parse!(
    pos: position!() >>
    first: non_leftrecursive_exp >>
    fold: fold_many0!(
        do_parse!(
            land >>
            expr: non_leftrecursive_exp >>
            (expr)
        ),
        first,
        |acc, item| Expression(pos, _Expression::Land(Box::new(acc), Box::new(item)))
    ) >>
    (fold)
));
```

We add a `return` statement to the language. It can optionally return an expression (`return x`), which defaults to `nil`. Technically we haven't introduced functions yet, so this may seem odd. But in general, execution of a pavo script is equivalent to execution of a function of zero arguments with the script as the body (actually, it'll be an async function, but we are not there yet). Under this interpretation, `return` makes perfect sense in a top-level script. There's nothing interesting about the implementation whatsoever.

Next, we add `while` loops and the associated `break` statements. Syntactically, the loops are of the form `while cond_exp { stmt1; stmt2 }`. `while` loops are blocky expressions, they can be used as an `else` clause without delimiting curly braces. `break` works like `return` (including the optional expression to evaluate to), but jumps to the basic block after the loop rather than returning. A `break` statement that is not contained in a loop acts like a `return`.

We use the `BBB` helper to keep track of where to jump at a `break`. Before creating the code of the loop body, we save the old address (initialized to `BB_RETURN`) to the current stack frame and set the value on the `BBB` to the block where execution after the loop should resume. After the loop body has been generated, we reset the value to the saved one.

While loops need to juggle some registers around when evaluating the condition: The result of the previous loop iteration is stored in register 0, and we need to preserve it because we want to return that value after we checked the condition. To that end, we extend our instruction set with instructions to move around values:

```rust
enum Instruction {
    /* old instructios remain unchanged, new ones are below*/    
    /// Write the value at Addr `src` to the Addr `dst`.
    Write { src: Addr, dst: Addr },
    /// Swap the values in the given Addrs.
    Swap(Addr, Addr),
}
```

Interpreting these instructions is straightforward:

```rust
match &self.basic_blocks[state.pc.0][state.pc.1 - 1] {
    /* interpretation of old instructions remains unchanged, new ones are below */

    Write { src, dst } => dst.store(src.load(&mut state), &mut state),

    Swap(a, b) => {
        let val_a = a.load(&mut state);
        let val_b = b.load(&mut state);
        a.store(val_b, &mut state);
        b.store(val_a, &mut state);
    }
}

```

The full code generation for a `while` loop, using these new intructions:

```rust
_Expression::While(cond, loop_block) => {
    let bb_cond = bbb.new_block();
    let bb_loop = bbb.new_block();
    let bb_cont = bbb.new_block();

    // Pretend there was a previous loop iteration that evaluated to `nil`, so that we
    // evaluate to `nil` if the condition evaluates falsey at the first attempt.
    bbb.append(Literal(Value::new_nil(), Addr::reg(0)));
    // Evaluate the condition for the first time.
    bbb.append(Jump(bb_cond));

    // The block for evaluating the condition. It also ensures that we evaluate to the
    // correct value.
    bbb.set_active_block(bb_cond);
    // When entering here, register 0 holds the result of the previous loop body execution.
    // We save it to register 1 before evaluating the condition, and restore it afterwards.
    bbb.append(Write { src: Addr::reg(0), dst: Addr::reg(1)});
    exp_to_ir(*cond, bbb);
    bbb.append(Swap(Addr::reg(1), Addr::reg(0)));
    bbb.append(CondJump(Addr::reg(1), bb_loop, bb_cont));

    // The loop body, we save the old breakpoint and set the new one.
    let prev_breakpoint = bbb.breakpoint;
    bbb.breakpoint = bb_cont;
    bbb.set_active_block(bb_loop);
    block_to_ir(loop_block, bb_cond, bbb);

    bbb.set_active_block(bb_cont);
    bbb.breakpoint = prev_breakpoint;
}
```

And the corresponding code generation for `break` statements:

```rust
_Statement::Break(exp) => {
    exp_to_ir(exp, bbb);
    bbb.append(Jump(bbb.breakpoint));
}
```

That concludes the basic control flow constructs. The remaining ones (`case`, `loop` and `try`/`catch`/`finally`) are based on *patterns*, but for those we need environments for variables first.
