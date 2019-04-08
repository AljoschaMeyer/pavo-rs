//! An intermediate representation for pavo code. Unlike ir in a compiler, it simply gets
//! interpreted.
//!
//! A chunk of ir (`IrChunk`) is a graph of
//! [basic blocks](https://en.wikipedia.org/wiki/Basic_block). The blocks themselves are sequences
//! of ir instructions (`Instruction`). The ir instructionss can be thought of as a "desugared"
//! version of pavo.

use std::rc::Rc;

use gc::{Gc, GcCell};
use gc_derive::{Trace, Finalize};

use crate::{
    binding_analysis::{
        Statement, _Statement, Expression, _Expression, DeBruijn,
        Patterns, Pattern, _Pattern, ArrayPattern, ArrayPatternOptionals,
    },
    builtins,
    value::{Value, Fun},
    context::{Computation, Context, PavoResult},
    util::FnWrap as W,
    toplevel::top_level,
    gc_foreign::Vector,
};

/// A control flow graph of basic blocks, each consisting of a sequence of statements.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IrChunk {
    // The ir instructions, as a graph of basic blocks.
    basic_blocks: Vec<Vec<Instruction>>,
}

type BBId = usize;

// Addresses a storage slot where a computation can write `Value`s to (or from where to read them).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Addr {
    Stack,
    Environment(DeBruijn),
}

impl Addr {
    fn env(id: DeBruijn) -> Addr {
        Addr::Environment(id)
    }
}

/// A single instruction of the ir.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Instruction {
    /// Push the value to the stack.
    Literal(Value),
    /// Create a closure value with the given IrChunk, push it to the stack.
    /// The BBId is the block at which to begin execution of the chunk.
    FunLiteral(Rc<IrChunk>, BBId),
    /// Jump to the given basic block. If the bb is `BB_RETURN`, return from the function instead.
    Jump(BBId),
    /// Jump to the first basic block if the value at the Addr is truthy, else to the second one.
    CondJump(Addr, BBId, BBId),
    /// Jump to the current catch handler basic block. If the bb is `BB_RETURN`, the function throws.
    Throw,
    /// Set the catch hander basic block.
    SetCatchHandler(BBId),
    /// Push the value at the Addr to the stack.
    Push(Addr),
    /// Pop the stack and write the value to the Addr.
    Pop(Addr),
    /// Clone the topmost stack value and push it onto the stack.
    Duplicate,
    /// Drop the topmost stack value without writing it anywhere.
    DropTop,
    /// Invoke the topmost value with the next `usize` many arguments. Remove them from the stack
    /// afterwards. If the bool is true, push the result onto the stack.
    ///
    /// The args need to be passed to the function in fifo order, *not* lifo.
    Call(usize, bool),
    /// Reuse the current stack for "calling" the closure at the DeBruijn address, entering at its
    /// entry (read from the closure at runtime, because I'm too lazy to implement this properly),
    /// by jumping there, with the usize topmost (fifo) arguments as a single array value on
    /// the stack.
    TailCall(usize, DeBruijn),
    /// Invoke the builtin function with the topmost value. If the bool is true, push the result
    /// onto the stack.
    CallBuiltin1(W<fn(&Value, &mut Context) -> PavoResult>, bool),
    /// Invoke the builtin function with the two topmost values (fifo). If the bool is true, push
    /// the result onto the stack.
    CallBuiltin2(W<fn(&Value, &Value, &mut Context) -> PavoResult>, bool),
    /// Invoke the builtin function with as many values from the stack (fifo) as specified. If the
    /// bool is true, push the result onto the stack.
    CallBuiltinMany(W<fn(&[Value], &mut Context) -> PavoResult>, usize, bool),
}
use Instruction::*;

// If this is given as an unconditional jump address, return from the function instead.
const BB_RETURN: BBId = std::usize::MAX;

// BasicBlockBuilder, a helper for constructing the graph of basic blocks.
//
// It provides a stateful api. There's the `current` block on which to work, and methods to modify
// it.
struct BBB {
    // All basic blocks generated so far.
    blocks: Vec<Vec<Instruction>>,
    // Index of the currently active block.
    current: BBId,
    // Index of the block to which a `break` statement should jump.
    // This has nothing to do with an *actual breakpoint*, but you can't stop me!
    breakpoint: BBId,
    // Index of the block to which a trap instruction should jump.
    trap_handler: BBId,
}

impl BBB {
    fn new() -> BBB {
        BBB {
            blocks: vec![vec![]],
            current: 0,
            breakpoint: BB_RETURN,
            trap_handler: BB_RETURN,
        }
    }

    // Create a new, empty basic block, and return it's id.
    fn new_block(&mut self) -> BBId {
        self.blocks.push(vec![]);
        return self.blocks.len() - 1;
    }

    // Set the block on which the BBB operates.
    fn set_active_block(&mut self, bb: BBId) {
        self.current = bb;
    }

    // Append an instruction to the currently active block.
    fn append(&mut self, inst: Instruction) {
        self.blocks[self.current].push(inst);
    }

    fn push_nil(&mut self) {
        self.append(Literal(Value::new_nil()))
    }

    // Consume the builder to create an IrChunk.
    fn into_ir(self) -> IrChunk {
        IrChunk {
            basic_blocks: self.blocks,
        }
    }
}

#[derive(Debug)]
struct Tails(Vec<Entry> /* must be sorted ascendingly */);

impl Tails {
    fn is_tco(&self, fun: &Expression) -> bool {
        match fun.1 {
            _Expression::Id(db) => {
                self.0.binary_search(& Entry {
                    de_bruijn: db,
                }).is_ok()
            }
            _ => false,
        }
    }

    fn empty() -> Tails {
        Tails(vec![])
    }

    fn from_de_bruijns<I: Iterator<Item = DeBruijn>>(input: I) -> Tails {
        Tails(input.map(|de_bruijn| Entry { de_bruijn: DeBruijn { up: 1, id: de_bruijn.id } }).collect())
    }
}

#[derive(Debug, Clone)]
struct Entry {
    de_bruijn: DeBruijn,
}

impl PartialEq for Entry {
    fn eq(&self, other: &Self) -> bool {
        self.de_bruijn == other.de_bruijn
    }
}

impl Eq for Entry {}

impl Ord for Entry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.de_bruijn.cmp(&other.de_bruijn)
    }
}

impl PartialOrd for Entry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Converts an abstract syntax tree into an `IrChunk`.
pub fn ast_to_ir(ast: Vec<Statement>) -> IrChunk {
    let mut bbb = BBB::new();
    fun_to_ir(ArrayPattern::empty(), ast, BB_RETURN, true, &mut bbb, &Tails::empty());
    return bbb.into_ir();
}

fn fun_to_ir(args: ArrayPattern, body: Vec<Statement>, jump_to: BBId, push: bool, bbb: &mut BBB, tails: &Tails) {
    let body_bb = bbb.new_block();
    array_pattern_to_ir(args, body_bb, bbb.trap_handler, bbb);
    bbb.set_active_block(body_bb);
    block_to_ir(body, jump_to, push, bbb, tails);
}

// Convert a sequence of statements into instructions and basic blocks, using the given BBB.
// As the last instruction, jump to the basic block `jump_to`.
fn block_to_ir(block: Vec<Statement>, jump_to: BBId, push: bool, bbb: &mut BBB, tails: &Tails) {
    let len = block.len();
    if len == 0 {
        if push {
            bbb.push_nil();
        }
    } else {
        for (i, statement) in block.into_iter().enumerate() {
            if i + 1 < len {
                statement_to_ir(statement, false, bbb, tails);
            } else {
                statement_to_ir(statement, push, bbb, tails);
            }
        }
    }

    bbb.append(Jump(jump_to));
}

// Convert a single statement into instructions and basic blocks, using the given BBB..
fn statement_to_ir(statement: Statement, push: bool, bbb: &mut BBB, tails: &Tails) {
    match statement.1 {
        _Statement::Expression(exp) => exp_to_ir(exp, push, bbb, tails),
        _Statement::Return(exp) => {
            exp_to_ir(exp, true, bbb, tails);
            bbb.append(Jump(BB_RETURN));
        }
        _Statement::Break(exp) => {
            exp_to_ir(exp, true, bbb, tails);
            bbb.append(Jump(bbb.breakpoint));
        }
        _Statement::Throw(exp) => {
            exp_to_ir(exp, true, bbb, tails);
            bbb.append(Throw);
        }
        _Statement::Assign(pats, rhs) => {
            exp_to_ir(rhs, true, bbb, tails);
            let cont_bb = bbb.new_block();
            patterns_to_ir(pats, cont_bb, bbb.trap_handler, bbb, tails);
            bbb.set_active_block(cont_bb);
            if push {
                bbb.push_nil();
            }
        }
        _Statement::Rec(defs) => {
            let (chunk, entries) = defs_to_chunk(defs);
            let chunk = Rc::new(chunk);

            for (db, entry) in entries {
                bbb.append(FunLiteral(chunk.clone(), entry));
                bbb.append(Pop(Addr::env(db)))
            }

            if push {
                bbb.push_nil();
            }
        }
    }
}

// Returns the chunk for the closure, and the entry points (in the same order as the defs)
fn defs_to_chunk(defs: Vec<(DeBruijn, ArrayPattern, Vec<Statement>)>) -> (IrChunk, Vec<(DeBruijn, BBId)>) {
    let mut bbb = BBB::new();
    let mut tc_info = Vec::with_capacity(defs.len());
    let tails = Tails::from_de_bruijns(defs.iter().map(|(db, _, _)| db.clone()));

    for (db, args, body) in defs.into_iter() {
        if bbb.current != 0 {
            let next = bbb.new_block();
            bbb.set_active_block(next);
        }

        tc_info.push((db, bbb.current));
        fun_to_ir(args, body, BB_RETURN, true, &mut bbb, &tails);
    }

    return (bbb.into_ir(), tc_info);
}

// Convert a single expression into instructions and basic blocks, using the given BBB.
fn exp_to_ir(exp: Expression, push: bool, bbb: &mut BBB, tails: &Tails) {
    match exp.1 {
        _Expression::Nil => {
            if push {
                bbb.push_nil();
            }
        }
        _Expression::Bool(b) => {
            if push {
                bbb.append(Literal(Value::new_bool(b)));
            }
        }
        _Expression::Int(n) => {
            if push {
                bbb.append(Literal(Value::new_int(n)));
            }
        }
        _Expression::Fun(args, body) => {
            if push {
                let mut inner_bbb = BBB::new();
                fun_to_ir(args, body, BB_RETURN, true, &mut inner_bbb, &Tails::empty());
                bbb.append(FunLiteral(Rc::new(inner_bbb.into_ir()), 0));
            }
        }
        _Expression::Id(id) => {
            if push {
                bbb.append(Push(Addr::env(id)));
            }
        },
        _Expression::Try(try_block, pats, catch_block, finally_block) => {
            let bb_try = bbb.new_block();
            let bb_catch = bbb.new_block();
            let bb_catch_body = bbb.new_block();
            let bb_cont = bbb.new_block();
            let bb_finally = finally_block.as_ref().map(|_| bbb.new_block()).unwrap_or(bb_cont);

            bbb.append(Jump(bb_try));
            let prev_trap_handler = bbb.trap_handler;
            bbb.set_active_block(bb_try);
            bbb.trap_handler = bb_catch;
            bbb.append(SetCatchHandler(bbb.trap_handler));
            block_to_ir(try_block, bb_finally, push, bbb, tails);

            bbb.set_active_block(bb_catch);
            bbb.trap_handler = prev_trap_handler;
            bbb.append(SetCatchHandler(bbb.trap_handler));
            patterns_to_ir(pats, bb_catch_body, bbb.trap_handler, bbb, tails);
            bbb.set_active_block(bb_catch_body);
            block_to_ir(catch_block, bb_finally, push, bbb, tails);

            bbb.set_active_block(bb_finally);
            bbb.trap_handler = prev_trap_handler;
            bbb.append(SetCatchHandler(bbb.trap_handler));

            if let Some(block) = finally_block {
                block_to_ir(block, bb_cont, push, bbb, tails);
                bbb.set_active_block(bb_cont);
            }
        }
        _Expression::Case(matcher, arms) => {
            let num_arms = arms.len();
            exp_to_ir(*matcher, num_arms > 0, bbb, tails);

            if num_arms == 0 {
                bbb.append(DropTop); // drop the evaluated matcher
                if push {
                    bbb.push_nil();
                }
            } else {
                // blocks[i].0: duplicate top of stack and match against pattern, going to
                // blocks[i].1 (the arm's body) if matched, or to block[i+1].0 if it didn't match
                let blocks: Vec<_> = arms.iter().map(|_| (bbb.new_block(), bbb.new_block())).collect();
                let bb_cont = bbb.new_block();

                bbb.append(Jump(blocks[0].0));
                bbb.set_active_block(blocks[0].0);
                for (i, (pats, body)) in arms.into_iter().enumerate() {
                    if i < num_arms {
                        if i > 0 {
                            bbb.append(DropTop); // drops the exception of the previous, non-matching patterns
                        }
                        bbb.append(Duplicate); // duplicate the value to match against
                        patterns_to_ir(pats, blocks[i].1, blocks[i + 1].0, bbb, tails);

                        bbb.set_active_block(blocks[i].1);
                        bbb.append(DropTop); // drop the duplicated value
                        block_to_ir(body, bb_cont, push, bbb, tails);

                        bbb.set_active_block(blocks[i + 1].0);
                    } else {
                        patterns_to_ir(pats, blocks[i].1, bbb.trap_handler, bbb, tails);

                        bbb.set_active_block(blocks[i].1);
                        block_to_ir(body, bb_cont, push, bbb, tails);
                    }
                }

                bbb.set_active_block(bb_cont);
            }
        }
        _Expression::Loop(matcher, arms) => {
            let num_arms = arms.len();
            let bb_matcher = bbb.new_block();

            // pretend there was a previous loop iteration that returned nil (so that we evaluate
            // to nil if no pattern matches in the first iteration)
            if push {
                bbb.push_nil();
            }

            bbb.set_active_block(bb_matcher);
            exp_to_ir(*matcher, true, bbb, tails);

            if num_arms == 0 {
                bbb.append(DropTop); // drop the evaluated matcher
            } else {
                // blocks[i].0: duplicate top of stack and match against pattern, going to
                // blocks[i].1 (the arm's body) if matched, or to block[i+1].0 if it didn't match
                let blocks: Vec<_> = arms.iter().map(|_| (bbb.new_block(), bbb.new_block())).collect();
                let bb_cont = bbb.new_block();

                let prev_breakpoint = bbb.breakpoint;
                bbb.breakpoint = bb_cont;

                bbb.append(Jump(blocks[0].0));
                bbb.set_active_block(blocks[0].0);

                for (i, (pats, body)) in arms.into_iter().enumerate() {
                    if i < num_arms {
                        if i > 0 {
                            bbb.append(DropTop); // drops the exception of the previous, non-matching pattern
                        }
                        bbb.append(Duplicate);
                        patterns_to_ir(pats, blocks[i].1, blocks[i + 1].0, bbb, tails);

                        bbb.set_active_block(blocks[i].1);
                        bbb.append(DropTop); // drop the duplicated value
                        if push {
                            bbb.append(DropTop); // drop the result of the previous loop iteration
                        }
                        block_to_ir(body, bb_matcher, push, bbb, tails);

                        bbb.set_active_block(blocks[i + 1].0);
                    } else {
                        patterns_to_ir(pats, blocks[i].1, bb_cont, bbb, tails);

                        bbb.set_active_block(blocks[i].1);
                        if push {
                            bbb.append(DropTop); // drop the result of the previous loop iteration
                        }
                        block_to_ir(body, bb_cont, push, bbb, tails);
                    }
                }

                bbb.set_active_block(bb_cont);
                bbb.breakpoint = prev_breakpoint;
            }
        }
        _Expression::Invocation(fun, args, tail) => {
            let num_args = args.len();

            for arg in args.into_iter() {
                exp_to_ir(arg, true, bbb, tails);
            }

            if tail && tails.is_tco(&fun) {
                match fun.1 {
                    _Expression::Id(db) => {
                        bbb.append(TailCall(num_args, db));
                    }
                    _ => unreachable!("if `is_tco(&fun)`, then fun must be an identifier expression"),
                }
            } else {
                exp_to_ir(*fun, true, bbb, tails);
                bbb.append(Call(num_args, push));
            }
        }
        _Expression::Builtin1(fun, arg) => {
            exp_to_ir(*arg, true, bbb, tails);
            bbb.append(CallBuiltin1(fun, push))
        }
        _Expression::Builtin2(fun, lhs, rhs) => {
            exp_to_ir(*lhs, true, bbb, tails);
            exp_to_ir(*rhs, true, bbb, tails);
            bbb.append(CallBuiltin2(fun, push))
        }
        _Expression::BuiltinMany(fun, args) => {
            let num_args = args.len();

            for arg in args.into_iter() {
                exp_to_ir(arg, true, bbb, tails);
            }

            bbb.append(CallBuiltinMany(fun, num_args, push));
        }
    }
}

// Convert some patterns into instructions and basic blocks, using the given BBB.
// Matches the patterns against the top of the stack. If successful, jumps to `yay`,
// else pushes an error value to the stack and jumps to `nay`.
//
// bbb.active_block stays unmodified.
fn patterns_to_ir(pats: Patterns, yay: BBId, nay: BBId, bbb: &mut BBB, tails: &Tails) {
    let prev_active_block = bbb.current;
    let num_pats = pats.1.len();
    debug_assert!(num_pats > 0);

    let blocks: Vec<_> = pats.1.iter().map(|_| bbb.new_block()).collect();
    let bb_pre_yay = bbb.new_block();
    let bb_pre_nay = bbb.new_block();

    bbb.append(Jump(blocks[0]));
    bbb.set_active_block(blocks[0]);

    for (i, pat) in pats.1.into_iter().enumerate() {
        if i < num_pats {
            if i > 0 {
                bbb.append(DropTop); // drops the exception of the previous, non-matching pattern
            }
            bbb.append(Duplicate);
            pattern_to_ir(pat, bb_pre_yay, blocks[i + 1], bbb);
            bbb.set_active_block(blocks[i + 1]);
        } else {
            bbb.append(Duplicate);
            pattern_to_ir(pat, bb_pre_yay, bb_pre_nay, bbb);
        }
    }

    bbb.set_active_block(bb_pre_yay);
    bbb.append(DropTop);
    match pats.2 {
        Some(guard) => {
            exp_to_ir(*guard, true, bbb, tails);
            bbb.append(CondJump(Addr::Stack, yay, nay));
        }
        None => bbb.append(Jump(yay)),
    }

    bbb.set_active_block(bb_pre_nay);
    bbb.append(DropTop);

    bbb.set_active_block(prev_active_block);
}

// Consume the topmost stack element, matching it against the pattern. If successful, jumps to
// `yay`, else pushes an error value to the stack and jumps to `nay`.
//
// bbb.active_block stays unmodified.
fn pattern_to_ir(pat: Pattern, yay: BBId, nay: BBId, bbb: &mut BBB) {
    let prev_active_block = bbb.current;
    let prev_trap_handler = bbb.trap_handler;

    bbb.trap_handler = nay;
    match pat.1 {
        _Pattern::Blank => bbb.append(Jump(yay)),
        _Pattern::Nil => {
            bbb.append(Literal(Value::new_nil()));
            bbb.append(CallBuiltin2(W(builtins::assert_eq), false));
            bbb.append(Jump(yay))
        }
        _Pattern::Array(ArrayPattern(left, opts, right)) => {
            let left_len = left.len();
            let right_len = right.len();

            // Make sure it's an array and there are enough entries for all mandatory patterns
            bbb.append(Duplicate); // FIXME duplicate is not dropped if anything throws
            bbb.append(Literal(Value::new_int_usize(left_len + right_len)));
            bbb.append(CallBuiltin2(W(builtins::assert_arr_len_at_least), false));

            for (i, sub_pat) in left.into_iter().enumerate() {
                bbb.append(Duplicate); // FIXME duplicate is not dropped if anything throws
                bbb.append(Literal(Value::new_int_usize(i)));
                bbb.append(CallBuiltin2(W(builtins::arr_get), true));
                pattern_to_ir(sub_pat, TODO, TODO, bbb);
            }

            unimplemented!()
        }
        _ => unimplemented!(),
    }

    bbb.set_active_block(prev_active_block);
    bbb.trap_handler = prev_trap_handler;
}

// Consume the topmost stack element, matching it against the ArrayPattern.
fn array_pattern_to_ir(p: ArrayPattern, yay: BBId, nay: BBId, bbb: &mut BBB) {
    pattern_to_ir(Pattern::array(p), yay, nay, bbb);
}

///////////////////////////////////////////////
// Everything below happens at pavo runtime. //
///////////////////////////////////////////////

// The local state upon which the instructions to operate. It is local to each invocation of
// `Computation::compute`.
#[derive(Debug)]
struct LocalState {
    // Index into the graph of instructions that indicates which instruction to execute next.
    // "pc" stands for "program counter".
    //
    // First usize is the basic block, second one the offset in the basic block.
    pc: (BBId, usize),
    // Temporary storage slots for `Value`s.
    stack: Vec<Value>,
    // Where to resume execution after something throws. If this is `BB_RETURN`, the function
    // itself throws rather than resuming execution.
    catch_handler: BBId,
}

impl LocalState {
    // Create and initialize a `LocalState` suitable for executing the given chunk.
    fn new(_chunk: &IrChunk, entry: BBId) -> LocalState {
        LocalState {
            pc: (entry, 0),
            stack: vec![],
            catch_handler: BB_RETURN,
        }
    }

    fn push(&mut self, val: Value) {
        self.stack.push(val);
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    fn args(&mut self, num: usize) -> &[Value] {
        let start = self.stack.len() - num;
        &self.stack[start..]
    }

    fn pop_n(&mut self, num: usize) {
        let new_len = self.stack.len() - num;
        self.stack.truncate(new_len);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
pub struct Environment {
    // The bindings local to this environment.
    bindings: Vec<Value>,
    // (Mutable) access to the parent binding, which is `None` for the top-level environment.
    parent: Option<Gc<GcCell<Environment>>>,
}

impl Environment {
    // Look up the value addressed by the given DeBruijnPair. Panics if the address is invalid
    // (which only happens if compilation is buggy).
    pub fn get(&self, mut addr: DeBruijn) -> Value {
        if addr.up == 0 {
            self.bindings[addr.id].clone()
        } else {
            addr.up -= 1;
            self.parent.as_ref().unwrap().borrow().get(addr)
        }
    }

    // Set the value at the given address. Panics if the address is invalid (which only happens if
    // compilation is buggy).
    pub fn set(&mut self, mut addr: DeBruijn, val: Value) {
        if addr.up == 0 {
            if addr.id >= self.bindings.len()  {
                self.bindings.resize_with(addr.id + 1, Default::default);
            }
            self.bindings[addr.id] = val;
        } else {
            addr.up -= 1;
            self.parent.as_ref().unwrap().borrow_mut().set(addr, val);
        }
    }

    pub fn child(parent: Gc<GcCell<Environment>>) -> Gc<GcCell<Environment>> {
        let env = Environment::root();
        env.borrow_mut().parent = Some(parent);
        env
    }

    pub fn root() -> Gc<GcCell<Environment>> {
        Gc::new(GcCell::new(Environment {
            bindings: vec![],
            parent: None,
        }))
    }
}

// An IrChunk together with an environment. This is a runtime value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Trace, Finalize)]
pub struct Closure {
    #[unsafe_ignore_trace]
    fun: Rc<IrChunk>,
    env: Gc<GcCell<Environment>>,
    // The basic block at which to begin execution of the `fun`.
    pub entry: usize,
}

impl Closure {
    /// Create a closure suitable for executing the main body of a script.
    ///
    /// Behaves as if the script was the body of a zero-argument function defined in the lexical
    /// scope of the (given) top-level environment.
    pub fn from_script_chunk(script: IrChunk) -> Closure {
        Closure::from_chunk(Rc::new(script), Environment::child(top_level()), 0)
    }

    fn from_chunk(fun: Rc<IrChunk>, env: Gc<GcCell<Environment>>, entry: usize) -> Closure {
        Closure {
            fun,
            env,
            entry,
        }
    }
}

impl Addr {
    // Use an `Addr` to retrieve a value. This can not fail, unless we created erroneous ir code.
    fn load(self, local: &mut LocalState, env: &Gc<GcCell<Environment>>) -> Value {
        match self {
            Addr::Stack => local.stack.pop().unwrap(),
            Addr::Environment(de_bruijn) => env.borrow().get(de_bruijn),
        }
    }

    // Use an `Addr` to store a value. This can not fail, unless we created erroneous vm code.
    fn store(self, val: Value, local: &mut LocalState, env: &Gc<GcCell<Environment>>) {
        match self {
            Addr::Stack => local.stack.push(val),
            Addr::Environment(de_bruijn) => env.borrow_mut().set(de_bruijn, val),
        }
    }
}

impl Computation for Closure {
    // To perform the computation, interpret the instructions of the chunk.
    //
    // Since at this point we only implement the case of running a full pavo file, there is no
    // notion of arguments and we can fully ignore them.
    fn compute_vector(&self, args: Vector<Value>, ctx: &mut Context) -> PavoResult {
        let mut state = LocalState::new(&self.fun, self.entry);
        state.push(Value::new_array(args));

        loop {
            state.pc.1 += 1;
            match &self.fun.basic_blocks[state.pc.0][state.pc.1 - 1] {
                Literal(val) => state.push(val.clone()),

                FunLiteral(chunk, entry) => state.push(Value::new_closure(
                    Gc::new(Closure::from_chunk(
                        chunk.clone(),
                        Environment::child(self.env.clone()),
                        *entry))
                )),

                Jump(block) => {
                    if *block == BB_RETURN {
                        return Ok(state.pop());
                    } else {
                        state.pc = (*block, 0);
                    }
                }

                CondJump(cond, then_block, else_block) => {
                    if cond.load(&mut state, &self.env).truthy() {
                        state.pc = (*then_block, 0);
                    } else {
                        state.pc = (*else_block, 0);
                    }
                }

                Throw => {
                    if state.catch_handler == BB_RETURN {
                        return Err(state.pop());
                    } else {
                        state.pc = (state.catch_handler, 0);
                    }
                }

                SetCatchHandler(bb) => state.catch_handler = *bb,

                Push(addr) => {
                    let val = addr.load(&mut state, &self.env);
                    state.push(val);
                }

                Pop(addr) => {
                    let val = state.pop();
                    addr.store(val, &mut state, &self.env);
                }

                Duplicate => {
                    let val = state.pop();
                    state.push(val.clone());
                    state.push(val);
                }

                DropTop => {let _ = state.pop();}

                Call(num_args, push) => {
                    let fun = state.pop();
                    let args = state.args(*num_args);

                    match fun.compute(args, ctx) {
                        Ok(val) => {
                            state.pop_n(*num_args);
                            if *push {
                                state.push(val);
                            }
                        }
                        Err(err) => {
                            state.pop_n(*num_args);
                            if state.catch_handler == BB_RETURN {
                                return Err(err);
                            } else {
                                state.push(err);
                                state.pc = (state.catch_handler, 0);
                            }
                        }
                    }
                }

                CallBuiltin1(fun, push) => {
                    let arg = state.pop();

                    match fun.0(&arg, ctx) {
                        Ok(val) => {
                            if *push {
                                state.push(val);
                            }
                        }
                        Err(err) => {
                            if state.catch_handler == BB_RETURN {
                                return Err(err);
                            } else {
                                state.push(err);
                                state.pc = (state.catch_handler, 0);
                            }
                        }
                    }
                }

                CallBuiltin2(fun, push) => {
                    let args = state.args(2);

                    match fun.0(&args[0], &args[1], ctx) {
                        Ok(val) => {
                            state.pop_n(2);
                            if *push {
                                state.push(val);
                            }
                        }
                        Err(err) => {
                            state.pop_n(2);
                            if state.catch_handler == BB_RETURN {
                                return Err(err);
                            } else {
                                state.push(err);
                                state.pc = (state.catch_handler, 0);
                            }
                        }
                    }
                }

                CallBuiltinMany(fun, num_args, push) => {
                    let args = state.args(*num_args);

                    match fun.0(args, ctx) {
                        Ok(val) => {
                            state.pop_n(*num_args);
                            if *push {
                                state.push(val);
                            }
                        }
                        Err(err) => {
                            state.pop_n(*num_args);
                            if state.catch_handler == BB_RETURN {
                                return Err(err);
                            } else {
                                state.push(err);
                                state.pc = (state.catch_handler, 0);
                            }
                        }
                    }
                }

                TailCall(num_args, db) => {
                    let args = state.args(*num_args);
                    let args_val = Value::new_array(Vector(args.into()));
                    state.push(args_val);

                    let block = match &Addr::env(*db).load(&mut state, &self.env) {
                        Value::Fun(Fun::Closure(c)) => c.entry,
                        _ => unreachable!("TailCall DeBruijn must point to a closure"),
                    };
                    state.pc = (block, 0);
                }
            }
        }
    }
}
