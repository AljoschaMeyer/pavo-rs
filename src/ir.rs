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
    binding_analysis::{Statement, _Statement, Expression, _Expression, DeBruijn},
    value::Value,
    context::{Computation, Context, PavoResult, DbgTrace},
};

/// A control flow graph of basic blocks, each consisting of a sequence of statements.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IrChunk {
    // The ir instructions, as a graph of basic blocks.
    basic_blocks: Vec<Vec<Instruction>>,
}

type RegisterId = usize;
type BBId = usize;

// Addresses a storage slot where a computation can write `Value`s to (or from where to read them).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Addr {
    // Address of a register in a `LocalState`.
    //
    // Register 0 is used for passing data from one statement to the next.
    // Register 1 is used by while loops to return the correct value.
    // Additional registers are used when multiple values need to be kept in memory simutaneously,
    // e.g. all the arguments that are passed to a function call.
    Register(RegisterId),
    Environment(DeBruijn),
}

impl Addr {
    fn reg(r: RegisterId) -> Addr {
        Addr::Register(r)
    }

    fn env(id: DeBruijn) -> Addr {
        Addr::Environment(id)
    }
}

/// A single instruction of the ir.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Instruction {
    /// Do nothing but evaluate to the given value and store it in the given location.
    Literal(Value, Addr),
    /// Jump to the given basic block. If the usize is `BB_RETURN`, return from the function instead.
    Jump(BBId),
    /// Jump to the given basic block. If the usize is `BB_RETURN`, throw from the function instead.
    Throw(BBId),
    /// Jump to the first basic block if the value at the Addr is truthy, else to the second one.
    CondJump(Addr, BBId, BBId),
    /// Write the value at Addr `src` to the Addr `dst`.
    Write { src: Addr, dst: Addr },
    /// Swap the values in the given Addrs.
    Swap(Addr, Addr),
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

    // Set register 0 to `nil`.
    fn eval_to_nil(&mut self) {
        self.append(Literal(Value::new_nil(), Addr::reg(0)))
    }

    // Consume the builder to create an IrChunk.
    fn into_ir(self) -> IrChunk {
        IrChunk {
            basic_blocks: self.blocks,
        }
    }
}

/// Converts an abstract syntax tree into an `IrChunk`.
pub fn ast_to_ir(ast: Vec<Statement>) -> IrChunk {
    let mut bbb = BBB::new();
    block_to_ir(ast, BB_RETURN, &mut bbb);
    return bbb.into_ir();
}

// Convert a sequence of statements into instructions and basic blocks, using the given BBB.
// As the last instruction, jump to the basic block `jump_to`.
fn block_to_ir(block: Vec<Statement>, jump_to: BBId, bbb: &mut BBB) {
    let len = block.len();
    for statement in block.into_iter() {
        statement_to_ir(statement, bbb);
    }

    if len == 0 {
        bbb.eval_to_nil();
    }

    bbb.append(Jump(jump_to));
}

// Convert a single statement into instructions and basic blocks, using the given BBB..
fn statement_to_ir(statement: Statement, bbb: &mut BBB) {
    match statement.1 {
        _Statement::Expression(exp) => exp_to_ir(exp, bbb),
        _Statement::Return(exp) => {
            exp_to_ir(exp, bbb);
            bbb.append(Jump(BB_RETURN));
        }
        _Statement::Break(exp) => {
            exp_to_ir(exp, bbb);
            bbb.append(Jump(bbb.breakpoint));
        }
        _Statement::Throw(exp) => {
            exp_to_ir(exp, bbb);
            bbb.append(Throw(bbb.trap_handler));
        }
        _Statement::Assign(de_bruijn, rhs) => {
            exp_to_ir(rhs, bbb);
            bbb.append(Write { src: Addr::reg(0), dst: Addr::env(de_bruijn) });
            bbb.eval_to_nil();
        }
    }
}

// Convert a single expression into instructions and basic blocks, using the given BBB..
fn exp_to_ir(exp: Expression, bbb: &mut BBB) {
    match exp.1 {
        _Expression::Nil => {
            bbb.append(Literal(Value::new_nil(), Addr::reg(0)));
        }
        _Expression::Bool(b) => {
            bbb.append(Literal(Value::new_bool(b), Addr::reg(0)));
        }
        _Expression::Id(id) => {
            bbb.append(Write {src: Addr::env(id), dst: Addr::reg(0)});
        },
        _Expression::If(cond, then_block, else_block) => {
            exp_to_ir(*cond, bbb);

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
        _Expression::Try(try_block, pattern_id, catch_block, finally_block) => {
            let bb_try = bbb.new_block();
            let bb_catch = bbb.new_block();
            let bb_finally = bbb.new_block();
            let bb_cont = bbb.new_block();

            bbb.append(Jump(bb_try));
            let prev_trap_handler = bbb.trap_handler;
            bbb.trap_handler = bb_catch;
            bbb.set_active_block(bb_try);
            block_to_ir(try_block, bb_finally, bbb);
            bbb.trap_handler = prev_trap_handler;

            bbb.set_active_block(bb_catch);
            bbb.append(Write { src: Addr::reg(0), dst: Addr::env(pattern_id) });
            block_to_ir(catch_block, bb_finally, bbb);

            bbb.set_active_block(bb_finally);
            if finally_block.len() > 0 {
                block_to_ir(finally_block, bb_cont, bbb);
            } else {
                bbb.append(Jump(bb_cont));
            }

            bbb.set_active_block(bb_cont);
        }
        _Expression::Thrown => {
            // no-op, thrown value is already in register 0, where the trap handling expects it
        }
    }
}

///////////////////////////////////////////////
// Everything below happens at pavo runtime. //
///////////////////////////////////////////////

// The local state upon which the instructions to operate. It is local to each invocation of
// `Computation::compute`.
struct LocalState {
    // Index into the graph of instructions that indicates which instruction to execute next.
    // "pc" stands for "program counter".
    //
    // First usize is the basic block, second one the offset in the basic block.
    pc: (BBId, usize),
    // Temporary storage slots for `Value`s.
    registers: Vec<Value>,
}

impl LocalState {
    // Create and initialize a `LocalState` suitable for executing the given chunk.
    fn new(_chunk: &IrChunk) -> LocalState {
        LocalState {
            pc: (0, 0),
            registers: vec![Value::default(), Value::default()], // first two registers are special
        }
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
    entry: usize,
}

impl Closure {
    /// Create a closure suitable for executing the main body of a script.
    ///
    /// Behaves as if the script was the body of a zero-argument function defined in the lexical
    /// scope of the (given) top-level environment.
    pub fn from_script_chunk(script: IrChunk) -> Closure {
        Closure {
            fun: Rc::new(script),
            env: Environment::child(top_level()),
            entry: 0,
        }
    }
}

// TODO XXX This is temporary...
fn top_level() -> Gc<GcCell<Environment>> {
    Environment::root()
}

impl Addr {
    // Use an `Addr` to retrieve a value. This can not fail, unless we created erroneous ir code.
    fn load(self, local: &LocalState, env: &Gc<GcCell<Environment>>) -> Value {
        match self {
            Addr::Register(index) => local.registers[index].clone(),
            Addr::Environment(de_bruijn) => env.borrow().get(de_bruijn),
        }
    }

    // Use an `Addr` to store a value. This can not fail, unless we created erroneous vm code.
    fn store(self, val: Value, local: &mut LocalState, env: &Gc<GcCell<Environment>>) {
        match self {
            Addr::Register(index) => {
                if index >= local.registers.len()  {
                    local.registers.resize_with(index + 1, Default::default);
                }
                local.registers[index] = val;
            }
            Addr::Environment(de_bruijn) => env.borrow_mut().set(de_bruijn, val),
        }
    }
}

// An IrChunk encodes a pavo computation, so it can implement the `Computation` trait.
//
// We will remove this impl at a later point: Once we implement value bindings (aka variables),
// we need an environment for computation. An IrChunk only stores the raw code, but not the
// corresponding environment (it's a function, not a closure).
impl Computation for Closure {
    // To perform the computation, interpret the instructions of the chunk.
    //
    // Since at this point we only implement the case of running a full pavo file, there is no
    // notion of arguments and we can fully ignore them.
    fn compute<Args: IntoIterator<Item = Value>>(&self, _: Args, _: &mut Context) -> PavoResult {
        let mut state = LocalState::new(&self.fun);

        loop {
            state.pc.1 += 1;
            match &self.fun.basic_blocks[state.pc.0][state.pc.1 - 1] {
                Literal(val, dst) => dst.store(val.clone(), &mut state, &self.env),

                Jump(block) => {
                    if *block == BB_RETURN {
                        // register 0 holds the evaluation result of the previously executed statement
                        return Ok(Addr::reg(0).load(&state, &self.env));
                    } else {
                        state.pc = (*block, 0);
                    }
                }

                Throw(block) => {
                    if *block == BB_RETURN {
                        // register 0 holds the evaluation result of the previously executed statement
                        return Err((Addr::reg(0).load(&state, &self.env), DbgTrace));
                    } else {
                        state.pc = (*block, 0);
                    }
                }

                CondJump(cond, then_block, else_block) => {
                    if cond.load(&state, &self.env).truthy() {
                        state.pc = (*then_block, 0);
                    } else {
                        state.pc = (*else_block, 0);
                    }
                }

                Write { src, dst } => dst.store(src.load(&state, &self.env), &mut state, &self.env),

                Swap(a, b) => {
                    let val_a = a.load(&state, &self.env);
                    let val_b = b.load(&state, &self.env);
                    a.store(val_b, &mut state, &self.env);
                    b.store(val_a, &mut state, &self.env);
                }
            }
        }
    }
}
