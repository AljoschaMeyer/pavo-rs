//! An intermediate representation for pavo code. Unlike ir in a compiler, it simply gets
//! interpreted.
//!
//! A chunk of ir (`IrChunk`) is a graph of
//! [basic blocks](https://en.wikipedia.org/wiki/Basic_block). The blocks themselves are sequences
//! of ir instructions (`Instruction`). The ir instructionss can be thought of as a "desugared"
//! version of pavo.

use crate::{
    syntax::{Statement, _Statement, Expression, _Expression},
    value::Value,
    context::{Computation, Context, PavoResult},
};

/// A control flow graph of basic blocks, each consisting of a sequence of statements.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IrChunk {
    // The ir instructions, as a graph of basic blocks.
    basic_blocks: Vec<Vec<Instruction>>,
    // The number of registers the code needs to work.
    num_registers: usize,
}

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

impl Addr {
    fn reg(r: usize) -> Addr {
        Addr::Register(r)
    }
}

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
use Instruction::*;

// If this is given as an unconditional jump address, return from the function instead.
const BB_RETURN: usize = std::usize::MAX;

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

/// Converts an abstract syntax tree into an `IrChunk`.
pub fn ast_to_ir(ast: &Box<[Statement]>) -> IrChunk {
    let mut bbb = BBB::new();
    block_to_ir(ast, BB_RETURN, &mut bbb);
    return bbb.into_ir();
}

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
    pc: (usize, usize),
    // Temporary storage slots for `Value`s.
    registers: Box<[Value]>,
}

impl LocalState {
    // Create and initialize a `LocalState` suitable for executing the given chunk.
    fn new(chunk: &IrChunk) -> LocalState {
        // Allocate the registers and fill them with nil values.
        let mut registers: Vec<Value> = Vec::with_capacity(chunk.num_registers);
        registers.resize_with(chunk.num_registers, Default::default);

        LocalState {
            pc: (0, 0),
            registers: registers.into_boxed_slice(),
        }
    }
}

impl Addr {
    // Use an `Addr` to retrieve a value. This can not fail, unless we created erroneous ir code.
    fn load(self, local: &LocalState) -> Value {
        match self {
            Addr::Register(index) => local.registers[index].clone(),
        }
    }

    // Use an `Addr` to store a value. This can not fail, unless we created erroneous vm code.
    fn store(self, val: Value, local: &mut LocalState) {
        match self {
            Addr::Register(index) => local.registers[index] = val,
        }
    }
}

// An IrChunk encodes a pavo computation, so it can implement the `Computation` trait.
//
// We will remove this impl at a later point: Once we implement value bindings (aka variables),
// we need an environment for computation. An IrChunk only stores the raw code, but not the
// corresponding environment (it's a function, not a closure).
impl Computation for IrChunk {
    // To perform the computation, interpret the instructions of the chunk.
    //
    // Since at this point we only implement the case of running a full pavo file, there is no
    // notion of arguments and we can fully ignore them.
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
}
