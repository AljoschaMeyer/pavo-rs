//! A simple virtual machine and its instruction set. Pavo code gets compiled into vm code so that
//! it can be executed.
//!
//! The vm works by loading and storing pavo `Value`s in a set of "registers" (a `Box<[Value]>`)
//! local to the execution instance.

use crate::{
    value::Value,
    context::{Computation, Context, PavoResult},
};

// Holds some vm code to be executed.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VmChunk {
    // The vm code.
    code: Box<[Instruction]>,
    // The number of registers the code needs to work.
    num_registers: usize,
}

impl VmChunk {
    pub fn new(code: Box<[Instruction]>, num_registers: usize) -> VmChunk {
        VmChunk {
            code,
            num_registers,
        }
    }
}

// The local state upon which the instructions to operate. It is local to each invocation of
// `Computation::compute`.
struct LocalState {
    // Index into the `VmChunk`'s `code` field that indicates which instruction to execute next.
    // "pc" stands for "program counter".
    pc: usize,
    // Temporary storage slots for `Value`s.
    registers: Box<[Value]>,
}

impl LocalState {
    // Create and initialize a `LocalState` suitable for executing the given chunk.
    fn new(chunk: &VmChunk) -> LocalState {
        // Allocate the registers and fill them with nil values.
        let mut registers: Vec<Value> = Vec::with_capacity(chunk.num_registers);
        registers.resize_with(chunk.num_registers, Default::default);

        LocalState {
            pc: 0,
            registers: registers.into_boxed_slice(),
        }
    }
}

/// Addresses a storage slot where a computation can write `Value`s to (or from where to read them).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Addr {
    /// Address of a register in a `LocalState`.
    Register(usize),
}

impl Addr {
    pub fn reg(r: usize) -> Addr {
        Addr::Register(r)
    }

    // Use an `Addr` to retrieve a value. This can not fail, unless the compiler emitted erroneous
    // vm code.
    fn load(self, local: &LocalState) -> Value {
        match self {
            Addr::Register(index) => local.registers[index].clone(),
        }
    }

    // Use an `Addr` to store a value. This can not fail, unless the compiler emitted erroneous
    // vm code.
    fn store(self, val: Value, local: &mut LocalState) {
        match self {
            Addr::Register(index) => local.registers[index] = val,
        }
    }
}

// A single instruction of vm code.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Instruction {
    // Write the given literal `Value` to the address.
    Literal(Value, Addr),
    // Return the value at the address.
    Return(Addr),
}
use self::Instruction::*;

// A VmChunk encodes a pavo computation, so it can implement the `Computation` trait.
//
// We will remove this impl at a later point: Once we implement value bindings (aka variables),
// we need an environment for computation. A VmChunk only stores the raw code, but not the
// corresponding environment (it's a function, not a closure).
impl Computation for VmChunk {
    // To perform the computation, interpret the vm instructions of the chunk.
    //
    // Since at this point we only implement the case of running a full pavo file, there is no
    // notion of arguments and we can fully ignore them.
    fn compute<Args: IntoIterator<Item = Value>>(&self, _: Args, _: &mut Context) -> PavoResult {
        let mut state = LocalState::new(self);

        loop {
            state.pc += 1;
            match &self.code[state.pc - 1] {
                Return(addr) => return Ok(addr.load(&state)),
                Literal(val, dst) => dst.store(val.clone(), &mut state),
            }
        }
    }
}
