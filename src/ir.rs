//! An intermediate representation to aid in compiling pavo source code into vm code. Pavo syntax
//! trees get transformed into ir, the ir is then transformed into vm code.
//!
//! A chunk of ir (`IrChunk`) is a graph of
//! [basic blocks](https://en.wikipedia.org/wiki/Basic_block). The blocks themselves are sequences
//! of ir statements (`Stmt`). The ir statements can be thought of as a "desugared" version of pavo.

use crate::{
    syntax::{Statement, _Statement, Expression, _Expression},
    value::Value,
    vm::{VmChunk, Instruction, Addr as VmAddr},
};

/// A control flow graph of basic blocks, each consisting of a sequence of statements.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IrChunk {
    basic_blocks: Vec<Vec<Stmt>>,
}

/// The ir describes operations on values stored in particular locations. The implementation of
/// these locations is handled by the virtual machine, the ir just needs to address them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Addr {
    /// A location local to a particular execution of a computation.
    Register(usize),
}

impl Addr {
    fn reg(r: usize) -> Addr {
        Addr::Register(r)
    }
}

impl Into<VmAddr> for Addr {
    fn into(self) -> VmAddr {
        match self {
            Addr::Register(r) => VmAddr::reg(r),
        }
    }
}

/// A single statement of the ir.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Stmt {
    /// Do nothing but evaluate to the given value and store it in the given location.
    Literal(Value, Addr),
    // Return the value at the address.
    Return(Addr),
}

/// Converts an abstract syntax tree into an `IrChunk`.
pub fn ast_to_ir(ast: &Vec<Statement>) -> IrChunk {
    let mut basic_blocks = Vec::new();
    basic_blocks.push(Vec::new());

    for stmt in ast {
        match stmt.1 {
            _Statement::Expression(Expression(_, _Expression::Nil)) => {
                basic_blocks[0].push(Stmt::Literal(Value::new_nil(), Addr::reg(0)));
            }
        }
    }
    basic_blocks[0].push(Stmt::Return(Addr::reg(0)));

    IrChunk { basic_blocks }
}

/// Converts an `IrChunk` into a `VmChunk`.
// This is not the "real" implementation yet, the "real" implementation will have to properly
// traverse all basic blocks. We'll wait with that until we actually have multiple basic blocks.
pub fn ir_to_vm(ir: IrChunk) -> VmChunk {
    let mut instrs = Vec::new();

    for stmt in ir.basic_blocks[0].iter() {
        match stmt {
            Stmt::Literal(val, addr) => {
                instrs.push(Instruction::Literal(val.clone(), (*addr).into()));
            }
            Stmt::Return(addr) => {
                instrs.push(Instruction::Return((*addr).into()));
            }
        }
    }

    instrs.push(Instruction::Return(VmAddr::Register(0)));

    return VmChunk::new(instrs.into_boxed_slice(), 1);
}
