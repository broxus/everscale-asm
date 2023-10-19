mod opcodes;
mod util;

use everscale_types::prelude::*;

use self::opcodes::{cp0, Context};
use crate::ast;

pub fn assemble(ast: &[ast::Instr]) -> Result<Cell, AsmError> {
    let opcodes = cp0();

    let mut context = Context::new();
    for instr in ast {
        context.add_instr(opcodes, instr)?;
    }

    context
        .into_builder()?
        .build()
        .map_err(AsmError::StoreError)
}

#[derive(thiserror::Error, Debug)]
pub enum AsmError {
    #[error("unknown opcode: {0}")]
    UnknownOpcode(Box<str>),
    #[error("unexpected arg")]
    UnexpectedArg,
    #[error("invalid register")]
    InvalidRegister,
    #[error("too many args")]
    TooManyArgs,
    #[error("not enough args")]
    NotEnoughArgs,
    #[error("out of range")]
    OutOfRange,
    #[error("invalid usage: {0}")]
    WrongUsage(&'static str),
    #[error("store error: {0}")]
    StoreError(#[from] everscale_types::error::Error),
    #[error("multiple: {0:?}")]
    Multiple(Box<[AsmError]>),
}
