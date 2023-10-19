mod opcodes;
mod util;

use everscale_types::prelude::*;

use self::opcodes::{cp0, Context};
use crate::ast;

pub fn assemble(ast: &[ast::Instr], span: ast::Span) -> Result<Cell, AsmError> {
    let opcodes = cp0();

    let mut context = Context::new();
    for instr in ast {
        context.add_instr(opcodes, instr)?;
    }

    context
        .into_builder(span)?
        .build()
        .map_err(|e| AsmError::StoreError { inner: e, span })
}

#[derive(thiserror::Error, Debug)]
pub enum AsmError {
    #[error("unknown opcode: {name}")]
    UnknownOpcode { name: Box<str>, span: ast::Span },
    #[error("unexpected arg")]
    UnexpectedArg(ast::Span),
    #[error("invalid register")]
    InvalidRegister(ast::Span),
    #[error("too many args")]
    TooManyArgs(ast::Span),
    #[error("not enough args")]
    NotEnoughArgs(ast::Span),
    #[error("out of range")]
    OutOfRange(ast::Span),
    #[error("invalid usage: {details}")]
    WrongUsage {
        details: &'static str,
        span: ast::Span,
    },
    #[error("store error: {inner}")]
    StoreError {
        inner: everscale_types::error::Error,
        span: ast::Span,
    },
    #[error("multiple: {0:?}")]
    Multiple(Box<[AsmError]>),
}
