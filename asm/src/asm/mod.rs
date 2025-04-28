mod opcodes;
mod util;

use chumsky::span::Span;
use everscale_types::prelude::*;

use self::opcodes::{cp0, Context};
use crate::ast;

pub fn assemble(ast: &[ast::Stmt], span: ast::Span) -> Result<Cell, AsmError> {
    let opcodes = cp0();

    let mut context = Context::new();
    for stmt in ast {
        context.add_stmt(opcodes, stmt)?;
    }

    context
        .into_builder(span)?
        .build()
        .map_err(|e| AsmError::StoreError { inner: e, span })
}

pub fn check(ast: &[ast::Stmt], span: ast::Span) -> Vec<AsmError> {
    let opcodes = cp0();

    let mut errors = Vec::new();
    let mut context = Context::new();
    context.set_allow_invalid();
    for stmt in ast {
        if let Err(e) = context.add_stmt(opcodes, stmt) {
            errors.push(e);
        }
    }

    if let Err(e) = context.into_builder(span).and_then(|b| {
        b.build()
            .map_err(|e| AsmError::StoreError { inner: e, span })
    }) {
        errors.push(e);
    }

    errors
}

impl ast::InstrArgValue<'_> {
    fn ty(&self) -> ArgType {
        match self {
            ast::InstrArgValue::Nat(_) => ArgType::Nat,
            &ast::InstrArgValue::MethodId(_) => ArgType::MethodId,
            ast::InstrArgValue::SReg(_) => ArgType::StackRegister,
            ast::InstrArgValue::CReg(_) => ArgType::ControlRegister,
            ast::InstrArgValue::Slice(_) => ArgType::Slice,
            ast::InstrArgValue::Lib(_) => ArgType::Library,
            ast::InstrArgValue::Cell(_) => ArgType::Cell,
            ast::InstrArgValue::Block(_) => ArgType::Block,
            ast::InstrArgValue::Invalid => ArgType::Invalid,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ArgType {
    Nat,
    MethodId,
    StackRegister,
    ControlRegister,
    Slice,
    Library,
    Cell,
    Block,
    Invalid,
}

impl ArgType {
    pub fn expected_exact(self) -> ExpectedArgType {
        ExpectedArgType::Exact(self)
    }

    pub fn expected_or<T: Into<ExpectedArgType>>(self, other: T) -> ExpectedArgType {
        ExpectedArgType::OneOf(self, Box::new(other.into()))
    }
}

impl std::fmt::Display for ArgType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Nat => "number",
            Self::MethodId => "method id",
            Self::StackRegister => "stack register",
            Self::ControlRegister => "control register",
            Self::Slice => "cell slice",
            Self::Cell => "cell",
            Self::Library => "library hash",
            Self::Block => "instruction block",
            Self::Invalid => "invalid",
        })
    }
}

impl From<ArgType> for ExpectedArgType {
    #[inline]
    fn from(value: ArgType) -> Self {
        Self::Exact(value)
    }
}

#[derive(Debug)]
pub enum ExpectedArgType {
    Exact(ArgType),
    OneOf(ArgType, Box<Self>),
}

impl ExpectedArgType {
    pub fn join<T: Into<ExpectedArgType>>(mut self, other: T) -> Self {
        fn join_inner(this: &mut ExpectedArgType, other: ExpectedArgType) {
            let mut value = std::mem::replace(this, ExpectedArgType::Exact(ArgType::Invalid));
            match &mut value {
                ExpectedArgType::Exact(exact) => {
                    *this = ExpectedArgType::OneOf(*exact, Box::new(other))
                }
                ExpectedArgType::OneOf(_, rest) => {
                    join_inner(rest, other);
                    *this = value
                }
            }
        }

        join_inner(&mut self, other.into());
        self
    }
}

impl std::fmt::Display for ExpectedArgType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Exact(arg_type) => std::fmt::Display::fmt(arg_type, f),
            Self::OneOf(a, rest) => {
                std::fmt::Display::fmt(a, f)?;
                let mut rest = rest.as_ref();
                loop {
                    match rest {
                        Self::Exact(b) => return write!(f, " or {b}"),
                        Self::OneOf(b, next) => {
                            write!(f, ", {b}")?;
                            rest = next;
                        }
                    }
                }
            }
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum AsmError {
    #[error("unknown opcode: {name}")]
    UnknownOpcode { name: Box<str>, span: ast::Span },
    #[error("unaligned continuation of {bits} bits")]
    UnalignedCont { bits: u16, span: ast::Span },
    #[error("expected {expected}, got {found}")]
    ArgTypeMismatch {
        span: ast::Span,
        found: ArgType,
        expected: ExpectedArgType,
    },
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

impl AsmError {
    pub fn can_ignore(&self) -> bool {
        matches!(
            self,
            Self::ArgTypeMismatch {
                found: ArgType::Invalid,
                ..
            }
        )
    }

    pub fn span(&self) -> ast::Span {
        match self {
            Self::UnknownOpcode { span, .. }
            | Self::UnalignedCont { span, .. }
            | Self::ArgTypeMismatch { span, .. }
            | Self::InvalidRegister(span)
            | Self::TooManyArgs(span)
            | Self::NotEnoughArgs(span)
            | Self::OutOfRange(span)
            | Self::WrongUsage { span, .. }
            | Self::StoreError { span, .. } => *span,
            Self::Multiple(items) => match items.as_ref() {
                [] => ast::Span::new((), 0..0),
                [first, rest @ ..] => {
                    let mut res = first.span();
                    for item in rest {
                        let item_span = item.span();
                        res.start = std::cmp::min(res.start, item_span.start);
                        res.end = std::cmp::max(res.end, item_span.end);
                    }
                    res
                }
            },
        }
    }
}

pub trait JoinResults<T> {
    fn join_results(self) -> Result<T, AsmError>;
}

impl<T1, T2> JoinResults<(T1, T2)> for (Result<T1, AsmError>, Result<T2, AsmError>) {
    fn join_results(self) -> Result<(T1, T2), AsmError> {
        match self {
            (Ok(a1), Ok(a2)) => Ok((a1, a2)),
            (Ok(_), Err(e)) | (Err(e), Ok(_)) => Err(e),
            (Err(e1), Err(e2)) => Err(AsmError::Multiple(Box::from([e1, e2]))),
        }
    }
}

impl<T1, T2, T3> JoinResults<(T1, T2, T3)>
    for (
        Result<T1, AsmError>,
        Result<T2, AsmError>,
        Result<T3, AsmError>,
    )
{
    fn join_results(self) -> Result<(T1, T2, T3), AsmError> {
        match self {
            (Ok(a1), Ok(a2), Ok(a3)) => Ok((a1, a2, a3)),
            (Ok(_), Ok(_), Err(e)) | (Ok(_), Err(e), Ok(_)) | (Err(e), Ok(_), Ok(_)) => Err(e),
            (Ok(_), Err(e1), Err(e2)) | (Err(e1), Err(e2), Ok(_)) | (Err(e1), Ok(_), Err(e2)) => {
                Err(AsmError::Multiple(Box::from([e1, e2])))
            }
            (Err(e1), Err(e2), Err(e3)) => Err(AsmError::Multiple(Box::from([e1, e2, e3]))),
        }
    }
}
