use either::Either;
use everscale_types::prelude::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::asm::AsmError;
use crate::ast;

pub trait ParseArgs {
    fn parse_args<'a, T: FromInstrArgs<'a>>(&'a self) -> Result<T, AsmError>;
}

impl ParseArgs for ast::Instr<'_> {
    #[inline]
    fn parse_args<'a, T: FromInstrArgs<'a>>(&'a self) -> Result<T, AsmError> {
        T::from_instr_args(self.ident_span, &self.args)
    }
}

pub trait FromInstrArgs<'a>: Sized {
    fn from_instr_args(
        instr_span: ast::Span,
        args: &'a [ast::InstrArg<'_>],
    ) -> Result<Self, AsmError>;
}

impl<'a, T: FromInstrArg<'a>> FromInstrArgs<'a> for T {
    fn from_instr_args(
        instr_span: ast::Span,
        args: &'a [ast::InstrArg<'_>],
    ) -> Result<Self, AsmError> {
        let (s,) = <_>::from_instr_args(instr_span, args)?;
        Ok(s)
    }
}

impl FromInstrArgs<'_> for () {
    fn from_instr_args(_: ast::Span, args: &[ast::InstrArg<'_>]) -> Result<Self, AsmError> {
        match args {
            [] => Ok(()),
            [first, rest @ ..] => Err(AsmError::TooManyArgs(compute_args_span(first, rest))),
        }
    }
}

impl<'a, T: FromInstrArg<'a>> FromInstrArgs<'a> for (T,) {
    fn from_instr_args(
        instr_span: ast::Span,
        args: &'a [ast::InstrArg<'_>],
    ) -> Result<Self, AsmError> {
        match args {
            [a] => Ok((T::from_instr_arg(a)?,)),
            [_, first, rest @ ..] => Err(AsmError::TooManyArgs(compute_args_span(first, rest))),
            _ => Err(AsmError::NotEnoughArgs(instr_span)),
        }
    }
}

impl<'a, T1, T2> FromInstrArgs<'a> for (T1, T2)
where
    T1: FromInstrArg<'a>,
    T2: FromInstrArg<'a>,
{
    fn from_instr_args(
        instr_span: ast::Span,
        args: &'a [ast::InstrArg<'_>],
    ) -> Result<Self, AsmError> {
        match args {
            [a1, a2] => Ok((T1::from_instr_arg(a1)?, T2::from_instr_arg(a2)?)),
            [_, _, first, rest @ ..] => Err(AsmError::TooManyArgs(compute_args_span(first, rest))),
            _ => Err(AsmError::NotEnoughArgs(instr_span)),
        }
    }
}

impl<'a, T1, T2, T3> FromInstrArgs<'a> for (T1, T2, T3)
where
    T1: FromInstrArg<'a>,
    T2: FromInstrArg<'a>,
    T3: FromInstrArg<'a>,
{
    fn from_instr_args(
        instr_span: ast::Span,
        args: &'a [ast::InstrArg<'_>],
    ) -> Result<Self, AsmError> {
        match args {
            [a1, a2, a3] => Ok((
                T1::from_instr_arg(a1)?,
                T2::from_instr_arg(a2)?,
                T3::from_instr_arg(a3)?,
            )),
            [_, _, _, first, rest @ ..] => {
                Err(AsmError::TooManyArgs(compute_args_span(first, rest)))
            }
            _ => Err(AsmError::NotEnoughArgs(instr_span)),
        }
    }
}

pub trait FromInstrArg<'a>: Sized {
    fn from_instr_arg(arg: &'a ast::InstrArg<'_>) -> Result<Self, AsmError>;
}

impl<'a, T1, T2> FromInstrArg<'a> for Either<T1, T2>
where
    T1: FromInstrArg<'a>,
    T2: FromInstrArg<'a>,
{
    fn from_instr_arg(arg: &'a ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match T1::from_instr_arg(arg) {
            Ok(v) => Ok(Self::Left(v)),
            Err(e) => match T2::from_instr_arg(arg) {
                Ok(v) => Ok(Self::Right(v)),
                Err(_) => Err(e),
            },
        }
    }
}

pub struct WithSpan<T>(pub T, pub ast::Span);

impl<'a, T> FromInstrArg<'a> for WithSpan<T>
where
    T: FromInstrArg<'a>,
{
    fn from_instr_arg(arg: &'a ast::InstrArg<'_>) -> Result<Self, AsmError> {
        let span = arg.span;
        Ok(Self(T::from_instr_arg(arg)?, span))
    }
}

pub struct Nat<'a>(pub &'a BigInt);

impl<'a> FromInstrArg<'a> for Nat<'a> {
    fn from_instr_arg(arg: &'a ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => Ok(Self(n)),
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

pub struct NatU2(pub u8);

impl FromInstrArg<'_> for NatU2 {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u8() {
                    if n <= 0b11 {
                        return Ok(Self(n));
                    }
                }
                Err(AsmError::OutOfRange(arg.span))
            }
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

pub struct NatU4(pub u8);

impl FromInstrArg<'_> for NatU4 {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u8() {
                    if n <= 0xf {
                        return Ok(Self(n));
                    }
                }
                Err(AsmError::OutOfRange(arg.span))
            }
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

pub struct NatU5(pub u8);

impl FromInstrArg<'_> for NatU5 {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u8() {
                    if n <= 0b11111 {
                        return Ok(Self(n));
                    }
                }
                Err(AsmError::OutOfRange(arg.span))
            }
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

pub struct NatU8(pub u8);

impl FromInstrArg<'_> for NatU8 {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => match n.to_u8() {
                Some(n) => Ok(Self(n)),
                None => Err(AsmError::OutOfRange(arg.span)),
            },
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

pub struct NatU8minus1(pub u8);

impl FromInstrArg<'_> for NatU8minus1 {
    fn from_instr_arg(arg: &'_ ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u16() {
                    if (1..=256).contains(&n) {
                        return Ok(Self((n - 1) as u8));
                    }
                }
                Err(AsmError::OutOfRange(arg.span))
            }
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

pub struct SReg(pub u8);

impl FromInstrArg<'_> for SReg {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::SReg(n) => FullSReg(*n, arg.span).try_into(),
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

pub struct FullSReg(pub i16, pub ast::Span);

impl FromInstrArg<'_> for FullSReg {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::SReg(n) => Ok(Self(*n, arg.span)),
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

impl TryInto<SReg> for FullSReg {
    type Error = AsmError;

    fn try_into(self) -> Result<SReg, Self::Error> {
        if (0x0..=0xf).contains(&self.0) {
            Ok(SReg(self.0 as u8))
        } else {
            Err(AsmError::InvalidRegister(self.1))
        }
    }
}

pub struct CReg(pub u8);

impl FromInstrArg<'_> for CReg {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::CReg(n) => Ok(Self(*n)),
            _ => Err(AsmError::UnexpectedArg(arg.span)),
        }
    }
}

pub struct SliceOrCont<'a>(pub Either<Cell, (&'a [ast::Instr<'a>], ast::Span)>);

impl<'a> FromInstrArg<'a> for SliceOrCont<'a> {
    fn from_instr_arg(arg: &'a ast::InstrArg<'_>) -> Result<Self, AsmError> {
        Ok(Self(match &arg.value {
            ast::InstrArgValue::Slice(cell) => Either::Left(cell.clone()),
            ast::InstrArgValue::Block(items) => Either::Right((items.as_slice(), arg.span)),
            _ => return Err(AsmError::UnexpectedArg(arg.span)),
        }))
    }
}

fn compute_args_span(first: &ast::InstrArg<'_>, rest: &[ast::InstrArg<'_>]) -> ast::Span {
    let mut res = first.span;
    for arg in rest {
        res.start = std::cmp::min(res.start, arg.span.start);
        res.end = std::cmp::max(res.end, arg.span.end);
    }
    res
}
