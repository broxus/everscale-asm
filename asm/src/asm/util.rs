use either::Either;
use everscale_types::prelude::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use super::{ArgType, JoinResults, Scope};
use crate::asm::AsmError;
use crate::ast;

pub trait ParseArgs<'s> {
    fn parse_args<'i: 'c, 'c, T: FromInstrArgs<'c, 's>>(
        &'i self,
        scope: &'c Scope<'_, 's>,
    ) -> Result<T, AsmError>;
}

impl<'s> ParseArgs<'s> for ast::Instr<'s> {
    #[inline]
    fn parse_args<'i: 'c, 'c, T: FromInstrArgs<'c, 's>>(
        &'i self,
        scope: &'c Scope<'_, 's>,
    ) -> Result<T, AsmError> {
        T::from_instr_args(self.ident_span, &self.args, scope)
    }
}

impl<'s> ParseArgs<'s> for ast::Inline<'s> {
    #[inline]
    fn parse_args<'i: 'c, 'c, T: FromInstrArgs<'c, 's>>(
        &'i self,
        scope: &'c Scope<'_, 's>,
    ) -> Result<T, AsmError> {
        T::from_instr_args(self.span, std::slice::from_ref(&self.value), scope)
    }
}

pub trait FromInstrArgs<'c, 's>: Sized {
    fn from_instr_args<'i: 'c>(
        instr_span: ast::Span,
        args: &'i [ast::InstrArg<'s>],
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError>;
}

impl<'c, 's, T: FromInstrArg<'c, 's>> FromInstrArgs<'c, 's> for T {
    fn from_instr_args<'i: 'c>(
        instr_span: ast::Span,
        args: &'i [ast::InstrArg<'s>],
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let (s,) = <_>::from_instr_args(instr_span, args, scope)?;
        Ok(s)
    }
}

impl<'c, 's> FromInstrArgs<'c, 's> for () {
    fn from_instr_args<'i: 'c>(
        _: ast::Span,
        args: &'i [ast::InstrArg<'s>],
        _: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        match args {
            [] => Ok(()),
            [first, rest @ ..] => Err(AsmError::TooManyArgs(compute_args_span(first, rest))),
        }
    }
}

impl<'c, 's, T: FromInstrArg<'c, 's>> FromInstrArgs<'c, 's> for (T,) {
    fn from_instr_args<'i: 'c>(
        instr_span: ast::Span,
        args: &'i [ast::InstrArg<'s>],
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        match args {
            [a] => Ok((T::from_instr_arg(a, scope)?,)),
            [_, first, rest @ ..] => Err(AsmError::TooManyArgs(compute_args_span(first, rest))),
            _ => Err(AsmError::NotEnoughArgs(instr_span)),
        }
    }
}

impl<'c, 's, T1, T2> FromInstrArgs<'c, 's> for (T1, T2)
where
    T1: FromInstrArg<'c, 's>,
    T2: FromInstrArg<'c, 's>,
{
    fn from_instr_args<'i: 'c>(
        instr_span: ast::Span,
        args: &'i [ast::InstrArg<'s>],
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        match args {
            [a1, a2] => {
                (T1::from_instr_arg(a1, scope), T2::from_instr_arg(a2, scope)).join_results()
            }
            [_, _, first, rest @ ..] => Err(AsmError::TooManyArgs(compute_args_span(first, rest))),
            _ => Err(AsmError::NotEnoughArgs(instr_span)),
        }
    }
}

impl<'c, 's, T1, T2, T3> FromInstrArgs<'c, 's> for (T1, T2, T3)
where
    T1: FromInstrArg<'c, 's>,
    T2: FromInstrArg<'c, 's>,
    T3: FromInstrArg<'c, 's>,
{
    fn from_instr_args<'i: 'c>(
        instr_span: ast::Span,
        args: &'i [ast::InstrArg<'s>],
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        match args {
            [a1, a2, a3] => (
                T1::from_instr_arg(a1, scope),
                T2::from_instr_arg(a2, scope),
                T3::from_instr_arg(a3, scope),
            )
                .join_results(),
            [_, _, _, first, rest @ ..] => {
                Err(AsmError::TooManyArgs(compute_args_span(first, rest)))
            }
            _ => Err(AsmError::NotEnoughArgs(instr_span)),
        }
    }
}

pub trait FromInstrArg<'c, 's>: Sized {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError>;
}

impl<'c, 's> FromInstrArg<'c, 's> for &'c ast::InstrArg<'s> {
    #[inline]
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        scope.resolve_arg_once(arg)
    }
}

impl<'c, 's, T1, T2> FromInstrArg<'c, 's> for Either<T1, T2>
where
    T1: FromInstrArg<'c, 's>,
    T2: FromInstrArg<'c, 's>,
{
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        match T1::from_instr_arg(arg, scope) {
            Ok(v) => Ok(Either::Left(v)),
            Err(AsmError::ArgTypeMismatch {
                span,
                expected: expected_a,
                found,
            }) => match T2::from_instr_arg(arg, scope) {
                Ok(v) => Ok(Either::Right(v)),
                Err(AsmError::ArgTypeMismatch {
                    expected: expected_b,
                    ..
                }) => Err(AsmError::ArgTypeMismatch {
                    span,
                    expected: expected_a.join(expected_b),
                    found,
                }),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }
}

pub struct WithSpan<T>(pub T, pub ast::Span);

impl<'c, 's, T> FromInstrArg<'c, 's> for WithSpan<T>
where
    T: FromInstrArg<'c, 's>,
{
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let span = arg.span;
        Ok(WithSpan(T::from_instr_arg(arg, scope)?, span))
    }
}

pub struct Nat<'a>(pub &'a BigInt);

impl<'c, 's> FromInstrArg<'c, 's> for Nat<'c> {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        match &arg.value {
            ast::InstrArgValue::Nat(n) => Ok(Self(n)),
            ast::InstrArgValue::MethodId(m) => Ok(Self(&m.value.computed)),
            _ => Err(AsmError::ArgTypeMismatch {
                span: arg.span,
                expected: ArgType::Nat.expected_exact(),
                found: arg.value.ty(),
            }),
        }
    }
}

macro_rules! nat_u8 {
    ($($bits:literal => $ident:ident),*$(,)?) => {$(
        pub struct $ident(pub u8);

        impl<'c, 's> FromInstrArg<'c, 's> for $ident {
            fn from_instr_arg<'i: 'c>(
                arg: &'i ast::InstrArg<'s>,
                scope: &'c Scope<'_, 's>,
            ) -> Result<Self, AsmError> {
                let arg = scope.resolve_arg_once(arg)?;
                match &arg.value {
                    ast::InstrArgValue::Nat(n) => {
                        if let Some(n) = n.to_u8() {
                            if n <= const { ((1u16 << $bits) - 1) as u8 } {
                                return Ok(Self(n));
                            }
                        }
                        Err(AsmError::OutOfRange(arg.span))
                    }
                    _ => Err(AsmError::ArgTypeMismatch {
                        span: arg.span,
                        expected: ArgType::Nat.expected_exact(),
                        found: arg.value.ty(),
                    }),
                }
            }
        }
    )*};
}

nat_u8! {
    2 => NatU2,
    4 => NatU4,
    5 => NatU5,
    8 => NatU8,
}

pub struct NatU4minus<const N: u8>(pub u8);

impl<'c, 's, const N: u8> FromInstrArg<'c, 's> for NatU4minus<N> {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u8() {
                    if (N..=15 + N).contains(&n) {
                        return Ok(Self(n - N));
                    }
                }
                Err(AsmError::OutOfRange(arg.span))
            }
            _ => Err(AsmError::ArgTypeMismatch {
                span: arg.span,
                expected: ArgType::Nat.expected_exact(),
                found: arg.value.ty(),
            }),
        }
    }
}

pub struct NatU8minus<const N: u16>(pub u8);

impl<'c, 's, const N: u16> FromInstrArg<'c, 's> for NatU8minus<N> {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u16() {
                    if (N..=255 + N).contains(&n) {
                        return Ok(Self((n - N) as u8));
                    }
                }
                Err(AsmError::OutOfRange(arg.span))
            }
            _ => Err(AsmError::ArgTypeMismatch {
                span: arg.span,
                expected: ArgType::Nat.expected_exact(),
                found: arg.value.ty(),
            }),
        }
    }
}

pub struct NatI8(pub i8);

impl<'c, 's> FromInstrArg<'c, 's> for NatI8 {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        match &arg.value {
            ast::InstrArgValue::Nat(n) => match n.to_i8() {
                Some(n) => Ok(Self(n)),
                None => Err(AsmError::OutOfRange(arg.span)),
            },
            _ => Err(AsmError::ArgTypeMismatch {
                span: arg.span,
                expected: ArgType::Nat.expected_exact(),
                found: arg.value.ty(),
            }),
        }
    }
}

macro_rules! nat_u16 {
    ($($bits:literal => $ident:ident),*$(,)?) => {$(
        pub struct $ident(pub u16);

        impl<'c, 's> FromInstrArg<'c, 's> for $ident {
            fn from_instr_arg<'i: 'c>(
                arg: &'i ast::InstrArg<'s>,
                scope: &'c Scope<'_, 's>,
            ) -> Result<Self, AsmError> {
                let arg = scope.resolve_arg_once(arg)?;
                match &arg.value {
                    ast::InstrArgValue::Nat(n) => {
                        if let Some(n) = n.to_u16() {
                            if n <= const { ((1u32 << $bits) - 1) as u16 } {
                                return Ok(Self(n));
                            }
                        }
                        Err(AsmError::OutOfRange(arg.span))
                    }
                    _ => Err(AsmError::ArgTypeMismatch {
                        span: arg.span,
                        expected: ArgType::Nat.expected_exact(),
                        found: arg.value.ty(),
                    }),
                }
            }
        }
    )*};
}

nat_u16! {
    10 => NatU10,
    11 => NatU11,
    12 => NatU12,
}

pub struct SReg(pub u8);

impl<'c, 's> FromInstrArg<'c, 's> for SReg {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        match &arg.value {
            ast::InstrArgValue::SReg(n) => FullSReg(*n, arg.span).try_into(),
            _ => Err(AsmError::ArgTypeMismatch {
                span: arg.span,
                expected: ArgType::StackRegister.expected_exact(),
                found: arg.value.ty(),
            }),
        }
    }
}

pub struct FullSReg(pub i16, pub ast::Span);

impl<'c, 's> FromInstrArg<'c, 's> for FullSReg {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        match &arg.value {
            ast::InstrArgValue::SReg(n) => Ok(Self(*n, arg.span)),
            _ => Err(AsmError::ArgTypeMismatch {
                span: arg.span,
                expected: ArgType::StackRegister.expected_exact(),
                found: arg.value.ty(),
            }),
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

impl<'c, 's> FromInstrArg<'c, 's> for CReg {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        match &arg.value {
            ast::InstrArgValue::CReg(n) => Ok(Self(*n)),
            _ => Err(AsmError::ArgTypeMismatch {
                span: arg.span,
                expected: ArgType::ControlRegister.expected_exact(),
                found: arg.value.ty(),
            }),
        }
    }
}

pub struct Slice(pub Cell);

impl<'c, 's> FromInstrArg<'c, 's> for Slice {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        match &arg.value {
            ast::InstrArgValue::Slice(cell) | ast::InstrArgValue::Cell(cell) => {
                Ok(Self(cell.clone()))
            }
            _ => Err(AsmError::ArgTypeMismatch {
                span: arg.span,
                expected: ArgType::Slice
                    .expected_or(ArgType::Cell)
                    .join(ArgType::Block),
                found: arg.value.ty(),
            }),
        }
    }
}

pub struct SliceOrCont<'c, 's>(pub Either<Cell, (&'c [ast::Stmt<'s>], ast::Span)>);

impl<'c, 's> FromInstrArg<'c, 's> for SliceOrCont<'c, 's> {
    fn from_instr_arg<'i: 'c>(
        arg: &'i ast::InstrArg<'s>,
        scope: &'c Scope<'_, 's>,
    ) -> Result<Self, AsmError> {
        let arg = scope.resolve_arg_once(arg)?;
        Ok(Self(match &arg.value {
            ast::InstrArgValue::Slice(cell)
            | ast::InstrArgValue::Lib(cell)
            | ast::InstrArgValue::Cell(cell) => Either::Left(cell.clone()),
            ast::InstrArgValue::Block(items) => Either::Right((items.as_slice(), arg.span)),
            _ => {
                return Err(AsmError::ArgTypeMismatch {
                    span: arg.span,
                    expected: ArgType::Slice.expected_or(ArgType::Block),
                    found: arg.value.ty(),
                })
            }
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
