use std::str::FromStr;

use chumsky::text::TextExpected;
use chumsky::util::MaybeRef;
use chumsky::{prelude::*, DefaultExpected};
use everscale_types::boc::Boc;
use everscale_types::cell::{CellType, HashBytes};
use everscale_types::prelude::{Cell, CellBuilder};
use num_bigint::BigInt;
use num_traits::Num;

pub type Span = SimpleSpan<usize>;

pub fn parse(s: &'_ str) -> ParseResult<Code<'_>, ParserError> {
    parser().parse(s)
}

#[derive(Debug, Clone)]
pub struct Code<'a> {
    pub span: Span,
    pub items: Vec<Stmt<'a>>,
}

#[derive(Debug, Clone)]
pub enum Stmt<'a> {
    Instr(Instr<'a>),
    Inline(Inline<'a>),
    NewCell(#[allow(unused)] NewCell),
}

#[derive(Debug, Clone)]
pub struct Instr<'a> {
    pub span: Span,
    pub ident_span: Span,
    pub ident: &'a str,
    pub args: Vec<InstrArg<'a>>,
}

#[derive(Debug, Clone)]
pub struct Inline<'a> {
    pub span: Span,
    pub value: InstrArg<'a>,
}

#[derive(Debug, Clone)]
pub struct NewCell {
    #[allow(unused)]
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct InstrArg<'a> {
    pub span: Span,
    pub value: InstrArgValue<'a>,
}

#[derive(Debug, Clone)]
pub enum InstrArgValue<'a> {
    Nat(BigInt),
    SReg(i16),
    CReg(u8),
    Slice(Cell),
    Lib(Cell),
    Cell(Cell),
    Block(Vec<Stmt<'a>>),
    Invalid,
}

fn parser<'a>() -> impl Parser<'a, &'a str, Code<'a>, extra::Err<ParserError>> {
    stmt()
        .recover_with(skip_then_retry_until(any().ignored(), text::newline()))
        .padded()
        .repeated()
        .collect()
        .map_with(|items, e| Code {
            span: e.span(),
            items,
        })
}

fn stmt<'a>() -> impl Parser<'a, &'a str, Stmt<'a>, extra::Err<ParserError>> {
    recursive(|stmt| {
        let inline = just("@inline")
            .padded_by(comment().repeated())
            .padded()
            .ignore_then(instr_arg(stmt.clone()))
            .map_with(|value, e| {
                Stmt::Inline(Inline {
                    value,
                    span: e.span(),
                })
            });

        let jumpref = just("@newcell")
            .padded_by(comment().repeated())
            .padded()
            .map_with(|_, e| Stmt::NewCell(NewCell { span: e.span() }));

        let instr = instr(stmt).map(Stmt::Instr);

        choice((inline, jumpref, instr))
    })
}

fn instr<'a>(
    stmt: Recursive<dyn Parser<'a, &'a str, Stmt<'a>, extra::Err<ParserError>> + 'a>,
) -> impl Parser<'a, &'a str, Instr<'a>, extra::Err<ParserError>> + Clone {
    fn compute_min_span(ident_span: Span, args: &[InstrArg<'_>]) -> Span {
        let mut res = ident_span;
        for arg in args {
            res.start = std::cmp::min(res.start, arg.span.start);
            res.end = std::cmp::max(res.end, arg.span.end);
        }
        res
    }

    let comment = comment();

    let args = instr_arg(stmt)
        .separated_by(
            just(',')
                .padded_by(comment.clone().repeated())
                .padded()
                .recover_with(skip_then_retry_until(
                    any().ignored(),
                    choice((just(',').ignored(), text::newline())),
                )),
        )
        .collect::<Vec<_>>();

    instr_ident()
        .map_with(|ident, e| (ident, e.span()))
        .padded_by(comment.repeated())
        .padded()
        .then(args)
        .map(|((ident, ident_span), args)| Instr {
            span: compute_min_span(ident_span, &args),
            ident,
            ident_span,
            args,
        })
}

fn instr_arg<'a>(
    stmt: Recursive<dyn Parser<'a, &'a str, Stmt<'a>, extra::Err<ParserError>> + 'a>,
) -> impl Parser<'a, &'a str, InstrArg<'a>, extra::Err<ParserError>> + Clone {
    choice((
        nat().map(InstrArgValue::Nat),
        stack_register().map(|idx| {
            idx.map(InstrArgValue::SReg)
                .unwrap_or(InstrArgValue::Invalid)
        }),
        control_register().map(|idx| {
            idx.map(InstrArgValue::CReg)
                .unwrap_or(InstrArgValue::Invalid)
        }),
        cont_block(stmt).map(InstrArgValue::Block),
        cell_slice().map(|slice| {
            slice
                .map(InstrArgValue::Slice)
                .unwrap_or(InstrArgValue::Invalid)
        }),
        library_cell().map(|lib| {
            lib.map(InstrArgValue::Lib)
                .unwrap_or(InstrArgValue::Invalid)
        }),
        raw_cell().map(|cell| {
            cell.map(InstrArgValue::Cell)
                .unwrap_or(InstrArgValue::Invalid)
        }),
    ))
    .map_with(|value, e| InstrArg {
        value,
        span: e.span(),
    })
}

fn comment<'a>() -> impl Parser<'a, &'a str, (), extra::Err<ParserError>> + Clone {
    just("//")
        .then(any().and_is(text::newline().not()).repeated())
        .padded()
        .ignored()
}

fn instr_ident<'a>() -> impl Parser<'a, &'a str, &'a str, extra::Err<ParserError>> + Clone {
    any()
        .filter(|&c: &char| !c.is_whitespace() && c != ',' && c != '}' && c != '{')
        .repeated()
        .at_least(1)
        .to_slice()
        .validate(|ident: &str, e, emitter| {
            let invalid_char = 'char: {
                let mut chars = ident.chars().peekable();
                let Some(first) = chars.peek() else {
                    break 'char None;
                };

                if *first == '-' {
                    chars.next();
                }

                let Some(first) = chars.peek() else {
                    break 'char None;
                };

                if first.is_ascii_digit() {
                    chars.next();
                    let Some(second) = chars.next() else {
                        break 'char None;
                    };
                    if !second.is_ascii_uppercase() {
                        break 'char Some(second);
                    }
                }

                for c in chars {
                    if !(c.is_ascii_uppercase()
                        || c.is_ascii_digit()
                        || c == '#'
                        || c == '_'
                        || c == ':')
                    {
                        break 'char Some(c);
                    }
                }

                return ident;
            };

            emitter.emit(ParserError::ExpectedFound {
                span: e.span(),
                found: invalid_char,
            });

            "#INVALID#"
        })
}

fn nat<'a>() -> impl Parser<'a, &'a str, BigInt, extra::Err<ParserError>> + Clone {
    fn parse_int(mut s: &str, radix: u32, span: Span) -> Result<BigInt, ParserError> {
        if !s.is_empty() {
            s = s.trim_start_matches('0');
            if s.is_empty() {
                s = "0";
            }
        }

        match BigInt::from_str_radix(s, radix) {
            Ok(n) => Ok(n),
            Err(e) => Err(ParserError::InvalidInt { span, inner: e }),
        }
    }

    let num_slice = any()
        .filter(|&c: &char| !c.is_whitespace() && c != ',' && c != '}' && c != '{')
        .repeated()
        .at_least(1)
        .to_slice();

    let number = choice((
        just("0x")
            .ignore_then(num_slice)
            .try_map(|s, span| parse_int(s, 16, span)),
        just("0b")
            .ignore_then(num_slice)
            .try_map(|s, span| parse_int(s, 2, span)),
        text::int(10).try_map(|s, span| parse_int(s, 10, span)),
    ));

    choice((
        just('-').ignore_then(number).map(std::ops::Neg::neg),
        number,
    ))
    .then_ignore(empty().and_is(choice((
        end(),
        text::whitespace().at_least(1),
        just(',').ignored(),
    ))))
}

fn stack_register<'a>() -> impl Parser<'a, &'a str, Option<i16>, extra::Err<ParserError>> + Clone {
    let until_next_arg = any()
        .filter(|&c: &char| c != ',' && !c.is_whitespace())
        .repeated();

    let until_eof_or_paren = none_of(")\n").repeated().then(just(')').or_not());

    let idx =
        text::int::<_, extra::Err<ParserError>>(10).try_map(|s, span| match i16::from_str(s) {
            Ok(n) => Ok(n),
            Err(e) => Err(ParserError::InvalidStackRegister {
                span,
                inner: e.into(),
            }),
        });

    just('s').ignore_then(
        choice((
            just('(').ignore_then(
                just('-')
                    .ignore_then(idx)
                    .map(|idx| Some(-idx))
                    .then_ignore(just(')'))
                    .recover_with(via_parser(until_eof_or_paren.map(|_| None))),
            ),
            idx.map(Some),
        ))
        .recover_with(via_parser(until_next_arg.map(|_| None))),
    )
}

fn control_register<'a>() -> impl Parser<'a, &'a str, Option<u8>, extra::Err<ParserError>> + Clone {
    let recovery = any()
        .filter(|&c: &char| c != ',' && !c.is_whitespace())
        .repeated();

    let idx = text::int::<_, extra::Err<ParserError>>(10)
        .try_map(|s, span| match u8::from_str(s) {
            Ok(n) if (0..=5).contains(&n) || n == 7 => Ok(Some(n)),
            Ok(n) => Err(ParserError::InvalidControlRegister {
                span,
                inner: ControlRegisterError::OutOfRange(n).into(),
            }),
            Err(e) => Err(ParserError::InvalidControlRegister {
                span,
                inner: e.into(),
            }),
        })
        .recover_with(via_parser(recovery.map(|_| None)));

    just('c').ignore_then(idx)
}

fn cont_block<'a>(
    stmt: Recursive<dyn Parser<'a, &'a str, Stmt<'a>, extra::Err<ParserError>> + 'a>,
) -> impl Parser<'a, &'a str, Vec<Stmt<'a>>, extra::Err<ParserError>> + Clone {
    stmt.padded().repeated().collect().delimited_by(
        just('{'),
        just('}')
            .ignored()
            .recover_with(via_parser(end()))
            .recover_with(skip_then_retry_until(any().ignored(), end())),
    )
}

fn library_cell<'a>() -> impl Parser<'a, &'a str, Option<Cell>, extra::Err<ParserError>> + Clone {
    let content_recovery = any()
        .filter(|&c: &char| c != '}' && !c.is_whitespace())
        .repeated();

    let braces_recovery = none_of("}\n").repeated().then(just('}').or_not());

    just("@{")
        .ignore_then(
            any()
                .filter(|&c: &char| c != '}' && !c.is_whitespace())
                .repeated()
                .to_slice()
                .try_map(move |s, span| match parse_library_ref(s) {
                    Ok(lib) => Ok(Some(lib)),
                    Err(e) => Err(ParserError::InvalidLibrary {
                        span,
                        inner: e.into(),
                    }),
                })
                .recover_with(via_parser(content_recovery.map(|_| None))),
        )
        .then(
            just('}')
                .map(|_| true)
                .recover_with(via_parser(braces_recovery.map(|_| false))),
        )
        .map(|(mut t, valid)| {
            if !valid {
                t = None;
            }
            t
        })
}

fn raw_cell<'a>() -> impl Parser<'a, &'a str, Option<Cell>, extra::Err<ParserError>> + Clone {
    let content_recovery = any()
        .filter(|&c: &char| c != '}' && !c.is_whitespace())
        .repeated();

    just("te6ccg").rewind().ignore_then(
        any()
            .filter(|&c: &char| c != '}' && !c.is_whitespace())
            .repeated()
            .to_slice()
            .try_map(move |s, span| match parse_cell_boc(s) {
                Ok(cell) => Ok(Some(cell)),
                Err(e) => Err(ParserError::InvalidCell {
                    span,
                    inner: e.into(),
                }),
            })
            .recover_with(via_parser(content_recovery.map(|_| None))),
    )
}

fn cell_slice<'a>() -> impl Parser<'a, &'a str, Option<Cell>, extra::Err<ParserError>> + Clone {
    let content_recovery = any()
        .filter(|&c: &char| c != '}' && !c.is_whitespace())
        .repeated();

    let braces_recovery = none_of("}\n").repeated().then(just('}').or_not());

    let make_slice_parser =
        |prefix: &'static str, parser: fn(&'a str) -> Result<Cell, SliceError>| {
            just(prefix)
                .ignore_then(
                    any()
                        .filter(|&c: &char| c != '}' && !c.is_whitespace())
                        .repeated()
                        .to_slice()
                        .try_map(move |s, span| match (parser)(s) {
                            Ok(s) => Ok(Some(s)),
                            Err(e) => Err(ParserError::InvalidSlice {
                                span,
                                inner: e.into(),
                            }),
                        })
                        .recover_with(via_parser(content_recovery.map(|_| None))),
                )
                .then(
                    just('}')
                        .map(|_| true)
                        .recover_with(via_parser(braces_recovery.map(|_| false))),
                )
                .map(|(mut t, valid)| {
                    if !valid {
                        t = None;
                    }
                    t
                })
        };

    choice((
        make_slice_parser("x{", parse_hex_slice),
        make_slice_parser("b{", parse_bin_slice),
    ))
}

fn parse_hex_slice(s: &str) -> Result<Cell, SliceError> {
    fn hex_char(c: u8) -> Result<u8, SliceError> {
        match c {
            b'A'..=b'F' => Ok(c - b'A' + 10),
            b'a'..=b'f' => Ok(c - b'a' + 10),
            b'0'..=b'9' => Ok(c - b'0'),
            _ => Err(SliceError::InvalidHex(c as char)),
        }
    }

    if !s.is_ascii() {
        return Err(SliceError::NonAscii);
    }

    let s = s.as_bytes();
    let (mut s, with_tag) = match s.strip_suffix(b"_") {
        Some(s) => (s, true),
        None => (s, false),
    };

    let mut half_byte = None;
    if s.len() % 2 != 0 {
        if let Some((last, prefix)) = s.split_last() {
            half_byte = Some(hex_char(*last)?);
            s = prefix;
        }
    }

    if s.len() > 128 * 2 {
        return Err(SliceError::TooLong);
    }

    let mut builder = CellBuilder::new();

    let mut bytes = hex::decode(s)?;

    let mut bits = bytes.len() as u16 * 8;
    if let Some(half_byte) = half_byte {
        bits += 4;
        bytes.push(half_byte << 4);
    }

    if with_tag {
        bits = bytes.len() as u16 * 8;
        for byte in bytes.iter().rev() {
            if *byte == 0 {
                bits -= 8;
            } else {
                bits -= 1 + byte.trailing_zeros() as u16;
                break;
            }
        }
    }

    builder.store_raw(&bytes, bits)?;
    builder.build().map_err(SliceError::CellError)
}

fn parse_bin_slice(s: &str) -> Result<Cell, SliceError> {
    use everscale_types::cell::MAX_BIT_LEN;

    let mut bits = 0;
    let mut bytes = [0; 128];

    for char in s.chars() {
        let value = match char {
            '0' => 0u8,
            '1' => 1,
            c => return Err(SliceError::InvalidBin(c)),
        };
        bytes[bits / 8] |= value << (7 - bits % 8);

        bits += 1;
        if bits > MAX_BIT_LEN as usize {
            return Err(SliceError::TooLong);
        }
    }

    let mut builder = CellBuilder::new();
    builder.store_raw(&bytes, bits as _)?;
    builder.build().map_err(SliceError::CellError)
}

fn parse_cell_boc(s: &str) -> Result<Cell, CellError> {
    Boc::decode_base64(s).map_err(Into::into)
}

fn parse_library_ref(s: &str) -> Result<Cell, LibraryError> {
    let hash = s.parse::<HashBytes>()?;
    let mut b = CellBuilder::new();
    b.set_exotic(true);
    b.store_u8(CellType::LibraryReference.to_byte())?;
    b.store_u256(&hash)?;
    b.build().map_err(LibraryError::CellError)
}

#[derive(thiserror::Error, Debug)]
pub enum ParserError {
    #[error("unexpected character found: {found:?}")]
    ExpectedFound { span: Span, found: Option<char> },
    #[error("invalid int: {inner}")]
    InvalidInt {
        span: Span,
        inner: num_bigint::ParseBigIntError,
    },
    #[error("invalid stack register: {inner}")]
    InvalidStackRegister { span: Span, inner: anyhow::Error },
    #[error("invalid control register: {inner}")]
    InvalidControlRegister { span: Span, inner: anyhow::Error },
    #[error("invalid slice: {inner}")]
    InvalidSlice { span: Span, inner: anyhow::Error },
    #[error("invalid cell: {inner}")]
    InvalidCell { span: Span, inner: anyhow::Error },
    #[error("invalid library cell: {inner}")]
    InvalidLibrary { span: Span, inner: anyhow::Error },
    #[error("unknown error")]
    UnknownError,
}

impl ParserError {
    pub fn span(&self) -> Option<Span> {
        match self {
            Self::ExpectedFound { span, .. }
            | Self::InvalidInt { span, .. }
            | Self::InvalidStackRegister { span, .. }
            | Self::InvalidControlRegister { span, .. }
            | Self::InvalidSlice { span, .. }
            | Self::InvalidCell { span, .. }
            | Self::InvalidLibrary { span, .. } => Some(*span),
            Self::UnknownError => None,
        }
    }
}

#[derive(thiserror::Error, Debug)]
enum ControlRegisterError {
    #[error("control register `c{0}` is out of range")]
    OutOfRange(u8),
}

#[derive(thiserror::Error, Debug)]
enum SliceError {
    #[error("non-ascii characters in bitstring")]
    NonAscii,
    #[error("unexpected char `{0}` in hex bitstring")]
    InvalidHex(char),
    #[error("invalid hex bitstring: {0}")]
    InvalidHexFull(#[from] hex::FromHexError),
    #[error("unexpected char `{0}` in binary bitstring")]
    InvalidBin(char),
    #[error("bitstring is too long")]
    TooLong,
    #[error("cell build error: {0}")]
    CellError(#[from] everscale_types::error::Error),
}

#[derive(thiserror::Error, Debug)]
#[error("invalid cell BOC: {0}")]
struct CellError(#[from] everscale_types::boc::de::Error);

#[derive(thiserror::Error, Debug)]
enum LibraryError {
    #[error("invalid hash: {0}")]
    InvalidHexFull(#[from] everscale_types::error::ParseHashBytesError),
    #[error("cell build error: {0}")]
    CellError(#[from] everscale_types::error::Error),
}

impl<'a> chumsky::error::LabelError<'a, &'a str, MaybeRef<'a, char>> for ParserError {
    fn expected_found<Iter: IntoIterator<Item = MaybeRef<'a, char>>>(
        _: Iter,
        found: Option<MaybeRef<'a, char>>,
        span: Span,
    ) -> Self {
        Self::ExpectedFound {
            span,
            found: found.as_deref().copied(),
        }
    }
}

impl<'a> chumsky::error::LabelError<'a, &'a str, TextExpected<'a, &'a str>> for ParserError {
    fn expected_found<Iter: IntoIterator<Item = TextExpected<'a, &'a str>>>(
        _: Iter,
        found: Option<MaybeRef<'a, char>>,
        span: Span,
    ) -> Self {
        Self::ExpectedFound {
            span,
            found: found.as_deref().copied(),
        }
    }
}

impl<'a> chumsky::error::LabelError<'a, &'a str, DefaultExpected<'a, char>> for ParserError {
    fn expected_found<Iter: IntoIterator<Item = DefaultExpected<'a, char>>>(
        _: Iter,
        found: Option<MaybeRef<'a, char>>,
        span: Span,
    ) -> Self {
        Self::ExpectedFound {
            span,
            found: found.as_deref().copied(),
        }
    }
}

impl<'a> chumsky::error::Error<'a, &'a str> for ParserError {
    fn merge(self, _: Self) -> Self {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_asm() {
        assert!(parse("").unwrap().items.is_empty());
    }

    #[test]
    fn simple_asm() {
        const CODE: &str = r#"
        PUSHCONT {
            PUSHREF x{afff_}
            PUSH s(-1)
            OVER
            LESSINT 2
            PUSHCONT {
                2DROP
                PUSHINT 1
            }
            IFJMP
            OVER
            DEC
            SWAP
            DUP
            EXECUTE
            MUL
        }
        DUP
        JMPX
        "#;

        let (output, errors) = parse(CODE).into_output_errors();
        println!("OUTPUT: {:#?}", output);
        println!("ERRORS: {:#?}", errors);

        assert!(output.is_some());
        assert!(errors.is_empty());
    }

    #[test]
    fn example_asm() {
        const CODE: &str = include_str!("tests/example.tvm");

        let (output, errors) = parse(CODE).into_output_errors();
        println!("OUTPUT: {:#?}", output);
        println!("ERRORS: {:#?}", errors);

        assert!(output.is_some());
        assert!(errors.is_empty());
    }

    #[test]
    fn complex_asm() {
        const CODE: &str = include_str!("tests/walletv3.tvm");

        let (output, errors) = parse(CODE).into_output_errors();
        println!("OUTPUT: {:#?}", output);
        println!("ERRORS: {:#?}", errors);

        assert!(output.is_some());
        assert!(errors.is_empty());
    }

    #[test]
    fn strange_opcodes() {
        let (output, errors) = parse(
            r#"
            NOP
            2DROP
            OVER
            LESSINT 2
            "#,
        )
        .into_output_errors();
        println!("OUTPUT: {:#?}", output);
        println!("ERRORS: {:#?}", errors);

        assert!(output.is_some());
        assert!(errors.is_empty());
    }

    #[test]
    fn library_cells() {
        let (output, errors) = parse(
            r#"
            PUSHREF @{aabbaaccaabbaaccaabbaaccaabbaaccaabbaaccaabbaaccaabbaaccaabbaacc}
            "#,
        )
        .into_output_errors();
        println!("OUTPUT: {:#?}", output);
        println!("ERRORS: {:#?}", errors);

        assert!(output.is_some());
        assert!(errors.is_empty());
    }
}
