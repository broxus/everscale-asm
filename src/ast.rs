use everscale_types::cell::MAX_BIT_LEN;
use everscale_types::prelude::*;
use num_bigint::BigInt;
use num_traits::Num;
use pest::iterators::Pair;
use pest::Parser;

pub fn parse(s: &'_ str) -> Result<Vec<Instr<'_>>, ParserError> {
    let pairs = Grammar::parse(Rule::code, s)
        .map_err(|e| ParserError::InvalidInput(Box::new(e)))?
        .next()
        .unwrap()
        .into_inner();

    let mut res = Vec::with_capacity(pairs.len());

    for pair in pairs {
        match pair.as_rule() {
            Rule::instr => res.push(Instr::parse(pair)?),
            Rule::EOI => break,
            r => panic!("Unexpected rule: {r:?}"),
        }
    }

    Ok(res)
}

#[derive(Debug, Clone)]
pub struct Instr<'a> {
    pub ident_span: Span,
    pub ident: &'a str,
    pub args: Vec<InstrArg<'a>>,
}

impl<'a> Instr<'a> {
    fn parse(pair: Pair<'a, Rule>) -> Result<Self, ParserError> {
        let mut pairs = pair.into_inner();

        let (ident, ident_span) = match pairs.next() {
            Some(pair) => {
                assert_eq!(pair.as_rule(), Rule::instr_ident);
                (pair.as_str(), pair.as_span().into())
            }
            None => panic!("Invalid rules"),
        };

        let mut args = Vec::with_capacity(pairs.len());
        for pair in pairs {
            args.push(InstrArg::parse(pair)?);
        }

        Ok(Self {
            ident_span,
            ident,
            args,
        })
    }
}

#[derive(Debug, Clone)]
pub struct InstrArg<'a> {
    pub span: Span,
    pub value: InstrArgValue<'a>,
}

impl<'a> InstrArg<'a> {
    fn parse(pair: Pair<'a, Rule>) -> Result<Self, ParserError> {
        Ok(InstrArg {
            span: pair.as_span().into(),
            value: InstrArgValue::parse(pair)?,
        })
    }
}

#[derive(Debug, Clone)]
pub enum InstrArgValue<'a> {
    Nat(BigInt),
    SReg(i16),
    CReg(u8),
    Slice(Cell),
    Block(Vec<Instr<'a>>),
}

impl<'a> InstrArgValue<'a> {
    fn parse(pair: Pair<'a, Rule>) -> Result<Self, ParserError> {
        match pair.as_rule() {
            Rule::nat => parse_nat(pair.as_str()).map(Self::Nat),
            Rule::s_reg => {
                let pair = pair.into_inner().next().unwrap();
                assert_eq!(pair.as_rule(), Rule::s_reg_id);
                parse_s_reg(pair.as_str()).map(Self::SReg)
            }
            Rule::c_reg => {
                let pair = pair.into_inner().next().unwrap();
                assert_eq!(pair.as_rule(), Rule::c_reg_id);
                parse_c_reg(pair.as_str()).map(Self::CReg)
            }
            Rule::block => {
                let pairs = pair.into_inner();
                let mut block = Vec::with_capacity(pairs.len());
                for pair in pairs {
                    block.push(Instr::parse(pair)?);
                }
                Ok(Self::Block(block))
            }
            Rule::slice => {
                let pair = pair.into_inner().next().unwrap();
                match pair.as_rule() {
                    Rule::bin_slice => parse_bin_slice(pair.as_str()).map(Self::Slice),
                    Rule::hex_slice => parse_hex_slice(pair.as_str()).map(Self::Slice),
                    r => panic!("Unexpected rule: {r:?}"),
                }
            }
            r => panic!("Unexpected rule: {r:?}"),
        }
    }
}

fn parse_nat(mut s: &str) -> Result<BigInt, ParserError> {
    let negate = match s.strip_prefix('-') {
        Some(rest) => {
            s = rest;
            true
        }
        None => false,
    };

    let radix = if let Some(rest) = s.strip_prefix("0x") {
        s = rest;
        16
    } else if let Some(rest) = s.strip_prefix("0b") {
        s = rest;
        2
    } else {
        10
    };

    let number = BigInt::from_str_radix(s, radix)?;
    Ok(if negate { -number } else { number })
}

fn parse_s_reg(s: &str) -> Result<i16, ParserError> {
    'err: {
        if let Some(rest) = s.strip_prefix("(-") {
            let Some(rest) = rest.strip_suffix(')') else {
                break 'err;
            };

            if let Ok(n) = rest.parse::<i16>() {
                return Ok(-n);
            }
        } else if let Ok(n) = s.parse::<i16>() {
            return Ok(n);
        }
    }

    Err(ParserError::InvalidStackRegister(Box::from(s)))
}

fn parse_c_reg(s: &str) -> Result<u8, ParserError> {
    if let Ok(n) = s.parse::<u8>() {
        if (0..=5).contains(&n) || n == 7 {
            return Ok(n);
        }
    }

    Err(ParserError::InvalidGeneralRegister(Box::from(s)))
}

fn parse_hex_slice(s: &str) -> Result<Cell, ParserError> {
    fn hex_char(c: u8) -> Result<u8, ParserError> {
        match c {
            b'A'..=b'F' => Ok(c - b'A' + 10),
            b'a'..=b'f' => Ok(c - b'a' + 10),
            b'0'..=b'9' => Ok(c - b'0'),
            _ => Err(ParserError::InvalidSlice(
                format!("Unexpected char `{c}` in hex bistring").into(),
            )),
        }
    }

    if !s.is_ascii() {
        return Err(ParserError::InvalidSlice(
            "Non-ascii characters in bitstring".into(),
        ));
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
        return Err(ParserError::InvalidSlice("Bitstring is too long".into()));
    }

    let mut builder = CellBuilder::new();

    let mut bytes = hex::decode(s).map_err(invalid_slice)?;

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

    builder.store_raw(&bytes, bits).map_err(invalid_slice)?;
    builder.build().map_err(invalid_slice)
}

fn parse_bin_slice(s: &str) -> Result<Cell, ParserError> {
    let mut bits = 0;
    let mut bytes = [0; 128];

    for char in s.chars() {
        let value = match char {
            '0' => 0u8,
            '1' => 1,
            c => {
                return Err(ParserError::InvalidSlice(
                    format!("Unexpected char `{c}` in binary bitstring").into(),
                ))
            }
        };
        bytes[bits / 8] |= value << (7 - bits % 8);

        bits += 1;
        if bits > MAX_BIT_LEN as usize {
            return Err(ParserError::InvalidSlice("Bitstring is too long".into()));
        }
    }

    let mut builder = CellBuilder::new();
    builder
        .store_raw(&bytes, bits as _)
        .map_err(invalid_slice)?;
    builder.build().map_err(invalid_slice)
}

fn invalid_slice<T: std::fmt::Display>(e: T) -> ParserError {
    ParserError::InvalidSlice(e.to_string().into())
}

#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl From<pest::Span<'_>> for Span {
    fn from(value: pest::Span) -> Self {
        Self {
            start: value.start(),
            end: value.end(),
        }
    }
}

#[derive(pest_derive::Parser)]
#[grammar = "asm.pest"]
pub struct Grammar;

#[allow(clippy::enum_variant_names)]
#[derive(thiserror::Error, Debug)]
pub enum ParserError {
    #[error("invalid input: {0}")]
    InvalidInput(Box<pest::error::Error<Rule>>),
    #[error("invalid int: {0}")]
    InvalidInt(#[from] num_bigint::ParseBigIntError),
    #[error("invalid stack register: {0}")]
    InvalidStackRegister(Box<str>),
    #[error("invalid general register: {0}")]
    InvalidGeneralRegister(Box<str>),
    #[error("invalid slice: {0}")]
    InvalidSlice(Box<str>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_asm() {
        assert!(parse("").unwrap().is_empty());
    }

    #[test]
    fn simple_asm() {
        const CODE: &str = r##"
        PUSHCONT {
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
        "##;

        let code = parse(CODE).unwrap();
        println!("{code:#?}");
    }

    #[test]
    fn wallet_v3() {
        const CODE: &str = r#"
        SETCP0 DUP IFNOTRET // return if recv_internal
        DUP
        PUSHINT 85143
        EQUAL OVER
        PUSHINT 78748
        EQUAL OR
        // "seqno" and "get_public_key" get-methods
        IFJUMP {
            PUSHINT 1
            AND
            PUSHCTR c4 CTOS
            LDU 32
            LDU 32
            NIP
            PLDU 256
            CONDSEL
        }
        // fail unless recv_external
        INC THROWIF 32

        PUSHPOW2 9 LDSLICEX // signature
        DUP
        LDU 32 // subwallet_id
        LDU 32 // valid_until
        LDU 32 // msg_seqno

        NOW
        XCHG s1, s3
        LEQ
        THROWIF 35

        PUSH c4 CTOS
        LDU 32
        LDU 32
        LDU 256
        ENDS

        XCPU s3, s2
        EQUAL
        THROWIF 33

        XCPU s4, s4
        EQUAL
        THROWIF 34

        XCHG s0, s4
        HASHSU
        XC2PU s0, s5, s5
        CHKSIGNU THROWIFNOT 35

        ACCEPT

        WHILE { DUP SREFS }, {
            LDU 8
            LDREF
            XCHG s0, s2
            SENDRAWMSG
        }
        ENDS SWAP INC

        NEWC
        STU 32
        STU 32
        STU 256
        ENDC
        POP c4
        "#;

        let code = parse(CODE).unwrap();
        println!("{code:#?}");
    }
}
