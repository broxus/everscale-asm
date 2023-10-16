use std::cmp::Ordering;
use std::sync::OnceLock;

use ahash::HashMap;
use either::Either;
use everscale_types::prelude::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use self::util::*;

mod ast;
mod util;

pub struct Code<'a> {
    _text: &'a str,
    ast: Vec<ast::Instr<'a>>,
}

impl<'a> Code<'a> {
    pub fn new(text: &'a str) -> Result<Self, ast::ParserError> {
        Ok(Self {
            _text: text,
            ast: ast::parse(text)?,
        })
    }

    pub fn assemble(self) -> Result<Cell, AsmError> {
        self.assemble_ext(&mut Cell::empty_context())
    }

    pub fn assemble_ext(self, context: &mut dyn CellContext) -> Result<Cell, AsmError> {
        let cell_context = &mut Cell::empty_context();
        let opcodes = cp0();
        let builder = self.assemble_block(opcodes, &self.ast, context)?;
        let cell = builder.build_ext(cell_context)?;
        Ok(cell)
    }

    fn assemble_block(
        &self,
        opcodes: &Opcodes,
        items: &[ast::Instr<'_>],
        cell_context: &mut dyn CellContext,
    ) -> Result<CellBuilder, AsmError> {
        let mut ctx = Context {
            stack: Default::default(),
            cell_context,
        };
        for item in items {
            self.assemble_instr(opcodes, &mut ctx, item)?;
        }
        ctx.into_builder()
    }

    fn assemble_instr(
        &self,
        opcodes: &Opcodes,
        ctx: &mut Context<'_>,
        instr: &ast::Instr<'_>,
    ) -> Result<(), AsmError> {
        let Some(handler) = opcodes.get(instr.ident) else {
            return Err(AsmError::UnknownOpcode(instr.ident.into()));
        };
        (handler)(ctx, &instr.args)
    }
}

struct Context<'a> {
    cell_context: &'a mut dyn CellContext,
    stack: Vec<CellBuilder>,
}

impl Context<'_> {
    fn into_builder(self) -> Result<CellBuilder, AsmError> {
        Self::merge_stack(self.stack, self.cell_context)
    }

    fn get_builder(&mut self, bits: u16) -> &mut CellBuilder {
        // NOTE: always reserve the last cell for the code
        self.get_builder_ext(bits, 1).0
    }

    fn get_builder_ext(&mut self, bits: u16, refs: u8) -> (&mut CellBuilder, &mut dyn CellContext) {
        'last: {
            if let Some(last) = self.stack.last() {
                if last.has_capacity(bits, refs) {
                    break 'last;
                }
            }
            self.stack.push(Default::default());
        };

        let builder = self.stack.last_mut().unwrap();
        (builder, self.cell_context)
    }

    fn merge_stack(
        mut stack: Vec<CellBuilder>,
        cell_context: &mut dyn CellContext,
    ) -> Result<CellBuilder, AsmError> {
        let mut result = None::<CellBuilder>;
        while let Some(mut last) = stack.pop() {
            if let Some(child) = result.take() {
                if last.has_capacity(child.bit_len(), child.reference_count()) {
                    last.store_slice(child.as_full_slice())?;
                } else {
                    last.store_reference(child.build_ext(cell_context)?)?;
                }
            }
            result = Some(last);
        }

        Ok(result.unwrap_or_default())
    }
}

type Opcodes = HashMap<&'static str, OpcodeHandlerFn>;
type OpcodeHandlerFn = fn(&mut Context<'_>, &[ast::InstrArg<'_>]) -> Result<(), AsmError>;

trait ArgsExt {
    fn parse<'a, T: FromInstrArgs<'a>>(&'a self) -> Result<T, AsmError>;
}

impl ArgsExt for [ast::InstrArg<'_>] {
    #[inline]
    fn parse<'a, T: FromInstrArgs<'a>>(&'a self) -> Result<T, AsmError> {
        T::from_instr_args(self)
    }
}

trait FromInstrArgs<'a>: Sized {
    fn from_instr_args(args: &'a [ast::InstrArg<'_>]) -> Result<Self, AsmError>;
}

impl<'a, T: FromInstrArg<'a>> FromInstrArgs<'a> for T {
    fn from_instr_args(args: &'a [ast::InstrArg<'_>]) -> Result<Self, AsmError> {
        let (s,) = <_>::from_instr_args(args)?;
        Ok(s)
    }
}

impl<'a, T: FromInstrArg<'a>> FromInstrArgs<'a> for (T,) {
    fn from_instr_args(args: &'a [ast::InstrArg<'_>]) -> Result<Self, AsmError> {
        match args {
            [a] => Ok((T::from_instr_arg(a)?,)),
            [] => Err(AsmError::NotEnoughArgs),
            _ => Err(AsmError::TooManyArgs),
        }
    }
}

impl FromInstrArgs<'_> for () {
    fn from_instr_args(args: &[ast::InstrArg<'_>]) -> Result<Self, AsmError> {
        if args.is_empty() {
            Ok(())
        } else {
            Err(AsmError::TooManyArgs)
        }
    }
}

impl<'a, T1, T2> FromInstrArgs<'a> for (T1, T2)
where
    T1: FromInstrArg<'a>,
    T2: FromInstrArg<'a>,
{
    fn from_instr_args(args: &'a [ast::InstrArg<'_>]) -> Result<Self, AsmError> {
        if args.len() < 2 {
            return Err(AsmError::NotEnoughArgs);
        }
        match args {
            [a1, a2] => Ok((T1::from_instr_arg(a1)?, T2::from_instr_arg(a2)?)),
            _ => Err(AsmError::TooManyArgs),
        }
    }
}

impl<'a, T1, T2, T3> FromInstrArgs<'a> for (T1, T2, T3)
where
    T1: FromInstrArg<'a>,
    T2: FromInstrArg<'a>,
    T3: FromInstrArg<'a>,
{
    fn from_instr_args(args: &'a [ast::InstrArg<'_>]) -> Result<Self, AsmError> {
        if args.len() < 3 {
            return Err(AsmError::NotEnoughArgs);
        }
        match args {
            [a1, a2, a3] => Ok((
                T1::from_instr_arg(a1)?,
                T2::from_instr_arg(a2)?,
                T3::from_instr_arg(a3)?,
            )),
            _ => Err(AsmError::TooManyArgs),
        }
    }
}

trait FromInstrArg<'a>: Sized {
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

struct WithSpan<T>(T, ast::Span);

impl<'a, T> FromInstrArg<'a> for WithSpan<T>
where
    T: FromInstrArg<'a>,
{
    fn from_instr_arg(arg: &'a ast::InstrArg<'_>) -> Result<Self, AsmError> {
        let span = arg.span;
        Ok(Self(T::from_instr_arg(arg)?, span))
    }
}

struct Nat<'a>(&'a BigInt);

impl<'a> FromInstrArg<'a> for Nat<'a> {
    fn from_instr_arg(arg: &'a ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => Ok(Self(n)),
            _ => Err(AsmError::UnexpectedArg),
        }
    }
}

struct NatU4(u8);

impl FromInstrArg<'_> for NatU4 {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u8() {
                    if n <= 0xf {
                        return Ok(Self(n));
                    }
                }
                Err(AsmError::OutOfRange)
            }
            _ => Err(AsmError::UnexpectedArg),
        }
    }
}

struct NatU8(u8);

impl FromInstrArg<'_> for NatU8 {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => match n.to_u8() {
                Some(n) => Ok(Self(n)),
                None => Err(AsmError::OutOfRange),
            },
            _ => Err(AsmError::UnexpectedArg),
        }
    }
}

struct NatU8minus1(u8);

impl FromInstrArg<'_> for NatU8minus1 {
    fn from_instr_arg(arg: &'_ ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u16() {
                    if (1..=256).contains(&n) {
                        return Ok(Self((n - 1) as u8));
                    }
                }
                Err(AsmError::OutOfRange)
            }
            _ => Err(AsmError::UnexpectedArg),
        }
    }
}

struct SReg(u8);

impl FromInstrArg<'_> for SReg {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::SReg(n) => FullSReg(*n).try_into(),
            _ => Err(AsmError::UnexpectedArg),
        }
    }
}

struct FullSReg(i16);

impl FromInstrArg<'_> for FullSReg {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::SReg(n) => Ok(Self(*n)),
            _ => Err(AsmError::UnexpectedArg),
        }
    }
}

impl TryInto<SReg> for FullSReg {
    type Error = AsmError;

    fn try_into(self) -> Result<SReg, Self::Error> {
        if (0x0..=0xf).contains(&self.0) {
            Ok(SReg(self.0 as u8))
        } else {
            Err(AsmError::InvalidRegister)
        }
    }
}

struct CReg(u8);

impl FromInstrArg<'_> for CReg {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::CReg(n) => Ok(Self(*n)),
            _ => Err(AsmError::UnexpectedArg),
        }
    }
}

fn cp0() -> &'static Opcodes {
    static OPCODES: OnceLock<Opcodes> = OnceLock::new();
    OPCODES.get_or_init(|| {
        let mut t = Opcodes::default();
        register_stackops(&mut t);
        t
    })
}

fn register_stackops(t: &mut Opcodes) {
    macro_rules! define_opcodes {
        ($t:ident, { $($($names:literal)|+ => $base:tt$(( $($args:tt)* ))? ),+, }) => {
            $(define_opcodes!(@args $t $($names)|+ $base $($($args)*)?));+
        };
        (@args $t:ident $($names:literal)|+ $f:ident) => {
            $($t.insert($names, $f));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal) => {
            $($t.insert(
                $names,
                op_simple::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal s) => {
            $($t.insert(
                $names,
                op_1sr::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal u4) => {
            $($t.insert(
                $names,
                op_u4::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal u8 - 1) => {
            $($t.insert(
                $names,
                op_u8_minus1::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal c) => {
            $($t.insert(
                $names,
                op_1cr::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal s, s) => {
            $($t.insert(
                $names,
                op_2sr::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal s, s, adj = $adj:literal) => {
            $($t.insert(
                $names,
                op_2sr_adj::<$base, { (stringify!($base).len() - 2) as u16 * 4 }, $adj>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal s, s, s) => {
            $($t.insert(
                $names,
                op_3sr::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal s, s, s, adj = $adj:literal) => {
            $($t.insert(
                $names,
                op_3sr_adj::<$base, { (stringify!($base).len() - 2) as u16 * 4 }, $adj>,
            ));+
        };
    }

    define_opcodes!(t, {
        // Simple stack primitives
        "NOP" => 0x00,
        "SWAP" => 0x01,
        "XCHG0" => 0x0(s),
        "XCHG" => op_xchg,
        "PUSH" => op_push,
        "DUP" => 0x20,
        "OVER" => 0x21,
        "POP" => op_pop,
        "DROP" => 0x30,
        "NIP" => 0x31,

        // Compound stack primitives
        "XCHG3" => 0x4(s, s, s),
        "XCHG2" => 0x50(s, s),
        "XCPU" => 0x51(s, s),
        "PUXC" => 0x52(s, s, adj = 0x01),
        "PUSH2" => 0x53(s, s),
        "XCHG3_l" => 0x540(s, s, s),
        "XC2PU" => 0x541(s, s, s),
        "XCPUXC" => 0x542(s, s, s, adj = 0x001),
        "XCPU2" => 0x543(s, s, s),
        "PUXC2" => 0x544(s, s, s, adj = 0x011),
        "PUXCPU" => 0x545(s, s, s, adj = 0x011),
        "PU2XC" => 0x546(s, s, s, adj = 0x012),
        "PUSH3" => 0x547(s, s, s),
        // TODO: BLKSWAP
        // TODO: ROLL
        // TODO: -ROLL | ROLLREV
        "2ROT" | "ROT2" => 0x5513,

        // Exotic stack primitives
        "ROT" => 0x58,
        "-ROT" | "ROTREV" => 0x59,
        "2SWAP" | "SWAP2" => 0x5a,
        "2DROP" | "DROP2" => 0x5b,
        "2DUP" | "DUP2" => 0x5c,
        "2OVER" | "OVER2" => 0x5d,
        // TODO: REVERSE
        "BLKDROP" => 0x5f0(u4),
        // TODO: BLKPUSH
        "PICK" | "PUSHX" => 0x60,
        "ROLLX" => 0x61,
        "-ROLLX" | "ROLLREVX" => 0x62,
        "BLKSWX" => 0x63,
        "REVX" => 0x64,
        "DROPX" => 0x65,
        "TUCK" => 0x66,
        "XCHGX" => 0x67,
        "DEPTH" => 0x68,
        "CHKDEPTH" => 0x69,
        "ONLYTOPX" => 0x6a,
        "ONLYX" => 0x6b,
        // TODO: BLKDROP2

        // Null primitives
        "NULL" | "PUSHNULL" => 0x6d,
        "ISNULL" => 0x6e,
        // Tuple primitives
        "TUPLE" => 0x6f0(u4),
        "NIL" => 0x6f00,
        "SINGLE" => 0x6f01,
        "PAIR" | "CONS" => 0x6f02,
        "TRIPLE" => 0x6f03,
        "INDEX" => 0x6f1(u4),
        "FIRST" | "CAR" => 0x6f10,
        "SECOND" | "CDR" => 0x6f11,
        "THIRD" => 0x6f12,
        "UNTUPLE" => 0x6f2(u4),
        "UNSINGLE" => 0x6f21,
        "UNPAIR" | "UNCONS" => 0x6f22,
        "UNTRIPLE" => 0x6f23,
        "UNPACKFIRST" => 0x6f3(u4),
        "CHKTUPLE" => 0x6f30,
        "EXPLODE" => 0x6f4(u4),
        "SETINDEX" => 0x6f5(u4),
        "SETFIRST" => 0x6f50,
        "SETSECOND" => 0x6f51,
        "SETTHIRD" => 0x6f52,
        "INDEXQ" => 0x6f6(u4),
        "FIRSTQ" | "CARQ" => 0x6f60,
        "SECONDQ" | "CDRQ" => 0x6f61,
        "THIRDQ" => 0x6f62,
        "SETINDEXQ" => 0x6f7(u4),
        "SETFIRSTQ" => 0x6f70,
        "SETSECONDQ" => 0x6f71,
        "SETTHIRDQ" => 0x6f72,
        "TUPLEVAR" => 0x6f80,
        "INDEXVAR" => 0x6f81,
        "UNTUPLEVAR" => 0x6f82,
        "UNPACKFIRSTVAR" => 0x6f83,
        "EXPLODEVAR" => 0x6f84,
        "SETINDEXVAR" => 0x6f85,
        "INDEXVARQ" => 0x6f86,
        "SETINDEXVARQ" => 0x6f87,
        "TLEN" => 0x6f88,
        "QTLEN" => 0x6f89,
        "ISTUPLE" => 0x6f8a,
        "LAST" => 0x6f8b,
        "TPUSH" | "COMMA" => 0x6f8c,
        "TPOP" => 0x6f8d,
        "NULLSWAPIF" => 0x6fa0,
        "NULLSWAPIFNOT" => 0x6fa1,
        "NULLROTRIF" => 0x6fa2,
        "NULLROTRIFNOT" => 0x6fa3,
        "NULLSWAPIF2" => 0x6fa4,
        "NULLSWAPIFNOT2" => 0x6fa5,
        "NULLROTRIF2" => 0x6fa6,
        "NULLROTRIFNOT2" => 0x6fa7,
        // TODO: INDEX2
        "CADR" => 0x6fb4,
        "CDDR" => 0x6fb5,
        // TODO: INDEX3
        "CADDR" => 0x6fd4,
        "CDDDR" => 0x6fd5,

        // Integer constants
        "ZERO" | "FALSE" => 0x70,
        "ONE" => 0x71,
        "TWO" => 0x72,
        "TEN" => 0x7a,
        "TRUE" => 0x7f,
        "PUSHINT" | "INT" => op_pushint,
        "PUSHPOW2" => op_pushpow2,
        "PUSHNAN" => 0x83ff,
        "PUSHPOW2DEC" => 0x84(u8 - 1),
        "PUSHNEGPOW2" => 0x85(u8 - 1),

        // TODO: other
        "PUSHCTR" => 0xed4(c),
        "POPCTR" => 0xed5(c),
    });
}

fn op_xchg(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    const SREG_RANGE: std::ops::RangeInclusive<i16> = 0x00..=0xff;

    let (FullSReg(mut s1), FullSReg(mut s2)) = args.parse()?;
    if !SREG_RANGE.contains(&s1) || !SREG_RANGE.contains(&s2) {
        return Err(AsmError::InvalidRegister);
    }

    match s1.cmp(&s2) {
        Ordering::Equal => return Ok(()),
        Ordering::Greater => std::mem::swap(&mut s1, &mut s2),
        Ordering::Less => {}
    }

    match (s1, s2) {
        (0, 0x1..=0xf) => ctx.get_builder(8).store_u8(s2 as u8),
        (0, 0x10..=0xff) => ctx.get_builder(16).store_u16(0x1100 | s2 as u16),
        (1, 0x2..=0xf) => ctx.get_builder(8).store_u8(0x10 | s2 as u8),
        (0x2..=0xf, 0x2..=0xf) => ctx
            .get_builder(16)
            .store_u16(0x1000 | ((s1 as u16) << 4) | (s2 as u16)),
        (0x2..=0xf, 0x10..=0xff) => {
            let b = ctx.get_builder(8 + 16 + 8);
            b.store_u8(s1 as u8)?;
            b.store_u16(0x1100 | s2 as u16)?;
            b.store_u8(s1 as u8)
        }
        (0x10..=0xff, 0x10..=0xff) => {
            let b = ctx.get_builder(16 * 3);
            b.store_u16(0x1100 | s1 as u16)?;
            b.store_u16(0x1100 | s2 as u16)?;
            b.store_u16(0x1100 | s1 as u16)
        }
        _ => Ok(()),
    }
    .map_err(AsmError::StoreError)
}

fn op_push(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    match args.parse()? {
        Either::Left(FullSReg(s1)) => match s1 {
            0x0..=0xf => ctx.get_builder(8).store_u8(0x20 | s1 as u8),
            0x10..=0xff => ctx.get_builder(16).store_u16(0x5600 | s1 as u16),
            _ => return Err(AsmError::InvalidRegister),
        },
        Either::Right(CReg(c)) => ctx.get_builder(16).store_u16(0xed40 | c as u16),
    }
    .map_err(AsmError::StoreError)
}

fn op_pop(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    match args.parse()? {
        Either::Left(FullSReg(s1)) => match s1 {
            0x0..=0xf => ctx.get_builder(8).store_u8(0x30 | s1 as u8),
            0x10..=0xff => ctx.get_builder(16).store_u16(0x5700 | s1 as u16),
            _ => return Err(AsmError::InvalidRegister),
        },
        Either::Right(CReg(c)) => ctx.get_builder(16).store_u16(0xed40 | c as u16),
    }
    .map_err(AsmError::StoreError)
}

fn op_pushint(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    let Nat(n) = args.parse()?;

    if let Some(n) = n.to_i8() {
        if (-5..=10).contains(&n) {
            return ctx
                .get_builder(8)
                .store_u8(0x70 | (n as u8) & 0xf)
                .map_err(AsmError::StoreError);
        }
    }

    let bitsize = bitsize(n);
    if bitsize <= 8 {
        let b = ctx.get_builder(16);
        b.store_u8(0x80)?;
        store_int_to_builder(b, n, 8)
    } else if bitsize <= 16 {
        let b = ctx.get_builder(24);
        b.store_u8(0x81)?;
        store_int_to_builder(b, n, 16)
    } else {
        if bitsize > 257 {
            return Err(AsmError::OutOfRange);
        }
        let l = (bitsize + 4) / 8;
        let value_bits = 3 + l * 8;
        let b = ctx.get_builder(13 + value_bits);
        b.store_u8(0x82)?;
        b.store_small_uint((l - 2) as u8, 5)?;
        store_int_to_builder(b, n, value_bits)
    }
    .map_err(AsmError::StoreError)
}

fn op_pushpow2(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    let Nat(n) = args.parse()?;

    match n.to_u16().unwrap_or(u16::MAX) {
        0 => ctx.get_builder(8).store_u8(0x71),
        n @ 1..=255 => {
            let b = ctx.get_builder(16);
            b.store_u8(0x83)?;
            b.store_u8((n - 1) as _)
        }
        256 => return Err(AsmError::WrongUsage("use PUSHNAN instead of PUSHPOW2 256")),
        _ => return Err(AsmError::OutOfRange),
    }
    .map_err(AsmError::StoreError)
}

fn op_simple<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    args.parse::<()>()?;
    write_op(ctx, BASE, BITS)
}

fn op_1sr<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let SReg(s1) = args.parse()?;
    write_op_1sr(ctx, BASE, BITS, s1)
}

fn op_u4<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let NatU4(s1) = args.parse()?;
    write_op_1sr(ctx, BASE, BITS, s1)
}

fn op_u8_minus1<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let NatU8minus1(s1) = args.parse()?;
    write_op_1sr_l(ctx, BASE, BITS, s1)
}

fn op_2sr<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let (SReg(s1), SReg(s2)) = args.parse()?;
    write_op_2sr(ctx, BASE, BITS, s1, s2)
}

fn op_2sr_adj<const BASE: u32, const BITS: u16, const ADJ: u32>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let (mut s1 @ FullSReg(_), mut s2 @ FullSReg(_)) = args.parse()?;
    s1.0 += ((ADJ >> 4) & 0xf) as i16;
    s2.0 += (ADJ & 0xf) as i16;
    let SReg(s1) = s1.try_into()?;
    let SReg(s2) = s2.try_into()?;
    write_op_2sr(ctx, BASE, BITS, s1, s2)
}

fn op_3sr<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let (SReg(s1), SReg(s2), SReg(s3)) = args.parse()?;
    write_op_3sr(ctx, BASE, BITS, s1, s2, s3)
}

fn op_3sr_adj<const BASE: u32, const BITS: u16, const ADJ: u32>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let (mut s1 @ FullSReg(_), mut s2 @ FullSReg(_), mut s3 @ FullSReg(_)) = args.parse()?;
    s1.0 += ((ADJ >> 8) & 0xf) as i16;
    s2.0 += ((ADJ >> 4) & 0xf) as i16;
    s3.0 += (ADJ & 0xf) as i16;
    let SReg(s1) = s1.try_into()?;
    let SReg(s2) = s2.try_into()?;
    let SReg(s3) = s3.try_into()?;
    write_op_3sr(ctx, BASE, BITS, s1, s2, s3)
}

fn op_1cr<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let CReg(c) = args.parse()?;
    write_op_1sr(ctx, BASE, BITS, c)
}

fn write_op(ctx: &mut Context<'_>, base: u32, bits: u16) -> Result<(), AsmError> {
    ctx.get_builder(bits)
        .store_uint(base as _, bits)
        .map_err(AsmError::StoreError)
}

fn write_op_1sr(ctx: &mut Context<'_>, base: u32, bits: u16, s1: u8) -> Result<(), AsmError> {
    ctx.get_builder(bits + 4)
        .store_uint(((base << 4) | s1 as u32) as _, bits + 4)
        .map_err(AsmError::StoreError)
}

fn write_op_1sr_l(ctx: &mut Context<'_>, base: u32, bits: u16, s1: u8) -> Result<(), AsmError> {
    ctx.get_builder(bits + 8)
        .store_uint(((base << 8) | s1 as u32) as _, bits + 8)
        .map_err(AsmError::StoreError)
}

fn write_op_2sr(
    ctx: &mut Context<'_>,
    base: u32,
    bits: u16,
    s1: u8,
    s2: u8,
) -> Result<(), AsmError> {
    ctx.get_builder(bits + 8)
        .store_uint(
            ((base << 8) | (s1 << 4) as u32 | (s2 & 0xf) as u32) as _,
            bits + 8,
        )
        .map_err(AsmError::StoreError)
}

fn write_op_3sr(
    ctx: &mut Context<'_>,
    base: u32,
    bits: u16,
    s1: u8,
    s2: u8,
    s3: u8,
) -> Result<(), AsmError> {
    let args = (((s1 & 0xf) as u32) << 8) | (((s2 & 0xf) as u32) << 4) | ((s3 & 0xf) as u32);
    ctx.get_builder(bits + 12)
        .store_uint(((base << 12) | args) as _, bits + 12)
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stack_ops() -> anyhow::Result<()> {
        let cell = Code::new(
            r##"
            XCHG s1, s2
            NOP
            SWAP
            XCHG3 s1, s2, s3
            "##,
        )?
        .assemble()?;

        assert_eq!(
            cell.repr_hash(),
            &"5f099122adde2ed3712374da4cd4e04e3214f0ddd7f155ffea923f1f2ab42d2b"
                .parse::<HashBytes>()
                .unwrap()
        );

        println!("{}", cell.display_tree());

        Ok(())
    }

    #[test]
    fn pushint() -> anyhow::Result<()> {
        let cell_tiny = Code::new("INT 7")?.assemble()?;
        assert_eq!(cell_tiny.data(), &[0x77]);

        let cell_byte = Code::new("INT 120")?.assemble()?;
        assert_eq!(cell_byte.data(), &[0x80, 120]);

        let cell_short = Code::new("INT 16000")?.assemble()?;
        assert_eq!(
            cell_short.data(),
            &[0x81, ((16000 >> 8) & 0xff) as u8, ((16000) & 0xff) as u8]
        );

        let cell_big = Code::new("INT 123123123123123123")?.assemble()?;
        assert_eq!(cell_big.data(), hex::decode("8229b56bd40163f3b3")?);

        let cell_max =
            Code::new("INT 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")?
                .assemble()?;
        assert_eq!(
            cell_max.data(),
            hex::decode("82f0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")?
        );

        let cell_neg_max =
            Code::new("INT -0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")?
                .assemble()?;
        assert_eq!(
            cell_neg_max.data(),
            hex::decode("82f70000000000000000000000000000000000000000000000000000000000000001")?
        );

        Ok(())
    }

    #[test]
    fn display() -> anyhow::Result<()> {
        let code = Code::new("PUSHPOW2DEC 256")?.assemble()?;
        println!("{}", code.display_tree());
        Ok(())
    }
}
