use std::cmp::Ordering;
use std::sync::OnceLock;

use ahash::HashMap;
use either::Either;
use everscale_types::cell::{MAX_BIT_LEN, MAX_REF_COUNT};
use everscale_types::prelude::*;
use num_bigint::{BigInt, Sign};
use num_traits::{One, ToPrimitive};

use self::util::*;

mod ast;
mod ast2;
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
        let builder = Self::assemble_block(opcodes, &self.ast, context)?;
        let cell = builder.build_ext(cell_context)?;
        Ok(cell)
    }

    fn assemble_block(
        opcodes: &Opcodes,
        items: &[ast::Instr<'_>],
        cell_context: &mut dyn CellContext,
    ) -> Result<CellBuilder, AsmError> {
        let mut ctx = Context {
            stack: Default::default(),
            cell_context,
        };
        for item in items {
            Self::assemble_instr(opcodes, &mut ctx, item)?;
        }
        ctx.into_builder()
    }

    fn assemble_instr(
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

    fn top_capacity(&self) -> (u16, u8) {
        match self.stack.last() {
            Some(last) => (last.spare_bits_capacity(), last.spare_refs_capacity()),
            None => (MAX_BIT_LEN, MAX_REF_COUNT as u8),
        }
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

struct NatU2(u8);

impl FromInstrArg<'_> for NatU2 {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u8() {
                    if n <= 0b11 {
                        return Ok(Self(n));
                    }
                }
                Err(AsmError::OutOfRange)
            }
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

struct NatU5(u8);

impl FromInstrArg<'_> for NatU5 {
    fn from_instr_arg(arg: &ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Nat(n) => {
                if let Some(n) = n.to_u8() {
                    if n <= 0b11111 {
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

struct SliceOrCont(Cell);

impl FromInstrArg<'_> for SliceOrCont {
    fn from_instr_arg(arg: &'_ ast::InstrArg<'_>) -> Result<Self, AsmError> {
        match &arg.value {
            ast::InstrArgValue::Slice(cell) => Ok(Self(cell.clone())),
            ast::InstrArgValue::Block(items) => {
                let cell_context = &mut Cell::empty_context();
                let opcodes = cp0();
                let builder = Code::assemble_block(opcodes, items, cell_context)?;
                builder
                    .build_ext(cell_context)
                    .map(Self)
                    .map_err(AsmError::StoreError)
            }
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
        (@args $t:ident $($names:literal)|+ $base:literal ref) => {
            $($t.insert(
                $names,
                op_1ref::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal ref, ref) => {
            $($t.insert(
                $names,
                op_2ref::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
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
        "INDEX2" => op_index2,
        "CADR" => 0x6fb4,
        "CDDR" => 0x6fb5,
        "INDEX3" => op_index3,
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

        // Other constants
        "PUSHREF" => 0x88(ref),
        "PUSHREFSLICE" => 0x89(ref),
        "PUSHREFCONT" => 0x8a(ref),
        "PUSHSLICE" | "SLICE" => op_pushslice,

        // Arithmetic operations
        "ADD" => 0xa0,
        "SUB" => 0xa1,
        "SUBR" => 0xa2,
        "NEGATE" => 0xa3,
        "INC" => 0xa4,
        "DEC" => 0xa5,
        // TODO: "ADDCONST" | "ADDINT"
        // TODO: "SUBCONST" | "SUBINT"
        // TODO: "MULCONST" | "MULINT"
        "MUL" => 0xa8,

        "DIV" => 0xa904,
        "DIVR" => 0xa905,
        "DIVC" => 0xa906,
        "MOD" => 0xa908,
        "MODR" => 0xa909,
        "MODC" => 0xa90a,
        "DIVMOD" => 0xa90c,
        "DIVMODR" => 0xa90d,
        "DIVMODC" => 0xa90e,

        "RSHIFTR" => 0xa925,
        "RSHIFTC" => 0xa926,
        "MODPOW2" => 0xa928,
        "MODPOW2R" => 0xa929,
        "MODPOW2C" => 0xa92a,
        "RSHIFTMOD" => 0xa92c,
        "RSHIFTMODR" => 0xa92d,
        "RSHIFTMODC" => 0xa92e,

        "RSHIFTR#" => 0xa935(u8 - 1),
        "RSHIFTC#" => 0xa936(u8 - 1),
        "MODPOW2#" => 0xa938(u8 - 1),
        "MODPOW2R#" => 0xa939(u8 - 1),
        "MODPOW2C#" => 0xa93a(u8 - 1),
        "RSHIFT#MOD" => 0xa93c(u8 - 1),
        "RSHIFTR#MOD" => 0xa93d(u8 - 1),
        "RSHIFTC#MOD" => 0xa93e(u8 - 1),

        "MULDIV" => 0xa984,
        "MULDIVR" => 0xa985,
        "MULDIVC" => 0xa986,
        "MULMOD" => 0xa988,
        "MULMODR" => 0xa989,
        "MULMODC" => 0xa98a,
        "MULDIVMOD" => 0xa98c,
        "MULDIVMODR" => 0xa98d,
        "MULDIVMODC" => 0xa98e,

        "MULRSHIFT" => 0xa9a4,
        "MULRSHIFTR" => 0xa9a5,
        "MULRSHIFTC" => 0xa9a6,
        "MULMODPOW2" => 0xa9a8,
        "MULMODPOW2R" => 0xa9a9,
        "MULMODPOW2C" => 0xa9aa,
        "MULRSHIFTMOD" => 0xa9ac,
        "MULRSHIFTRMOD" => 0xa9ad,
        "MULRSHIFTCMOD" => 0xa9ae,

        "MULRSHIFT#" => 0xa9b4(u8 - 1),
        "MULRSHIFTR#" => 0xa9b5(u8 - 1),
        "MULRSHIFTC#" => 0xa9b6(u8 - 1),
        "MULMODPOW2#" => 0xa9b8(u8 - 1),
        "MULMODPOW2R#" => 0xa9b9(u8 - 1),
        "MULMODPOW2C#" => 0xa9ba(u8 - 1),
        "MULRSHIFT#MOD" => 0xa9bc(u8 - 1),
        "MULRSHIFTR#MOD" => 0xa9bd(u8 - 1),
        "MULRSHIFTC#MOD" => 0xa9be(u8 - 1),

        "LSHIFTDIV" => 0xa9c4,
        "LSHIFTDIVR" => 0xa9c5,
        "LSHIFTDIVC" => 0xa9c6,
        "LSHIFTMOD" => 0xa9c8,
        "LSHIFTMODR" => 0xa9c9,
        "LSHIFTMODC" => 0xa9ca,
        "LSHIFTDIVMOD" => 0xa9cc,
        "LSHIFTDIVMODR" => 0xa9cd,
        "LSHIFTDIVMODC" => 0xa9ce,

        "LSHIFT#DIV" => 0xa9d4(u8 - 1),
        "LSHIFT#DIVR" => 0xa9d5(u8 - 1),
        "LSHIFT#DIVC" => 0xa9d6(u8 - 1),
        "LSHIFT#MOD" => 0xa9d8(u8 - 1),
        "LSHIFT#MODR" => 0xa9d9(u8 - 1),
        "LSHIFT#MODC" => 0xa9da(u8 - 1),
        "LSHIFT#DIVMOD" => 0xa9dc(u8 - 1),
        "LSHIFT#DIVMODR" => 0xa9dd(u8 - 1),
        "LSHIFT#DIVMODC" => 0xa9de(u8 - 1),

        "LSHIFT#" => 0xaa(u8 - 1),
        "RSHIFT#" => 0xab(u8 - 1),
        "LSHIFT" => 0xac,
        "RSHIFT" => 0xad,
        "POW2" => 0xae,
        "AND" => 0xb0,
        "OR" => 0xb1,
        "XOR" => 0xb2,
        "NOT" => 0xb3,
        "FITS" => 0xb4(u8 - 1),
        "CHKBOOL" => 0xb400,
        "UFITS" => 0xb5(u8 - 1),
        "CHKBIT" => 0xb500,
        "FITSX" => 0xb600,
        "UFITSX" => 0xb601,
        "BITSIZE" => 0xb602,
        "UBITSIZE" => 0xb603,
        "MIN" => 0xb608,
        "MAX" => 0xb609,
        "MINMAX" | "INTSORT2" => 0xb60a,
        "ABS" => 0xb60b,
        "QUIET" => 0xb7,
        "QADD" => 0xb7a0,
        "QSUB" => 0xb7a1,
        "QSUBR" => 0xb7a2,
        "QNEGATE" => 0xb7a3,
        "QINC" => 0xb7a4,
        "QDEC" => 0xb7a5,
        "QMUL" => 0xb7a8,
        "QDIV" => 0xb7a904,
        "QDIVR" => 0xb7a905,
        "QDIVC" => 0xb7a906,
        "QMOD" => 0xb7a908,
        "QDIVMOD" => 0xb7a90c,
        "QDIVMODR" => 0xb7a90d,
        "QDIVMODC" => 0xb7a90e,
        "QMULDIVR" => 0xb7a985,
        "QMULDIVMOD" => 0xb7a98c,
        "QLSHIFT" => 0xb7ac,
        "QRSHIFT" => 0xb7ad,
        "QPOW2" => 0xb7ae,
        "QAND" => 0xb7b0,
        "QOR" => 0xb7b1,
        "QXOR" => 0xb7b2,
        "QNOT" => 0xb7b3,
        "QFITS" => 0xb7b4,
        "QUFITS" => 0xb7b5,
        "QFITSX" => 0xb7b600,
        "QUFITSX" => 0xb7b601,

        // Advanced integer constants
        "PUSHINTX" | "INTX" => op_pushintx,

        // Integer comparison
        "SGN" => 0xb8,
        "LESS" => 0xb9,
        "EQUAL" => 0xba,
        "LEQ" => 0xbb,
        "GREATER" => 0xbc,
        "NEQ" => 0xbd,
        "GEQ" => 0xbe,
        "CMP" => 0xbf,
        // TODO: EQINT
        "ISZERO" => 0xc000,
        // TODO: LESSINT
        // TODO: LEQINT
        "ISNEG" => 0xc100,
        "ISNPOS" => 0xc101,
        // TODO: GTINT,
        // TODO: GEQINT,
        "ISPOS" => 0xc200,
        "ISNNEG" => 0xc2ff,
        // TODO: NEQINT
        "ISNZERO" => 0xc300,
        "ISNAN" => 0xc4,
        "CHKNAN" => 0xc5,

        // Other comparison
        "SEMPTY" => 0xc700,
        "SDEMPTY" => 0xc701,
        "SREMPTY" => 0xc702,
        "SDFIRST" => 0xc703,
        "SDLEXCMP" => 0xc704,
        "SDEQ" => 0xc705,
        "SDPFX" => 0xc708,
        "SDPFXREV" => 0xc709,
        "SDPPFX" => 0xc70a,
        "SDPPFXREV" => 0xc70b,
        "SDSFX" => 0xc70c,
        "SDSFXREV" => 0xc70d,
        "SDPSFX" => 0xc70e,
        "SDPSFXREV" => 0xc70f,
        "SDCNTLEAD0" => 0xc710,
        "SDCNTLEAD1" => 0xc711,
        "SDCNTTRAIL0" => 0xc712,
        "SDCNTTRAIL1" => 0xc713,

        // Cell serialization (Builder manipulation primitives)
        "NEWC" => 0xc8,
        "ENDC" => 0xc9,
        "STI" => 0xca(u8 - 1),
        "STU" => 0xcb(u8 - 1),
        "STREF" => 0xcc,
        "STBREFR" | "ENDCST" => 0xcd,
        "STSLICE" => 0xce,
        "STIX" => 0xcf00,
        "STUX" => 0xcf01,
        "STIXR" => 0xcf02,
        "STUXR" => 0xcf03,
        "STIXQ" => 0xcf04,
        "STUXQ" => 0xcf05,
        "STIXRQ" => 0xcf06,
        "STUXRQ" => 0xcf07,
        "STI_l" => 0xcf08(u8 - 1),
        "STU_l" => 0xcf09(u8 - 1),
        "STIR" => 0xcf0a(u8 - 1),
        "STUR" => 0xcf0b(u8 - 1),
        "STIQ" => 0xcf0c(u8 - 1),
        "STUQ" => 0xcf0d(u8 - 1),
        "STIRQ" => 0xcf0e(u8 - 1),
        "STURQ" => 0xcf0f(u8 - 1),
        "STREF_l" => 0xcf10,
        "STBREF" => 0xcf11,
        "STSLICE_l" => 0xcf12,
        "STB" => 0xcf13,
        "STREFR" => 0xcf14,
        "STBREFR_l" => 0xcf15,
        "STSLICER" => 0xcf16,
        "STBR" | "BCONCAT" => 0xcf17,
        "STREFQ" => 0xcf18,
        "STBREFQ" => 0xcf19,
        "STSLICEQ" => 0xcf1a,
        "STBQ" => 0xcf1b,
        "STREFRQ" => 0xcf1c,
        "STBREFRQ" => 0xcf1d,
        "STSLICERQ" => 0xcf1e,
        "STBRQ" | "BCONCATQ" => 0xcf1f,
        "STREFCONST" => 0xcf20(ref),
        "STREF2CONST" => 0xcf21(ref, ref),
        "ENDXC" => 0xcf23,
        "STILE4" => 0xcf28,
        "STULE4" => 0xcf29,
        "STILE8" => 0xcf2a,
        "STULE8" => 0xcf2b,
        "BDEPTH" => 0xcf30,
        "BBITS" => 0xcf31,
        "BREFS" => 0xcf32,
        "BBITREFS" => 0xcf33,
        "BREMBITS" => 0xcf35,
        "BREMREFS" => 0xcf36,
        "BREMBITREFS" => 0xcf37,
        "BCHKBITS#" => 0xcf38(u8 - 1),
        "BCHKBITS" => 0xcf39,
        "BCHKREFS" => 0xcf3a,
        "BCHKBITREFS" => 0xcf3b,
        "BCHKBITSQ#" => 0xcf3c(u8 - 1),
        "BCHKBITSQ" => 0xcf3d,
        "BCHKREFSQ" => 0xcf3e,
        "BCHKBITREFSQ" => 0xcf3f,
        "STZEROES" => 0xcf40,
        "STONES" => 0xcf41,
        "STSAME" => 0xcf42,
        // TODO: STSLICECONST
        "STZERO" => 0xcf81,
        "STONE" => 0xcf93,

        // Cell deserialization (CellSlice primitives)
        "CTOS" => 0xd0,
        "ENDS" => 0xd1,
        "LDI" => 0xd2(u8 - 1),
        "LDU" => 0xd3(u8 - 1),
        "LDREF" => 0xd4,
        "LDREFRTOS" => 0xd5,
        "LDSLICE" => 0xd6(u8 - 1),
        "LDIX" => 0xd700,
        "LDUX" => 0xd701,
        "PLDIX" => 0xd702,
        "PLDUX" => 0xd703,
        "LDIXQ" => 0xd704,
        "LDUXQ" => 0xd705,
        "PLDIXQ" => 0xd706,
        "PLDUXQ" => 0xd707,
        "LDI_l" => 0xd708(u8 - 1),
        "LDU_l" => 0xd709(u8 - 1),
        "PLDI" => 0xd70a(u8 - 1),
        "PLDU" => 0xd70b(u8 - 1),
        "LDIQ" => 0xd70c(u8 - 1),
        "LDUQ" => 0xd70d(u8 - 1),
        "PLDIQ" => 0xd70e(u8 - 1),
        "PLDUQ" => 0xd70f(u8 - 1),
        // TODO: PLDUZ
        "LDSLICEX" => 0xd718,
        "PLDSLICEX" => 0xd719,
        "LDSLICEXQ" => 0xd71a,
        "PLDSLICEXQ" => 0xd71b,
        "LDSLICE_l" => 0xd71c(u8 - 1),
        "PLDSLICE" => 0xd71d(u8 - 1),
        "LDSLICEQ" => 0xd71e(u8 - 1),
        "PLDSLICEQ" => 0xd71f(u8 - 1),
        "SDCUTFIRST" => 0xd720,
        "SDSKIPFIRST" => 0xd721,
        "SDCUTLAST" => 0xd722,
        "SDSKIPLAST" => 0xd723,
        "SDSUBSTR" => 0xd724,
        "SDBEGINSX" => 0xd726,
        "SDBEGINSXQ" => 0xd727,
        // TODO: SDBEGINS:imm
        // TODO: SDBEGINS
        // TODO: SDBEGINSQ:imm
        // TODO: SDBEGINSQ
        "SCUTFIRST" => 0xd730,
        "SSKIPFIRST" => 0xd731,
        "SCUTLAST" => 0xd732,
        "SSKIPLAST" => 0xd733,
        "SUBSLICE" => 0xd734,
        "SPLIT" => 0xd736,
        "SPLITQ" => 0xd737,
        "XCTOS" => 0xd739,
        "XLOAD" => 0xd73a,
        "XLOADQ" => 0xd73b,
        "SCHKBITS" => 0xd741,
        "SCHKREFS" => 0xd742,
        "SCHKBITREFS" => 0xd743,
        "SCHKBITSQ" => 0xd745,
        "SCHKREFSQ" => 0xd746,
        "SCHKBITREFSQ" => 0xd747,
        "PLDREFVAR" => 0xd748,
        "SBITS" => 0xd749,
        "SREFS" => 0xd74a,
        "SBITREFS" => 0xd74b,
        "PLDREFIDX" => op_pldrefidx,
        "PLDREF" => 0xd74c,
        "LDILE4" => 0xd750,
        "LDULE4" => 0xd751,
        "LDILE8" => 0xd752,
        "LDULE8" => 0xd753,
        "PLDILE4" => 0xd754,
        "PLDULE4" => 0xd755,
        "PLDILE8" => 0xd756,
        "PLDULE8" => 0xd757,
        "LDILE4Q" => 0xd758,
        "LDULE4Q" => 0xd759,
        "LDILE8Q" => 0xd75a,
        "LDULE8Q" => 0xd75b,
        "PLDILE4Q" => 0xd75c,
        "PLDULE4Q" => 0xd75d,
        "PLDILE8Q" => 0xd75e,
        "PLDULE8Q" => 0xd75f,
        "LDZEROES" => 0xd760,
        "LDONES" => 0xd761,
        "LDSAME" => 0xd762,
        "SDEPTH" => 0xd764,
        "CDEPTH" => 0xd765,

        // Continuation / Flow control primitives
        "EXECUTE" | "CALLX" => 0xd8,
        "JMPX" => 0xd9,
        // TODO: CALLXARGS
        "JMPXARGS" => 0xdb1(u4),
        "RETARGS" => 0xdb2(u4),
        "RET" | "RETTRUE" => 0xdb30,
        "RETALT" | "RETFALSE" => 0xdb31,
        "BRANCH" | "RETBOOL" => 0xdb32,
        "CALLCC" => 0xdb34,
        "JMPXDATA" => 0xdb35,
        // TODO: CALLCCARGS
        "CALLXVARARGS" => 0xdb38,
        "RETVARARGS" => 0xdb39,
        "JMPXVARARGS" => 0xdb3a,
        "CALLCCVARARGS" => 0xdb3b,
        "CALLREF" => 0xdb3c(ref),
        "JMPREF" => 0xdb3d(ref),
        "JMPREFDATA" => 0xdb3e(ref),
        "RETDATA" => 0xdb3f,

        // Conditional and iterated execution primitives
        "IFRET" => 0xdc,
        "IFNOTRET" => 0xdd,
        "IF" => 0xde,
        "IFNOT" => 0xdf,
        "IFJMP" => 0xe0,
        "IFNOTJMP" => 0xe1,
        "IFELSE" => 0xe2,

        "IFREF" => 0xe300(ref),
        "IFNOTREF" => 0xe301(ref),
        "IFJMPREF" => 0xe302(ref),
        "IFNOTJMPREF" => 0xe303(ref),
        "CONDSEL" => 0xe304,
        "CONDSELCHK" => 0xe305,
        "IFRETALT" => 0xe308,
        "IFNOTRETALT" => 0xe309,
        "IFREFELSE" => 0xe30d(ref),
        "IFELSEREF" => 0xe30e(ref),
        "IFREFELSEREF" => 0xe30f(ref, ref),

        "REPEATBRK" => 0xe314,
        "REPEATENDBRK" => 0xe315,
        "UNTILBRK" => 0xe316,
        "UNTILENDBRK" => 0xe317,
        "WHILEBRK" => 0xe318,
        "WHILEENDBRK" => 0xe319,
        "AGAINBRK" => 0xe31a,
        "AGAINENDBRK" => 0xe31b,

        "IFBITJMP" => op_ifbitjmp,
        "IFNBITJMP" => op_ifnbitjmp,
        "IFBITJMPREF" => op_ifbitjmpref,
        "IFNBITJMPREF" => op_ifnbitjmpref,

        "REPEAT" => 0xe4,
        "REPEATEND" => 0xe5,
        "UNTIL" => 0xe6,
        "UNTILEND" => 0xe7,
        "WHILE" => 0xe8,
        "WHILEEND" => 0xe9,
        "AGAIN" => 0xea,
        "AGAINEND" => 0xeb,

        // Continuation stack manipulation and continuation creation
        // TODO: SETCONTARGS
        // TODO: SETNUMARGS
        "RETURNARGS" => 0xed0(u4),
        "RETURNVARARGS" => 0xed10,
        "SETCONTVARARGS" => 0xed11,
        "SETNUMVARARGS" => 0xed12,
        "BLESS" => 0xed1e,
        "BLESSVARARGS" => 0xed1f,
        // TODO: BLESSARGS
        // TODO: BLESSNUMARGS

        // Control register and continuation savelist manipulation
        "PUSHCTR" => 0xed4(c),
        "PUSHROOT" => 0xed44,
        "POPCTR" => 0xed5(c),
        "POPROOT" => 0xed54,
        "SETCONTCTR" | "SETCONT" => 0xed6(c),
        "SETRETCTR" => 0xed7(c),
        "SETALTCTR" => 0xed8(c),
        "POPSAVE" | "POPCTRSAVE" => 0xed9(c),
        "SAVE" | "SAVECTR" => 0xeda(c),
        "SAVEALT" | "SAVEALTCTR" => 0xedb(c),
        "SAVEBOTH" | "SAVEBOTHCTR" => 0xedc(c),
        "PUSHCTRX" => 0xede0,
        "POPCTRX" => 0xede1,
        "SETCONTCTRX" => 0xede2,
        "BOOLAND" | "COMPOS" => 0xedf0,
        "BOOLOR" | "COMPOSALT" => 0xedf1,
        "COMPOSBOTH" => 0xedf2,
        "ATEXIT" => 0xedf3,
        "ATEXITALT" => 0xedf4,
        "SETEXITALT" => 0xedf5,
        "THENRET" => 0xedf6,
        "THENRETALT" => 0xedf7,
        "INVERT" => 0xedf8,
        "BOOLEVAL" => 0xedf9,
        "SAMEALT" => 0xedfa,
        "SAMEALTSAVE" => 0xedfb,

        // Dictionary subroutine call/jump primitives
        "CALLVAR" => op_callvar,
        "JMPVAR" => op_jmpvar,
        "PREPAREVAR" => op_preparevar,
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
        Either::Right(CReg(c)) => ctx.get_builder(16).store_u16(0xed50 | c as u16),
    }
    .map_err(AsmError::StoreError)
}

fn op_index2(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    let (NatU2(s1), NatU2(s2)) = args.parse()?;
    write_op_1sr_l(ctx, 0x6fb, 12, (s1 << 2) | s2)
}

fn op_index3(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    let (NatU2(s1), NatU2(s2), NatU2(s3)) = args.parse()?;
    let args = (s1 << 4) | (s2 << 2) | s3;
    ctx.get_builder(16)
        .store_uint(0x6fc0 | args as u64, 16)
        .map_err(AsmError::StoreError)
}

fn op_pushint(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    let Nat(n) = args.parse()?;
    write_pushint(ctx, n)
}

fn write_pushint(ctx: &mut Context<'_>, n: &BigInt) -> Result<(), AsmError> {
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

fn op_pushintx(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    let Nat(n) = args.parse()?;
    let bitsize = bitsize(n);

    if bitsize <= 8 {
        // NOTE: base=1 && pow2=0 case will be handled here
        return op_pushint(ctx, args);
    } else if bitsize > 257 {
        return Err(AsmError::OutOfRange);
    }

    // NOTE: `n` is never zero at this point
    let pow2 = n.trailing_zeros().unwrap();
    let base = n >> pow2;
    if base.magnitude().is_one() {
        // NOTE: `pow2` is never zero at this point
        let b = ctx.get_builder(16);
        b.store_u8(if base.sign() == Sign::Plus {
            0x83 // PUSHPOW2
        } else {
            0x85 // PUSHNEGPOW2
        })?;
        b.store_u8((pow2 - 1) as _).map_err(AsmError::StoreError)
    } else if pow2 >= 20 {
        // PUSHINT base
        write_pushint(ctx, &base)?;
        // LSHIFT# pow2
        write_op_1sr_l(ctx, 0xaa, 8, (pow2 - 1) as _)
    } else {
        if pow2 == 0 {
            let mut base = !n;
            let pow2 = base.trailing_zeros().unwrap();
            base >>= pow2;
            if base.sign() == Sign::Minus && base.magnitude().is_one() {
                // PUSHPOW2DEC
                return write_op_1sr_l(ctx, 0x84, 8, (pow2 - 1) as _);
            }
        }

        // Fallback to PUSHINT
        write_pushint(ctx, n)
    }
}

fn op_pushslice(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    const MAX_BITS_OVERHEAD: u16 = 26; // Longest prefix/padding

    let SliceOrCont(c) = args.parse()?;
    let bits = c.bit_len();
    let refs = c.reference_count();

    let (rem_bits, rem_refs) = ctx.top_capacity();
    if bits + MAX_BITS_OVERHEAD > rem_bits || refs + 1 > rem_refs {
        // Fallback to PUSHREFSLICE
        let (b, _) = ctx.get_builder_ext(8, 2);
        b.store_u8(0x89)?;
        b.store_reference(c).map_err(AsmError::StoreError)
    } else if bits <= 123 && refs == 0 {
        let l = (bits + 4) / 8;
        let padding = l * 8 + 4 - bits;
        let (b, _) = ctx.get_builder_ext(8 + 4 + bits + padding, refs + 1);
        b.store_u8(0x8b)?;
        b.store_small_uint(l as u8, 4)?;
        b.store_slice(c.as_slice()?)?;
        write_slice_padding(padding, b)
    } else if bits <= 248 && refs >= 1 {
        let l = (bits + 7) / 8;
        let padding = l * 8 + 1 - bits;
        let (b, _) = ctx.get_builder_ext(8 + 2 + 5 + bits + padding, refs + 1);
        b.store_u8(0x8c)?;
        b.store_small_uint(refs - 1, 2)?;
        b.store_small_uint(l as u8, 5)?;
        b.store_slice(c.as_slice()?)?;
        write_slice_padding(padding, b)
    } else {
        let l = (bits + 2) / 8;
        let padding = l * 8 + 6 - bits;
        let (b, _) = ctx.get_builder_ext(8 + 3 + 7 + bits + padding, refs + 1);
        b.store_u8(0x8d)?;
        b.store_small_uint(refs, 3)?;
        b.store_small_uint(l as u8, 7)?;
        b.store_slice(c.as_slice()?)?;
        write_slice_padding(padding, b)
    }
}

fn op_pldrefidx(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    let NatU2(s) = args.parse()?;
    ctx.get_builder(16)
        .store_u16(0xd74c | s as u16)
        .map_err(AsmError::StoreError)
}

fn op_ifbitjmp(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    op_ifbitjmp_impl::<false>(ctx, args)
}

fn op_ifnbitjmp(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    op_ifbitjmp_impl::<true>(ctx, args)
}

fn op_ifbitjmp_impl<const INV: bool>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let NatU5(s) = args.parse()?;
    ctx.get_builder(16)
        .store_u16(0xe380 | (0x20 * INV as u16) | s as u16)
        .map_err(AsmError::StoreError)
}

fn op_ifbitjmpref(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    op_ifbitjmpref_impl::<false>(ctx, args)
}

fn op_ifnbitjmpref(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    op_ifbitjmpref_impl::<true>(ctx, args)
}

fn op_ifbitjmpref_impl<const INV: bool>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let (NatU5(s), SliceOrCont(c)) = args.parse()?;
    let (b, _) = ctx.get_builder_ext(16, 2);
    b.store_u16(0xe39c | (0x20 * INV as u16) | s as u16)?;
    b.store_reference(c).map_err(AsmError::StoreError)
}

fn op_callvar(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    // PUSH c3
    op_preparevar(ctx, args)?;
    // EXECUTE
    write_op(ctx, 0xd8, 8)
}

fn op_jmpvar(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    // PUSH c3
    op_preparevar(ctx, args)?;
    // JMPX
    write_op(ctx, 0xd9, 8)
}

fn op_preparevar(ctx: &mut Context<'_>, args: &[ast::InstrArg<'_>]) -> Result<(), AsmError> {
    args.parse::<()>()?;
    // PUSH c3
    write_op_1sr(ctx, 0xed4, 12, 3)
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

fn op_1ref<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let SliceOrCont(c) = args.parse()?;
    write_op_1ref(ctx, BASE, BITS, c)
}

fn op_2ref<const BASE: u32, const BITS: u16>(
    ctx: &mut Context<'_>,
    args: &[ast::InstrArg<'_>],
) -> Result<(), AsmError> {
    let (SliceOrCont(c1), SliceOrCont(c2)) = args.parse()?;
    write_op_2ref(ctx, BASE, BITS, c1, c2)
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

fn write_op_1ref(ctx: &mut Context<'_>, base: u32, bits: u16, r: Cell) -> Result<(), AsmError> {
    let (b, _) = ctx.get_builder_ext(bits, 2);
    b.store_uint(base as _, bits)?;
    b.store_reference(r).map_err(AsmError::StoreError)
}

fn write_op_2ref(
    ctx: &mut Context<'_>,
    base: u32,
    bits: u16,
    r1: Cell,
    r2: Cell,
) -> Result<(), AsmError> {
    let (b, _) = ctx.get_builder_ext(bits, 3);
    b.store_uint(base as _, bits)?;
    b.store_reference(r1)?;
    b.store_reference(r2).map_err(AsmError::StoreError)
}

fn write_slice_padding(padding: u16, b: &mut CellBuilder) -> Result<(), AsmError> {
    debug_assert!((1..=8).contains(&padding), "Invalid slice padding");
    b.store_bit_one()?;
    b.store_zeros(padding - 1)?;
    Ok(())
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
    fn pushintx() -> anyhow::Result<()> {
        let cell_tiny = Code::new("INTX 7")?.assemble()?;
        assert_eq!(cell_tiny.data(), &[0x77]);

        let cell_byte = Code::new("INTX 120")?.assemble()?;
        assert_eq!(cell_byte.data(), &[0x80, 120]);

        let cell_short = Code::new("INTX 16000")?.assemble()?;
        assert_eq!(
            cell_short.data(),
            &[0x81, ((16000 >> 8) & 0xff) as u8, ((16000) & 0xff) as u8]
        );

        let cell_big = Code::new("INTX 123123123123123123")?.assemble()?;
        assert_eq!(cell_big.data(), hex::decode("8229b56bd40163f3b3")?);

        let cell_big = Code::new("INTX 90596966400")?.assemble()?;
        assert_eq!(cell_big.data(), hex::decode("8102a3aa1a")?);

        let cell_max =
            Code::new("INTX 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")?
                .assemble()?;
        assert_eq!(cell_max.data(), hex::decode("84ff")?);

        let cell_neg_max =
            Code::new("INTX -0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")?
                .assemble()?;
        assert_eq!(
            cell_neg_max.data(),
            hex::decode("82f70000000000000000000000000000000000000000000000000000000000000001")?
        );

        Ok(())
    }

    #[test]
    fn display() -> anyhow::Result<()> {
        let code = Code::new("PUSHSLICE x{6_}")?.assemble()?;
        println!("{}", code.display_tree());
        Ok(())
    }
}
