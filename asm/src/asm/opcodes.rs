use std::cmp::Ordering;
use std::collections::hash_map;
use std::sync::OnceLock;

use ahash::HashMap;
use either::Either;
use num_bigint::{BigInt, Sign};
use num_traits::{One, ToPrimitive};
use tycho_types::cell::{MAX_BIT_LEN, MAX_REF_COUNT};
use tycho_types::error::Error;
use tycho_types::prelude::*;

use super::{ArgType, JoinResults};
use crate::asm::AsmError;
use crate::asm::util::*;
use crate::ast;
use crate::util::*;

pub struct Scope<'c, 's> {
    parent: Option<&'c Scope<'c, 's>>,
    defines: HashMap<&'s str, &'c ast::InstrArg<'s>>,
}

impl<'c, 's> Scope<'c, 's> {
    pub fn new() -> Self {
        Scope {
            parent: None,
            defines: Default::default(),
        }
    }

    pub fn define(&mut self, op: &'c ast::Define<'s>) -> Result<(), AsmError> {
        if let Some(parent) = self.parent {
            if parent.resolve_use_raw(op.name.name).is_some() {
                return Err(AsmError::RedefinedVariable(op.name.span));
            }
        }

        match self.defines.entry(op.name.name) {
            hash_map::Entry::Vacant(entry) => {
                if let ast::InstrArgValue::Use(value) = &op.value.value {
                    return Err(AsmError::WrongUsage {
                        details: "creating aliases this way is not supported",
                        span: value.span,
                    });
                }
                entry.insert(&op.value);
                Ok(())
            }
            hash_map::Entry::Occupied(_) => Err(AsmError::RedefinedVariable(op.name.span)),
        }
    }

    pub fn make_child_scope<'n: 'c>(&'n self) -> Scope<'n, 's> {
        Self {
            parent: Some(self),
            defines: Default::default(),
        }
    }

    #[must_use = "resolved argument is returned as result of this method"]
    pub fn resolve_arg_once<'a, 'b: 'a>(
        &'a self,
        arg: &'b ast::InstrArg<'s>,
    ) -> Result<&'a ast::InstrArg<'s>, AsmError> {
        if let ast::InstrArgValue::Use(u) = &arg.value {
            match self.resolve_use_raw(u.value.name) {
                Some(value) => return Ok(value),
                None => return Err(AsmError::UndefinedVariable(u.value.span)),
            }
        }
        Ok(arg)
    }

    pub fn resolve_use_raw<'a>(&'a self, name: &str) -> Option<&'a ast::InstrArg<'s>> {
        let mut this = Some(self);
        while let Some(ctx) = this {
            if let Some(value) = ctx.defines.get(name) {
                return Some(*value);
            }
            this = ctx.parent;
        }
        None
    }
}

#[derive(Default)]
pub struct Context {
    stack: Vec<StackItem>,
    allow_invalid: bool,
}

struct StackItem {
    inline: bool,
    value: CellBuilder,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set_allow_invalid(&mut self) {
        self.allow_invalid = true;
    }

    pub fn make_child_context(&self) -> Context {
        Self {
            stack: Default::default(),
            allow_invalid: self.allow_invalid,
        }
    }

    pub fn add_stmt<'i: 'c, 'c, 's>(
        &mut self,
        opcodes: &Opcodes,
        stmt: &'i ast::Stmt<'s>,
        scope: &'c mut Scope<'i, 's>,
    ) -> Result<(), AsmError> {
        match stmt {
            ast::Stmt::Inline(inline) => {
                let Slice(slice) = inline.parse_args(scope)?;
                self.get_builder(slice.bit_len())
                    .store_cell_data(slice)
                    .with_span(inline.span)
            }
            ast::Stmt::NewCell(_) => {
                self.stack.push(StackItem {
                    inline: false,
                    value: Default::default(),
                });
                Ok(())
            }
            ast::Stmt::Instr(instr) => {
                let Some(handler) = opcodes.get(instr.ident) else {
                    return Err(AsmError::UnknownOpcode {
                        name: instr.ident.into(),
                        span: instr.ident_span,
                    });
                };
                (handler)(self, instr, scope)
            }
            ast::Stmt::Define(define) => scope.define(define),
            ast::Stmt::Invalid(span) => Err(AsmError::InvalidStatement(*span)),
        }
    }

    pub fn into_builder(self, block_span: ast::Span) -> Result<CellBuilder, AsmError> {
        Self::merge_stack(self.stack, block_span)
    }

    fn get_builder(&mut self, bits: u16) -> &mut CellBuilder {
        // NOTE: always reserve the last cell for the code
        self.get_builder_ext(bits, 1)
    }

    fn get_builder_ext(&mut self, bits: u16, refs: u8) -> &mut CellBuilder {
        'last: {
            if let Some(last) = self.stack.last() {
                if last.value.has_capacity(bits, refs) {
                    break 'last;
                }
            }
            self.stack.push(StackItem {
                inline: true,
                value: Default::default(),
            });
        };
        &mut self.stack.last_mut().unwrap().value
    }

    fn top_capacity(&self) -> (u16, u8) {
        match self.stack.last() {
            Some(StackItem { value, .. }) => {
                (value.spare_capacity_bits(), value.spare_capacity_refs())
            }
            None => (MAX_BIT_LEN, MAX_REF_COUNT as u8),
        }
    }

    fn merge_stack(
        mut stack: Vec<StackItem>,
        block_span: ast::Span,
    ) -> Result<CellBuilder, AsmError> {
        let cell_context = Cell::empty_context();
        let mut result = None::<StackItem>;
        while let Some(mut last) = stack.pop() {
            let StackItem { value, .. } = &mut last;

            if let Some(StackItem {
                value: child,
                inline,
            }) = result.take()
            {
                if inline && value.has_capacity(child.size_bits(), child.size_refs()) {
                    value.store_slice(child.as_full_slice())
                } else {
                    value.store_reference(child.build_ext(cell_context).with_span(block_span)?)
                }
                .with_span(block_span)?;
            }
            result = Some(last);
        }

        Ok(match result {
            Some(StackItem { value, .. }) => value,
            None => CellBuilder::new(),
        })
    }
}

pub type Opcodes = HashMap<&'static str, OpcodeHandlerFn>;
pub type OpcodeHandlerFn =
    for<'c, 's> fn(&mut Context, &ast::Instr<'s>, &mut Scope<'c, 's>) -> Result<(), AsmError>;

pub fn cp0() -> &'static Opcodes {
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
        (@args $t:ident $($names:literal)|+ $base:literal u8) => {
            $($t.insert(
                $names,
                op_u8::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal u8 - 1) => {
            $($t.insert(
                $names,
                op_u8_minus1::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal i8) => {
            $($t.insert(
                $names,
                op_i8::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
            ));+
        };
        (@args $t:ident $($names:literal)|+ $base:literal u12) => {
            $($t.insert(
                $names,
                op_u12::<$base, { (stringify!($base).len() - 2) as u16 * 4 }>,
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
        "XCHG3_L" => 0x540(s, s, s),
        "XC2PU" => 0x541(s, s, s),
        "XCPUXC" => 0x542(s, s, s, adj = 0x001),
        "XCPU2" => 0x543(s, s, s),
        "PUXC2" => 0x544(s, s, s, adj = 0x011),
        "PUXCPU" => 0x545(s, s, s, adj = 0x011),
        "PU2XC" => 0x546(s, s, s, adj = 0x012),
        "PUSH3" => 0x547(s, s, s),
        "BLKSWAP" => op_blkswap,
        "ROLL" => op_roll,
        "-ROLL" | "ROLLREV" => op_rollrev,
        "2ROT" | "ROT2" => 0x5513,

        // Exotic stack primitives
        "ROT" => 0x58,
        "-ROT" | "ROTREV" => 0x59,
        "2SWAP" | "SWAP2" => 0x5a,
        "2DROP" | "DROP2" => 0x5b,
        "2DUP" | "DUP2" => 0x5c,
        "2OVER" | "OVER2" => 0x5d,
        "REVERSE" => op_reverse,
        "BLKDROP" => 0x5f0(u4),
        "BLKPUSH" => op_blkpush,
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
        "BLKDROP2" => op_blkdrop2,

        // Null primitives
        "NULL" | "PUSHNULL" | "NEWDICT" => 0x6d,
        "ISNULL" | "DICTEMPTY" => 0x6e,
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
        "PUSHCONT" | "CONT" => op_pushcont,

        // Arithmetic operations
        "ADD" => 0xa0,
        "SUB" => 0xa1,
        "SUBR" => 0xa2,
        "NEGATE" => 0xa3,
        "INC" => 0xa4,
        "DEC" => 0xa5,
        "ADDCONST" | "ADDINT" => 0xa6(i8),
        "SUBCONST" | "SUBINT" => op_subconst,
        "MULCONST" | "MULINT" => 0xa7(i8),
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
        "ADDDIVMOD" => 0xa900,
        "ADDDIVMODR" => 0xa901,
        "ADDDIVMODC" => 0xa902,

        "RSHIFTR" => 0xa925,
        "RSHIFTC" => 0xa926,
        "MODPOW2" => 0xa928,
        "MODPOW2R" => 0xa929,
        "MODPOW2C" => 0xa92a,
        "RSHIFTMOD" => 0xa92c,
        "RSHIFTMODR" => 0xa92d,
        "RSHIFTMODC" => 0xa92e,
        "ADDRSHIFTMOD" => 0xa920,
        "ADDRSHIFTMODR" => 0xa921,
        "ADDRSHIFTMODC" => 0xa922,

        "RSHIFTR#" => 0xa935(u8 - 1),
        "RSHIFTC#" => 0xa936(u8 - 1),
        "MODPOW2#" => 0xa938(u8 - 1),
        "MODPOW2R#" => 0xa939(u8 - 1),
        "MODPOW2C#" => 0xa93a(u8 - 1),
        "RSHIFT#MOD" => 0xa93c(u8 - 1),
        "RSHIFTR#MOD" => 0xa93d(u8 - 1),
        "RSHIFTC#MOD" => 0xa93e(u8 - 1),
        "ADDRSHIFT#MOD" => 0xa930(u8 - 1),
        "ADDRSHIFTR#MOD" => 0xa931(u8 - 1),
        "ADDRSHIFTC#MOD" => 0xa932(u8 - 1),

        "MULDIV" => 0xa984,
        "MULDIVR" => 0xa985,
        "MULDIVC" => 0xa986,
        "MULMOD" => 0xa988,
        "MULMODR" => 0xa989,
        "MULMODC" => 0xa98a,
        "MULDIVMOD" => 0xa98c,
        "MULDIVMODR" => 0xa98d,
        "MULDIVMODC" => 0xa98e,
        "MULADDDIVMOD" => 0xa980,
        "MULADDDIVMODR" => 0xa981,
        "MULADDDIVMODC" => 0xa982,

        "MULRSHIFT" => 0xa9a4,
        "MULRSHIFTR" => 0xa9a5,
        "MULRSHIFTC" => 0xa9a6,
        "MULMODPOW2" => 0xa9a8,
        "MULMODPOW2R" => 0xa9a9,
        "MULMODPOW2C" => 0xa9aa,
        "MULRSHIFTMOD" => 0xa9ac,
        "MULRSHIFTRMOD" => 0xa9ad,
        "MULRSHIFTCMOD" => 0xa9ae,
        "MULADDRSHIFTMOD" => 0xa9a0,
        "MULADDRSHIFTRMOD" => 0xa9a1,
        "MULADDRSHIFTCMOD" => 0xa9a2,

        "MULRSHIFT#" => 0xa9b4(u8 - 1),
        "MULRSHIFTR#" => 0xa9b5(u8 - 1),
        "MULRSHIFTC#" => 0xa9b6(u8 - 1),
        "MULMODPOW2#" => 0xa9b8(u8 - 1),
        "MULMODPOW2R#" => 0xa9b9(u8 - 1),
        "MULMODPOW2C#" => 0xa9ba(u8 - 1),
        "MULRSHIFT#MOD" => 0xa9bc(u8 - 1),
        "MULRSHIFTR#MOD" => 0xa9bd(u8 - 1),
        "MULRSHIFTC#MOD" => 0xa9be(u8 - 1),
        "MULADDRSHIFT#MOD" => 0xa9b0(u8 - 1),
        "MULADDRSHIFTR#MOD" => 0xa9b1(u8 - 1),
        "MULADDRSHIFTC#MOD" => 0xa9b2(u8 - 1),

        "LSHIFTDIV" => 0xa9c4,
        "LSHIFTDIVR" => 0xa9c5,
        "LSHIFTDIVC" => 0xa9c6,
        "LSHIFTMOD" => 0xa9c8,
        "LSHIFTMODR" => 0xa9c9,
        "LSHIFTMODC" => 0xa9ca,
        "LSHIFTDIVMOD" => 0xa9cc,
        "LSHIFTDIVMODR" => 0xa9cd,
        "LSHIFTDIVMODC" => 0xa9ce,
        "LSHIFTADDDIVMOD" => 0xa9c0,
        "LSHIFTADDDIVMODR" => 0xa9c1,
        "LSHIFTADDDIVMODC" => 0xa9c2,

        "LSHIFT#DIV" => 0xa9d4(u8 - 1),
        "LSHIFT#DIVR" => 0xa9d5(u8 - 1),
        "LSHIFT#DIVC" => 0xa9d6(u8 - 1),
        "LSHIFT#MOD" => 0xa9d8(u8 - 1),
        "LSHIFT#MODR" => 0xa9d9(u8 - 1),
        "LSHIFT#MODC" => 0xa9da(u8 - 1),
        "LSHIFT#DIVMOD" => 0xa9dc(u8 - 1),
        "LSHIFT#DIVMODR" => 0xa9dd(u8 - 1),
        "LSHIFT#DIVMODC" => 0xa9de(u8 - 1),
        "LSHIFT#ADDDIVMOD" => 0xa9d0(u8 - 1),
        "LSHIFT#ADDDIVMODR" => 0xa9d1(u8 - 1),
        "LSHIFT#ADDDIVMODC" => 0xa9d2(u8 - 1),

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
        "QADDCONST" | "QADDINT" => 0xb7a6(i8),
        "QMULCONST" | "QMULINT" => 0xb7a7(i8),
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
        "EQINT" => 0xc0(i8),
        "ISZERO" => 0xc000,
        "LESSINT" => 0xc1(i8),
        "ISNEG" => 0xc100,
        "ISNPOS" => 0xc101,
        "GTINT" => 0xc2(i8),
        "ISPOS" => 0xc200,
        "ISNNEG" => 0xc2ff,
        "NEQINT" => 0xc3(i8),
        "ISNZERO" => 0xc300,
        "ISNAN" => 0xc4,
        "CHKNAN" => 0xc5,

        "QSGN" => 0xb7b8,
        "QLESS" => 0xb7b9,
        "QEQUAL" => 0xb7ba,
        "QLEQ" => 0xb7bb,
        "QGREATER" => 0xb7bc,
        "QNEQ" => 0xb7bd,
        "QGEQ" => 0xb7be,
        "QCMP" => 0xb7bf,
        "QEQINT" => 0xb7c0(i8),
        "QLESSINT" => 0xb7c1(i8),
        "QGTINT" => 0xb7c2(i8),
        "QNEQINT" => 0xb7c3(i8),

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
        "STSLICE" | "STDICTS" => 0xce,
        "STIX" => 0xcf00,
        "STUX" => 0xcf01,
        "STIXR" => 0xcf02,
        "STUXR" => 0xcf03,
        "STIXQ" => 0xcf04,
        "STUXQ" => 0xcf05,
        "STIXRQ" => 0xcf06,
        "STUXRQ" => 0xcf07,
        "STI_L" => 0xcf08(u8 - 1),
        "STU_L" => 0xcf09(u8 - 1),
        "STIR" => 0xcf0a(u8 - 1),
        "STUR" => 0xcf0b(u8 - 1),
        "STIQ" => 0xcf0c(u8 - 1),
        "STUQ" => 0xcf0d(u8 - 1),
        "STIRQ" => 0xcf0e(u8 - 1),
        "STURQ" => 0xcf0f(u8 - 1),
        "STREF_L" => 0xcf10,
        "STBREF" => 0xcf11,
        "STSLICE_L" => 0xcf12,
        "STB" => 0xcf13,
        "STREFR" => 0xcf14,
        "STBREFR_L" => 0xcf15,
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
        "STSLICECONST" => op_stsliceconst,
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
        "LDI_L" => 0xd708(u8 - 1),
        "LDU_L" => 0xd709(u8 - 1),
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
        "LDSLICE_L" => 0xd71c(u8 - 1),
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
        "CALLXARGS" => op_callxargs,
        "JMPXARGS" => 0xdb1(u4),
        "RETARGS" => 0xdb2(u4),
        "RET" | "RETTRUE" => 0xdb30,
        "RETALT" | "RETFALSE" => 0xdb31,
        "BRANCH" | "RETBOOL" => 0xdb32,
        "CALLCC" => 0xdb34,
        "JMPXDATA" => 0xdb35,
        "CALLCCARGS" => op_callccargs,
        "CALLXVARARGS" => 0xdb38,
        "RETVARARGS" => 0xdb39,
        "JMPXVARARGS" => 0xdb3a,
        "CALLCCVARARGS" => 0xdb3b,
        "CALLREF" => 0xdb3c(ref),
        "JMPREF" => 0xdb3d(ref),
        "JMPREFDATA" => 0xdb3e(ref),
        "RETDATA" => 0xdb3f,

        "RUNVM" => 0xdb4(u12),
        "RUNVMX" => 0xdb50,

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
        "SETCONTARGS" => op_setcontargs,
        "SETNUMARGS" => op_setnumargs,
        "RETURNARGS" => 0xed0(u4),
        "RETURNVARARGS" => 0xed10,
        "SETCONTVARARGS" => 0xed11,
        "SETNUMVARARGS" => 0xed12,
        "BLESS" => 0xed1e,
        "BLESSVARARGS" => 0xed1f,
        "BLESSARGS" => op_blessargs,
        "BLESSNUMARGS" => op_blessnumargs,

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
        "SETCONTCTRMANY" | "SETCONTMANY" => 0xede3(u8),
        "SETCONTCTRMANYX" | "SETCONTMANYX" => 0xede4,
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
        "CALL" | "CALLDICT" => op_call,
        "JMP" | "JMPDICT" => op_jmp,
        "PREPARE" | "PREPAREDICT" => op_prepare,

        "THROW" => op_throw,
        "THROWIF" => op_throwif,
        "THROWIFNOT" => op_throwifnot,
        "THROWARG" => op_throwarg,
        "THROWARGIF" => op_throwargif,
        "THROWARGIFNOT" => op_throwargifnot,

        "THROWANY" => 0xf2f0,
        "THROWARGANY" => 0xf2f1,
        "THROWANYIF" => 0xf2f2,
        "THROWARGANYIF" => 0xf2f3,
        "THROWANYIFNOT" => 0xf2f4,
        "THROWARGANYIFNOT" => 0xf2f5,
        "TRY" => 0xf2ff,
        "TRYARGS" => op_tryargs,

        // Dictionary manipulation
        "STDICT" | "STOPTREF" => 0xf400,
        "SKIPDICT" | "SKIPOPTREF" => 0xf401,
        "LDDICTS" => 0xf402,
        "PLDDICTS" => 0xf403,
        "LDDICT" | "LDOPTREF" => 0xf404,
        "PLDDICT" | "PLDOPTREF" => 0xf405,
        "LDDICTQ" => 0xf406,
        "PLDDICTQ" => 0xf407,

        "DICTGET" => 0xf40a,
        "DICTGETREF" => 0xf40b,
        "DICTIGET" => 0xf40c,
        "DICTIGETREF" => 0xf40d,
        "DICTUGET" => 0xf40e,
        "DICTUGETREF" => 0xf40f,

        "DICTSET" => 0xf412,
        "DICTSETREF" => 0xf413,
        "DICTISET" => 0xf414,
        "DICTISETREF" => 0xf415,
        "DICTUSET" => 0xf416,
        "DICTUSETREF" => 0xf417,
        "DICTSETGET" => 0xf41a,
        "DICTSETGETREF" => 0xf41b,
        "DICTISETGET" => 0xf41c,
        "DICTISETGETREF" => 0xf41d,
        "DICTUSETGET" => 0xf41e,
        "DICTUSETGETREF" => 0xf41f,

        "DICTREPLACE" => 0xf422,
        "DICTREPLACEREF" => 0xf423,
        "DICTIREPLACE" => 0xf424,
        "DICTIREPLACEREF" => 0xf425,
        "DICTUREPLACE" => 0xf426,
        "DICTUREPLACEREF" => 0xf427,
        "DICTREPLACEGET" => 0xf42a,
        "DICTREPLACEGETREF" => 0xf42b,
        "DICTIREPLACEGET" => 0xf42c,
        "DICTIREPLACEGETREF" => 0xf42d,
        "DICTUREPLACEGET" => 0xf42e,
        "DICTUREPLACEGETREF" => 0xf42f,

        "DICTADD" => 0xf432,
        "DICTADDREF" => 0xf433,
        "DICTIADD" => 0xf434,
        "DICTIADDREF" => 0xf435,
        "DICTUADD" => 0xf436,
        "DICTUADDREF" => 0xf437,
        "DICTADDGET" => 0xf43a,
        "DICTADDGETREF" => 0xf43b,
        "DICTIADDGET" => 0xf43c,
        "DICTIADDGETREF" => 0xf43d,
        "DICTUADDGET" => 0xf43e,
        "DICTUADDGETREF" => 0xf43f,

        "DICTSETB" => 0xf441,
        "DICTISETB" => 0xf442,
        "DICTUSETB" => 0xf443,
        "DICTSETGETB" => 0xf445,
        "DICTISETGETB" => 0xf446,
        "DICTUSETGETB" => 0xf447,

        "DICTREPLACEB" => 0xf449,
        "DICTIREPLACEB" => 0xf44a,
        "DICTUREPLACEB" => 0xf44b,
        "DICTREPLACEGETB" => 0xf44d,
        "DICTIREPLACEGETB" => 0xf44e,
        "DICTUREPLACEGETB" => 0xf44f,

        "DICTADDB" => 0xf451,
        "DICTIADDB" => 0xf452,
        "DICTUADDB" => 0xf453,
        "DICTADDGETB" => 0xf455,
        "DICTIADDGETB" => 0xf456,
        "DICTUADDGETB" => 0xf457,

        "DICTDEL" => 0xf459,
        "DICTIDEL" => 0xf45a,
        "DICTUDEL" => 0xf45b,

        "DICTDELGET" => 0xf462,
        "DICTDELGETREF" => 0xf463,
        "DICTIDELGET" => 0xf464,
        "DICTIDELGETREF" => 0xf465,
        "DICTUDELGET" => 0xf466,
        "DICTUDELGETREF" => 0xf467,

        "DICTGETOPTREF" => 0xf469,
        "DICTIGETOPTREF" => 0xf46a,
        "DICTUGETOPTREF" => 0xf46b,
        "DICTSETGETOPTREF" => 0xf46d,
        "DICTISETGETOPTREF" => 0xf46e,
        "DICTUSETGETOPTREF" => 0xf46f,

        "PFXDICTSET" => 0xf470,
        "PFXDICTREPLACE" => 0xf471,
        "PFXDICTADD" => 0xf472,
        "PFXDICTDEL" => 0xf473,

        "DICTGETNEXT" => 0xf474,
        "DICTGETNEXTEQ" => 0xf475,
        "DICTGETPREV" => 0xf476,
        "DICTGETPREVEQ" => 0xf477,
        "DICTIGETNEXT" => 0xf478,
        "DICTIGETNEXTEQ" => 0xf479,
        "DICTIGETPREV" => 0xf47a,
        "DICTIGETPREVEQ" => 0xf47b,
        "DICTUGETNEXT" => 0xf47c,
        "DICTUGETNEXTEQ" => 0xf47d,
        "DICTUGETPREV" => 0xf47e,
        "DICTUGETPREVEQ" => 0xf47f,

        "DICTMIN" => 0xf482,
        "DICTMINREF" => 0xf483,
        "DICTIMIN" => 0xf484,
        "DICTIMINREF" => 0xf485,
        "DICTUMIN" => 0xf486,
        "DICTUMINREF" => 0xf487,
        "DICTMAX" => 0xf48a,
        "DICTMAXREF" => 0xf48b,
        "DICTIMAX" => 0xf48c,
        "DICTIMAXREF" => 0xf48d,
        "DICTUMAX" => 0xf48e,
        "DICTUMAXREF" => 0xf48f,

        "DICTREMMIN" => 0xf492,
        "DICTREMMINREF" => 0xf493,
        "DICTIREMMIN" => 0xf494,
        "DICTIREMMINREF" => 0xf495,
        "DICTUREMMIN" => 0xf496,
        "DICTUREMMINREF" => 0xf497,
        "DICTREMMAX" => 0xf49a,
        "DICTREMMAXREF" => 0xf49b,
        "DICTIREMMAX" => 0xf49c,
        "DICTIREMMAXREF" => 0xf49d,
        "DICTUREMMAX" => 0xf49e,
        "DICTUREMMAXREF" => 0xf49f,

        "DICTIGETJMP" => 0xf4a0,
        "DICTUGETJMP" => 0xf4a1,
        "DICTIGETEXEC" => 0xf4a2,
        "DICTUGETEXEC" => 0xf4a3,

        "DICTPUSHCONST" => op_dictpushconst,

        "PFXDICTGETQ" => 0xf4a8,
        "PFXDICTGET" => 0xf4a9,
        "PFXDICTGETJMP" => 0xf4aa,
        "PFXDICTGETEXEC" => 0xf4ab,
        // TODO: "PFXDICTCONSTGETJMP" | "PFXDICTSWITCH"

        "SUBDICTGET" => 0xf4b1,
        "SUBDICTIGET" => 0xf4b2,
        "SUBDICTUGET" => 0xf4b3,
        "SUBDICTRPGET" => 0xf4b5,
        "SUBDICTIRPGET" => 0xf4b6,
        "SUBDICTURPGET" => 0xf4b7,

        "DICTIGETJMPZ" => 0xf4bc,
        "DICTUGETJMPZ" => 0xf4bd,
        "DICTIGETEXECZ" => 0xf4be,
        "DICTUGETEXECZ" => 0xf4bf,

        // Blockchain-specific primitives
        "ACCEPT" => 0xf800,
        "SETGASLIMIT" => 0xf801,
        "BUYGAS" => 0xf802,
        "GRAMTOGAS" => 0xf804,
        "GASTOGRAM" => 0xf805,
        "GASREMAINING" => 0xf806,
        "GASCONSUMED" => 0xf807,
        "COMMIT" => 0xf80f,

        "RANDU256" => 0xf810,
        "RAND" => 0xf811,
        "SETRAND" => 0xf814,
        "ADDRAND" | "RANDOMIZE" => 0xf815,

        "GETPARAM" => 0xf82(u4),
        "NOW" => 0xf823,
        "BLOCKLT" => 0xf824,
        "LTIME" => 0xf825,
        "RANDSEED" => 0xf826,
        "BALANCE" => 0xf827,
        "MYADDR" => 0xf828,
        "CONFIGROOT" => 0xf829,
        "MYCODE" => 0xf82a,
        "INITCODEHASH" => 0xf82b,
        "STORAGEFEE" => 0xf82c,
        "SEQNO" => 0xf82d,
        "CONFIGDICT" => 0xf830,
        "CONFIGPARAM" => 0xf832,
        "CONFIGOPTPARAM" => 0xf833,

        "GETGLOBVAR" => 0xf840,
        "GETGLOB" => op_getglob,
        "SETGLOBVAR" => 0xf860,
        "SETGLOB" => op_setglob,

        "GETEXTRABALANCE" => 0xf880,

        "GETPARAMLONG" => 0xf881(u8),
        "INMSGPARAMS" => 0xf88111,

        "INMSGPARAM" => 0xf89(u4),
        "INMSG_BOUNCE" => 0xf890,
        "INMSG_BOUNCED" => 0xf891,
        "INMSG_SRC" => 0xf892,
        "INMSG_FWDFEE" => 0xf893,
        "INMSG_LT" => 0xf894,
        "INMSG_UTIME" => 0xf895,
        "INMSG_ORIGVALUE" => 0xf896,
        "INMSG_VALUE" => 0xf897,
        "INMSG_VALUEEXTRA" => 0xf898,
        "INMSG_STATEINIT" => 0xf899,

        "HASHCU" => 0xf900,
        "HASHSU" => 0xf901,
        "SHA256U" => 0xf902,

        "HASHEXT" => 0xf904(u8),
        "HASHEXT_SHA256" => 0xf90400,
        "HASHEXT_SHA512" => 0xf90401,
        "HASHEXT_BLAKE2B" => 0xf90402,
        "HASHEXT_KECCAK256" => 0xf90403,
        "HASHEXT_KECCAK512" => 0xf90404,
        "HASHEXTR" => 0xf905(u8),
        "HASHEXTR_SHA256" => 0xf90500,
        "HASHEXTR_SHA512" => 0xf90501,
        "HASHEXTR_BLAKE2B" => 0xf90502,
        "HASHEXTR_KECCAK256" => 0xf90503,
        "HASHEXTR_KECCAK512" => 0xf90504,
        "HASHEXTA" => 0xf906(u8),
        "HASHEXTA_SHA256" => 0xf90600,
        "HASHEXTA_SHA512" => 0xf90601,
        "HASHEXTA_BLAKE2B" => 0xf90602,
        "HASHEXTA_KECCAK256" => 0xf90603,
        "HASHEXTA_KECCAK512" => 0xf90604,
        "HASHEXTAR" => 0xf907(u8),
        "HASHEXTAR_SHA256" => 0xf90700,
        "HASHEXTAR_SHA512" => 0xf90701,
        "HASHEXTAR_BLAKE2B" => 0xf90702,
        "HASHEXTAR_KECCAK256" => 0xf90703,
        "HASHEXTAR_KECCAK512" => 0xf90704,

        "CHKSIGNU" => 0xf910,
        "CHKSIGNS" => 0xf911,
        "ECRECOVER" => 0xf912,
        "SECP256K1_XONLY_PUBKEY_TWEAK_ADD" => 0xf913,
        "P256_CHKSIGNU" => 0xf914,
        "P256_CHKSIGNS" => 0xf915,

        "RIST255_FROMHASH" => 0xf920,
        "RIST255_VALIDATE" => 0xf921,
        "RIST255_ADD" => 0xf922,
        "RIST255_SUB" => 0xf923,
        "RIST255_MUL" => 0xf924,
        "RIST255_MULBASE" => 0xf925,
        "RIST255_PUSHL" => 0xf926,

        "RIST255_QVALIDATE" => 0xb7f921,
        "RIST255_QADD" => 0xb7f922,
        "RIST255_QSUB" => 0xb7f923,
        "RIST255_QMUL" => 0xb7f924,
        "RIST255_QMULBASE" => 0xb7f925,

        "BLS_VERIFY" => 0xf93000,
        "BLS_AGGREGATE" => 0xf93001,
        "BLS_FASTAGGREGATEVERIFY" => 0xf93002,
        "BLS_AGGREGATEVERIFY" => 0xf93003,

        "BLS_G1_ADD" => 0xf93010,
        "BLS_G1_SUB" => 0xf93011,
        "BLS_G1_NEG" => 0xf93012,
        "BLS_G1_MUL" => 0xf93013,
        "BLS_G1_MULTIEXP" => 0xf93014,
        "BLS_G1_ZERO" => 0xf93015,
        "BLS_MAP_TO_G1" => 0xf93016,
        "BLS_G1_INGROUP" => 0xf93017,
        "BLS_G1_ISZERO" => 0xf93018,

        "BLS_G2_ADD" => 0xf93020,
        "BLS_G2_SUB" => 0xf93021,
        "BLS_G2_NEG" => 0xf93022,
        "BLS_G2_MUL" => 0xf93023,
        "BLS_G2_MULTIEXP" => 0xf93024,
        "BLS_G2_ZERO" => 0xf93025,
        "BLS_MAP_TO_G2" => 0xf93026,
        "BLS_G2_INGROUP" => 0xf93027,
        "BLS_G2_ISZERO" => 0xf93028,

        "BLS_PAIRING" => 0xf93030,
        "BLS_PUSHR" => 0xf93031,

        "CDATASIZEQ" => 0xf940,
        "CDATASIZE" => 0xf941,
        "SDATASIZEQ" => 0xf942,
        "SDATASIZE" => 0xf943,

        "LDGRAMS" | "LDVARUINT16" => 0xfa00,
        "LDVARINT16" => 0xfa01,
        "STGRAMS" | "STVARUINT16" => 0xfa02,
        "STVARINT16" => 0xfa03,

        "LDVARUINT32" => 0xfa04,
        "LDVARINT32" => 0xfa05,
        "STVARUINT32" => 0xfa06,
        "STVARINT32" => 0xfa07,

        "LDMSGADDR" => 0xfa40,
        "LDMSGADDRQ" => 0xfa41,
        "PARSEMSGADDR" => 0xfa42,
        "PARSEMSGADDRQ" => 0xfa43,
        "REWRITESTDADDR" => 0xfa44,
        "REWRITESTDADDRQ" => 0xfa45,
        "REWRITEVARADDR" => 0xfa46,
        "REWRITEVARADDRQ" => 0xfa47,

        "SENDRAWMSG" => 0xfb00,
        "RAWRESERVE" => 0xfb02,
        "RAWRESERVEX" => 0xfb03,
        "SETCODE" => 0xfb04,
        "SETLIBCODE" => 0xfb06,
        "CHANGELIB" => 0xfb07,
        "SENDMSG" => 0xfb08,

        // Debug primitives
        "DEBUG" => op_debug,
        "DEBUGSTR" | "DUMPTOSFMT" => op_debugstr,
        // TODO: "DEBUGSTRI"

        "DUMPSTK" => 0xfe00,
        "DUMPSTKTOP" => op_dumpstktop,
        "HEXDUMP" => 0xfe10,
        "HEXPRINT" => 0xfe11,
        "BINDUMP" => 0xfe12,
        "BINPRINT" => 0xfe13,
        "STRDUMP" => 0xfe14,
        "STRPRINT" => 0xfe15,
        "DEBUGOFF" => 0xfe1e,
        "DEBUGON" => 0xfe1f,
        "DUMP" => 0xfe2(s),
        "PRINT" => 0xfe3(s),
        // TODO: "LOGSTR"
        // TODO: "PRINTSTR"
        "LOGFLUSH" => 0xfef000,

        // Codepage primitives
        "SETCP0" => 0xff00,
        "SETCPX" => 0xfff0,
        "SETCP" => op_setcp,
    });
}

fn op_xchg<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    const SREG_RANGE: std::ops::RangeInclusive<i16> = 0x00..=0xff;

    let (FullSReg(mut s1, s1_span), FullSReg(mut s2, s2_span)) = instr.parse_args(scope)?;
    if !SREG_RANGE.contains(&s1) {
        return Err(AsmError::InvalidRegister(s1_span));
    }
    if !SREG_RANGE.contains(&s2) {
        return Err(AsmError::InvalidRegister(s2_span));
    }

    match s1.cmp(&s2) {
        Ordering::Equal => return Ok(()),
        Ordering::Greater => std::mem::swap(&mut s1, &mut s2),
        Ordering::Less => {}
    }

    fn write_xchg(ctx: &mut Context, s1: i16, s2: i16) -> Result<(), Error> {
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
    }

    write_xchg(ctx, s1, s2).with_span(instr.span)
}

fn op_push<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    match instr.parse_args(scope)? {
        Either::Left(FullSReg(s1, s1_span)) => match s1 {
            0x0..=0xf => ctx.get_builder(8).store_u8(0x20 | s1 as u8),
            0x10..=0xff => ctx.get_builder(16).store_u16(0x5600 | s1 as u16),
            _ => return Err(AsmError::InvalidRegister(s1_span)),
        },
        Either::Right(CReg(c)) => ctx.get_builder(16).store_u16(0xed40 | c as u16),
    }
    .with_span(instr.span)
}

fn op_pop<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    match instr.parse_args(scope)? {
        Either::Left(FullSReg(s1, s1_span)) => match s1 {
            0x0..=0xf => ctx.get_builder(8).store_u8(0x30 | s1 as u8),
            0x10..=0xff => ctx.get_builder(16).store_u16(0x5700 | s1 as u16),
            _ => return Err(AsmError::InvalidRegister(s1_span)),
        },
        Either::Right(CReg(c)) => ctx.get_builder(16).store_u16(0xed50 | c as u16),
    }
    .with_span(instr.span)
}

fn op_blkswap<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU4minus::<1>(s1), NatU4minus::<1>(s2)) = instr.parse_args(scope)?;
    write_op_2sr(ctx, 0x55, 8, s1, s2).with_span(instr.span)
}

fn op_roll<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU4minus::<1>(s2) = instr.parse_args(scope)?;
    if s2 > 0 {
        write_op_2sr(ctx, 0x55, 8, 0, s2).with_span(instr.span)
    } else {
        Ok(())
    }
}

fn op_rollrev<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU4minus::<1>(s1) = instr.parse_args(scope)?;
    if s1 > 0 {
        write_op_2sr(ctx, 0x55, 8, s1, 0).with_span(instr.span)
    } else {
        Ok(())
    }
}

fn op_reverse<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU4minus::<2>(s1), NatU4(s2)) = instr.parse_args(scope)?;
    write_op_2sr(ctx, 0x5e, 8, s1, s2).with_span(instr.span)
}

fn op_blkpush<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (WithSpan(NatU4(s1), arg_span), NatU4(s2)) = instr.parse_args(scope)?;
    if s1 == 0 {
        return Err(AsmError::OutOfRange(arg_span));
    }
    write_op_2sr(ctx, 0x5f, 8, s1, s2).with_span(instr.span)
}

fn op_blkdrop2<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (WithSpan(NatU4(s1), arg_span), NatU4(s2)) = instr.parse_args(scope)?;
    if s1 == 0 {
        return Err(AsmError::OutOfRange(arg_span));
    }
    write_op_2sr(ctx, 0x6c, 8, s1, s2).with_span(instr.span)
}

fn op_index2<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU2(s1), NatU2(s2)) = instr.parse_args(scope)?;
    write_op_1sr(ctx, 0x6fb, 12, (s1 << 2) | s2).with_span(instr.span)
}

fn op_index3<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU2(s1), NatU2(s2), NatU2(s3)) = instr.parse_args(scope)?;
    let args = (s1 << 4) | (s2 << 2) | s3;
    ctx.get_builder(16)
        .store_uint(0x6fc0 | args as u64, 16)
        .with_span(instr.span)
}

fn op_pushint<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(n), nat_span) = instr.parse_args(scope)?;
    write_pushint(ctx, instr.span, nat_span, n)
}

fn write_pushint(
    ctx: &mut Context,
    instr_span: ast::Span,
    nat_span: ast::Span,
    n: &BigInt,
) -> Result<(), AsmError> {
    if let Some(n) = n.to_i8() {
        if (-5..=10).contains(&n) {
            return ctx
                .get_builder(8)
                .store_u8(0x70 | (n as u8) & 0xf)
                .with_span(instr_span);
        }
    }

    let bitsize = bitsize(n, true);
    if bitsize > 257 {
        return Err(AsmError::OutOfRange(nat_span));
    }

    fn write_pushint_impl(ctx: &mut Context, n: &BigInt, bitsize: u16) -> Result<(), Error> {
        if bitsize <= 8 {
            let b = ctx.get_builder(16);
            b.store_u8(0x80)?;
            store_int_to_builder(n, 8, true, b)
        } else if bitsize <= 16 {
            let b = ctx.get_builder(24);
            b.store_u8(0x81)?;
            store_int_to_builder(n, 16, true, b)
        } else {
            let l = (bitsize + 4) / 8;
            let value_bits = 3 + l * 8;
            let b = ctx.get_builder(13 + value_bits);
            b.store_u8(0x82)?;
            b.store_small_uint((l - 2) as u8, 5)?;
            store_int_to_builder(n, value_bits, true, b)
        }
    }

    write_pushint_impl(ctx, n, bitsize).with_span(instr_span)
}

fn op_pushpow2<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(n), span) = instr.parse_args(scope)?;

    match n.to_u16().unwrap_or(u16::MAX) {
        0 => ctx.get_builder(8).store_u8(0x71),
        n @ 1..=255 => {
            let b = ctx.get_builder(16);
            b.store_u8(0x83).with_span(instr.span)?;
            b.store_u8((n - 1) as _)
        }
        256 => {
            return Err(AsmError::WrongUsage {
                details: "use PUSHNAN instead of PUSHPOW2 256",
                span,
            });
        }
        _ => return Err(AsmError::OutOfRange(span)),
    }
    .with_span(instr.span)
}

fn op_pushintx<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(n), span) = instr.parse_args(scope)?;
    let bitsize = bitsize(n, true);

    if bitsize <= 8 {
        // NOTE: base=1 && pow2=0 case will be handled here
        return op_pushint(ctx, instr, scope);
    } else if bitsize > 257 {
        return Err(AsmError::OutOfRange(span));
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
        })
        .with_span(instr.span)?;
        b.store_u8((pow2 - 1) as _).with_span(instr.span)
    } else if pow2 >= 20 {
        // PUSHINT base
        write_pushint(ctx, instr.span, span, &base)?;
        // LSHIFT# pow2
        write_op_1sr_l(ctx, 0xaa, 8, (pow2 - 1) as _).with_span(instr.span)
    } else {
        if pow2 == 0 {
            let mut base = !n;
            let pow2 = base.trailing_zeros().unwrap();
            base >>= pow2;
            if base.sign() == Sign::Minus && base.magnitude().is_one() {
                // PUSHPOW2DEC
                return write_op_1sr_l(ctx, 0x84, 8, (pow2 - 1) as _).with_span(instr.span);
            }
        }

        // Fallback to PUSHINT
        write_pushint(ctx, instr.span, span, n)
    }
}

fn op_stsliceconst<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    const PREFIX_BIT_LEN: u16 = 22;

    let c = instr
        .parse_args::<SliceOrCont>(scope)?
        .into_cell(ctx.make_child_context(), scope.make_child_scope())?;

    fn write_stsliceconst(ctx: &mut Context, c: Cell) -> Result<(), Error> {
        const MAX_BITS: u16 = 8 * 7 + 1;
        const MAX_REFS: u8 = 3;

        let bits = c.bit_len();
        let refs = c.reference_count();

        let (rem_bits, rem_refs) = ctx.top_capacity();
        if bits + PREFIX_BIT_LEN > rem_bits || refs > rem_refs.min(MAX_REFS) || bits > MAX_BITS {
            // Fallback to PUSHSLICE STSLICER
            write_pushslice(ctx, c)?;
            write_op(ctx, 0xcf16, 16)
        } else {
            let l = (bits + 6) / 8;
            let padding = l * 8 + 2 - bits;
            let b = ctx.get_builder_ext(9 + 2 + 3 + bits + padding, refs);
            b.store_u8(0xcf)?;
            b.store_bit_one()?;
            b.store_small_uint(refs, 2)?;
            b.store_small_uint(l as u8, 3)?;
            b.store_slice(c.as_slice_allow_exotic())?;
            write_slice_padding(padding, b)
        }
    }

    write_stsliceconst(ctx, c).with_span(instr.span)
}

fn op_pushslice<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let c = instr
        .parse_args::<SliceOrCont>(scope)?
        .into_cell(ctx.make_child_context(), scope.make_child_scope())?;
    write_pushslice(ctx, c).with_span(instr.span)
}

fn write_pushslice(ctx: &mut Context, c: Cell) -> Result<(), Error> {
    const MAX_BITS_OVERHEAD: u16 = 26; // Longest prefix/padding

    let bits = c.bit_len();
    let refs = c.reference_count();

    let (rem_bits, rem_refs) = ctx.top_capacity();
    if bits + MAX_BITS_OVERHEAD > rem_bits || refs + 1 > rem_refs {
        // Fallback to PUSHREFSLICE
        let b = ctx.get_builder_ext(8, 2);
        b.store_u8(0x89)?;
        b.store_reference(c)
    } else if bits <= 123 && refs == 0 {
        let l = (bits + 4) / 8;
        let padding = l * 8 + 4 - bits;
        let b = ctx.get_builder_ext(8 + 4 + bits + padding, refs + 1);
        b.store_u8(0x8b)?;
        b.store_small_uint(l as u8, 4)?;
        b.store_slice(c.as_slice_allow_exotic())?;
        write_slice_padding(padding, b)
    } else if bits <= 248 && refs >= 1 {
        let l = bits.div_ceil(8);
        let padding = l * 8 + 1 - bits;
        let b = ctx.get_builder_ext(8 + 2 + 5 + bits + padding, refs + 1);
        b.store_u8(0x8c)?;
        b.store_small_uint(refs - 1, 2)?;
        b.store_small_uint(l as u8, 5)?;
        b.store_slice(c.as_slice_allow_exotic())?;
        write_slice_padding(padding, b)
    } else {
        let l = (bits + 2) / 8;
        let padding = l * 8 + 6 - bits;
        let b = ctx.get_builder_ext(8 + 3 + 7 + bits + padding, refs + 1);
        b.store_u8(0x8d)?;
        b.store_small_uint(refs, 3)?;
        b.store_small_uint(l as u8, 7)?;
        b.store_slice(c.as_slice_allow_exotic())?;
        write_slice_padding(padding, b)
    }
}

fn op_pushcont<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    const MAX_BITS_OVERHEAD: u16 = 16;

    let WithSpan(c @ SliceOrCont(..), span) = instr.parse_args(scope)?;
    let c = c.into_cell(ctx.make_child_context(), scope.make_child_scope())?;
    let bits = c.bit_len();
    if bits % 8 != 0 {
        return Err(AsmError::UnalignedCont { bits, span });
    }

    fn write_pushcont(ctx: &mut Context, c: Cell) -> Result<(), Error> {
        let bits = c.bit_len();
        let refs = c.reference_count();
        let is_library = c.descriptor().cell_type() == CellType::LibraryReference;

        let (rem_bits, rem_refs) = ctx.top_capacity();
        if is_library || bits + MAX_BITS_OVERHEAD > rem_bits || refs + 1 > rem_refs {
            // Fallback to PUSHREFCONT
            let b = ctx.get_builder_ext(8, 2);
            b.store_u8(0x8a)?;
            b.store_reference(c)
        } else if bits <= 120 && refs == 0 {
            let b = ctx.get_builder(8 + bits);
            b.store_u8(0x90 | (bits / 8) as u8)?;
            b.store_slice(c.as_slice_allow_exotic())
        } else {
            let b = ctx.get_builder_ext(16 + bits, refs + 1);
            b.store_u16(0x8e00 | ((refs as u16) << 7) | (bits / 8))?;
            b.store_slice(c.as_slice_allow_exotic())
        }
    }

    write_pushcont(ctx, c).with_span(instr.span)
}

fn op_subconst<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(NatI8(s1), span) = instr.parse_args(scope)?;
    if s1 == i8::MIN {
        return Err(AsmError::OutOfRange(span));
    }
    write_op_1sr_l(ctx, 0xa6, 8, -s1 as u8).with_span(instr.span)
}

fn op_pldrefidx<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU2(s) = instr.parse_args(scope)?;
    ctx.get_builder(16)
        .store_u16(0xd74c | s as u16)
        .with_span(instr.span)
}

fn op_callxargs<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU4(p), WithSpan(Nat(r), r_span)) = instr.parse_args(scope)?;
    match r.sign() {
        // DApr
        Sign::NoSign | Sign::Plus => {
            let r = match r.to_u8() {
                Some(r) if (0..=15).contains(&r) => r,
                _ => return Err(AsmError::OutOfRange(r_span)),
            };
            ctx.get_builder(16)
                .store_u16(0xda00 | ((p as u16) << 4) | (r as u16))
        }
        // DB0p
        Sign::Minus => {
            if !matches!(r.to_i8(), Some(-1)) {
                return Err(AsmError::OutOfRange(r_span));
            }
            ctx.get_builder(16).store_u16(0xdb00 | (p as u16))
        }
    }
    .with_span(instr.span)
}

fn op_callccargs<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU4(p), WithSpan(Nat(r), r_span)) = instr.parse_args(scope)?;
    let r = match r.to_i8() {
        Some(r) if (-1..=14).contains(&r) => (r as u8) & 0xf,
        _ => return Err(AsmError::OutOfRange(r_span)),
    };
    ctx.get_builder(24)
        .store_uint(0xdb3600 | ((p as u64) << 4) | (r as u64), 24)
        .with_span(instr.span)
}

fn op_ifbitjmp<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    op_ifbitjmp_impl::<false>(ctx, instr, scope)
}

fn op_ifnbitjmp<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    op_ifbitjmp_impl::<true>(ctx, instr, scope)
}

fn op_ifbitjmp_impl<'s, const INV: bool>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU5(s) = instr.parse_args(scope)?;
    ctx.get_builder(16)
        .store_u16(0xe380 | (0x20 * INV as u16) | s as u16)
        .with_span(instr.span)
}

fn op_ifbitjmpref<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    op_ifbitjmpref_impl::<false>(ctx, instr, scope)
}

fn op_ifnbitjmpref<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    op_ifbitjmpref_impl::<true>(ctx, instr, scope)
}

fn op_ifbitjmpref_impl<'s, const INV: bool>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU5(s), c @ SliceOrCont(..)) = instr.parse_args(scope)?;
    let c = c.into_cell(ctx.make_child_context(), scope.make_child_scope())?;

    let b = ctx.get_builder_ext(16, 2);
    b.store_u16(0xe39c | (0x20 * INV as u16) | s as u16)
        .with_span(instr.span)?;
    b.store_reference(c).with_span(instr.span)
}

fn op_setcontargs<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU4(r), WithSpan(Nat(n), n_span)) = instr.parse_args(scope)?;
    let n = match n.to_i8() {
        Some(n) if (-1..=14).contains(&n) => (n as u8) & 0xf,
        _ => return Err(AsmError::OutOfRange(n_span)),
    };
    ctx.get_builder(16)
        .store_u16(0xec00 | ((r as u16) << 4) | (n as u16))
        .with_span(instr.span)
}

fn op_setnumargs<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(n), n_span) = instr.parse_args(scope)?;
    let n = match n.to_i8() {
        Some(n) if (-1..=14).contains(&n) => (n as u8) & 0xf,
        _ => return Err(AsmError::OutOfRange(n_span)),
    };
    ctx.get_builder(16)
        .store_u16(0xec00 | (n as u16))
        .with_span(instr.span)
}

fn op_blessargs<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU4(r), WithSpan(Nat(n), n_span)) = instr.parse_args(scope)?;
    let n = match n.to_i8() {
        Some(n) if (-1..=14).contains(&n) => (n as u8) & 0xf,
        _ => return Err(AsmError::OutOfRange(n_span)),
    };
    ctx.get_builder(16)
        .store_u16(0xee00 | ((r as u16) << 4) | (n as u16))
        .with_span(instr.span)
}

fn op_blessnumargs<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(n), n_span) = instr.parse_args(scope)?;
    let n = match n.to_i8() {
        Some(n) if (-1..=14).contains(&n) => (n as u8) & 0xf,
        _ => return Err(AsmError::OutOfRange(n_span)),
    };
    ctx.get_builder(16)
        .store_u16(0xee00 | (n as u16))
        .with_span(instr.span)
}

fn op_callvar<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    // PUSH c3
    op_preparevar(ctx, instr, scope)?;
    // EXECUTE
    write_op(ctx, 0xd8, 8).with_span(instr.span)
}

fn op_jmpvar<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    // PUSH c3
    op_preparevar(ctx, instr, scope)?;
    // JMPX
    write_op(ctx, 0xd9, 8).with_span(instr.span)
}

fn op_preparevar<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    instr.parse_args::<()>(scope)?;
    // PUSH c3
    write_op_1sr(ctx, 0xed4, 12, 3).with_span(instr.span)
}

fn op_call<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(id), nat_span) = instr.parse_args(scope)?;

    match id.to_u16() {
        Some(id @ 0x00..=0xff) => write_op_1sr_l(ctx, 0xf0, 8, id as u8),
        Some(id @ 0x0100..=0x3fff) => ctx
            .get_builder(24)
            .store_uint(0xf10000 | ((id as u64) & 0x3fff), 24),
        _ => {
            // PUSHINT id
            write_pushint(ctx, instr.span, nat_span, id)?;
            // PUSH c3
            op_preparevar(ctx, instr, scope)?;
            // EXECUTE
            write_op(ctx, 0xd8, 8)
        }
    }
    .with_span(instr.span)
}

fn op_jmp<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(id), nat_span) = instr.parse_args(scope)?;

    match id.to_u16() {
        Some(id @ 0x0000..=0x3fff) => ctx
            .get_builder(24)
            .store_uint(0xf14000 | ((id as u64) & 0x3fff), 24),
        _ => {
            // PUSHINT id
            write_pushint(ctx, instr.span, nat_span, id)?;
            // PUSH c3
            op_preparevar(ctx, instr, scope)?;
            // JMPX
            write_op(ctx, 0xd9, 8)
        }
    }
    .with_span(instr.span)
}

fn op_prepare<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(id), nat_span) = instr.parse_args(scope)?;

    match id.to_u16() {
        Some(id @ 0x0000..=0x3fff) => ctx
            .get_builder(24)
            .store_uint(0xf18000 | ((id as u64) & 0x3fff), 24)
            .with_span(instr.span),
        _ => {
            // PUSHINT id
            write_pushint(ctx, instr.span, nat_span, id)?;
            // PUSH c3
            op_preparevar(ctx, instr, scope)
        }
    }
}

fn op_throw<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(id), nat_span) = instr.parse_args(scope)?;

    match id.to_u16() {
        Some(id @ 0x00..=0x3f) => ctx.get_builder(16).store_u16(0xf200 | id),
        Some(id @ 0x40..=0x7ff) => ctx.get_builder(24).store_uint(0xf2c000 | (id as u64), 24),
        _ => return Err(AsmError::OutOfRange(nat_span)),
    }
    .with_span(instr.span)
}

fn op_throwif<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(id), nat_span) = instr.parse_args(scope)?;

    match id.to_u16() {
        Some(id @ 0x00..=0x3f) => ctx.get_builder(16).store_u16(0xf240 | id),
        Some(id @ 0x100..=0x7ff) => ctx.get_builder(24).store_uint(0xf2d000 | (id as u64), 24),
        _ => return Err(AsmError::OutOfRange(nat_span)),
    }
    .with_span(instr.span)
}

fn op_throwifnot<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(id), nat_span) = instr.parse_args(scope)?;

    match id.to_u16() {
        Some(id @ 0x00..=0x3f) => ctx.get_builder(16).store_u16(0xf280 | id),
        Some(id @ 0x100..=0x7ff) => ctx.get_builder(24).store_uint(0xf2e000 | (id as u64), 24),
        _ => return Err(AsmError::OutOfRange(nat_span)),
    }
    .with_span(instr.span)
}

fn op_throwarg<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU11(n) = instr.parse_args(scope)?;
    ctx.get_builder(24)
        .store_uint(0xf2c800 | (n as u64), 24)
        .with_span(instr.span)
}

fn op_throwargif<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU11(n) = instr.parse_args(scope)?;
    ctx.get_builder(24)
        .store_uint(0xf2d800 | (n as u64), 24)
        .with_span(instr.span)
}

fn op_throwargifnot<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU11(n) = instr.parse_args(scope)?;
    ctx.get_builder(24)
        .store_uint(0xf2e800 | (n as u64), 24)
        .with_span(instr.span)
}

fn op_tryargs<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (NatU4(s1), NatU4(s2)) = instr.parse_args(scope)?;
    write_op_2sr(ctx, 0xf3, 8, s1, s2).with_span(instr.span)
}

fn op_dictpushconst<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    use tycho_types::dict;

    let (NatU10(n), dict) = instr.parse_args::<(_, &ast::InstrArg<'_>)>(scope)?;
    let dict_span = dict.span;
    let ast::InstrArgValue::JumpTable(dict) = &dict.value else {
        return Err(AsmError::ArgTypeMismatch {
            span: dict.span,
            found: dict.value.ty(),
            expected: ArgType::JumpTable.expected_exact(),
        });
    };

    let mut errors = Vec::new();

    let mut result = None::<Cell>;
    for method in &dict.methods {
        let key = match &method.key.data {
            ast::JumpTableItemKeyData::Nat(n) => Some(n),
            ast::JumpTableItemKeyData::MethodId(m) => Some(&m.value.computed),
            ast::JumpTableItemKeyData::Use(u) => match scope.resolve_use_raw(u.value.name) {
                Some(x) => match &x.value {
                    ast::InstrArgValue::Nat(n) => Some(n),
                    ast::InstrArgValue::MethodId(m) => Some(&m.value.computed),
                    _ => {
                        errors.push(AsmError::ArgTypeMismatch {
                            span: u.span,
                            found: x.value.ty(),
                            expected: ArgType::Nat.expected_or(ArgType::MethodId),
                        });
                        None
                    }
                },
                None => {
                    errors.push(AsmError::UndefinedVariable(u.value.span));
                    None
                }
            },
            ast::JumpTableItemKeyData::Invalid => {
                errors.push(AsmError::InvalidJumpTableKey(method.key.span));
                None
            }
        };

        let value = match &method.value.data {
            ast::JumpTableItemValueData::Block(value) => Some(SliceOrCont(Either::Right((
                value.as_slice(),
                method.value.span,
            )))),
            ast::JumpTableItemValueData::Invalid => {
                errors.push(AsmError::InvalidJumpTableValue(method.value.span));
                None
            }
        };

        let mut kb;
        let key = match key {
            Some(key) => {
                kb = CellBuilder::new();
                if store_int_to_builder(key, n, key.sign() == Sign::Minus, &mut kb).is_ok() {
                    Some(kb.as_data_slice())
                } else {
                    errors.push(AsmError::TooBigInteger(method.key.span));
                    None
                }
            }
            None => None,
        };

        let value = match value {
            Some(value) => {
                match value.into_cell(ctx.make_child_context(), scope.make_child_scope()) {
                    Ok(value) => Some(value),
                    Err(e) if ctx.allow_invalid => {
                        errors.push(e);
                        None
                    }
                    Err(e) => return Err(e),
                }
            }
            None => None,
        };

        if let (Some(mut key), Some(value)) = (key, value) {
            if let Ok(value) = value.as_slice() {
                let prev_key = key;
                let prev_result = result.clone();
                match dict::dict_insert(
                    &mut result,
                    &mut key,
                    n,
                    &value,
                    dict::SetMode::Add,
                    Cell::empty_context(),
                ) {
                    Ok(true) => continue,
                    Ok(false) => return Err(AsmError::DuplicateJumpTableEntry(method.key.span)),
                    Err(_) => {
                        result = prev_result;
                        key = prev_key;
                    }
                }
            }

            match dict::dict_insert(
                &mut result,
                &mut key,
                n,
                &value,
                dict::SetMode::Add,
                Cell::empty_context(),
            ) {
                Ok(true) => {}
                Ok(false) => return Err(AsmError::DuplicateJumpTableEntry(method.key.span)),
                Err(e) => {
                    errors.push(AsmError::StoreError {
                        inner: e,
                        span: method.value.span,
                    });
                }
            }
        }
    }

    if !errors.is_empty() {
        return Err(AsmError::Multiple(errors.into()));
    }

    let Some(result) = result else {
        return Err(AsmError::EmptyJumpTable(dict_span));
    };

    let b = ctx.get_builder_ext(24, 1);
    b.store_uint(0xf4a400_u64 | n as u64, 24)
        .with_span(instr.span)?;
    b.store_reference(result).with_span(instr.span)
}

fn op_getglob<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(NatU5(n), span) = instr.parse_args(scope)?;
    if n == 0 {
        return Err(AsmError::OutOfRange(span));
    }
    ctx.get_builder(16)
        .store_u16(0xf840 | n as u16)
        .with_span(instr.span)
}

fn op_setglob<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(NatU5(n), span) = instr.parse_args(scope)?;
    if n == 0 {
        return Err(AsmError::OutOfRange(span));
    }
    ctx.get_builder(16)
        .store_u16(0xf860 | n as u16)
        .with_span(instr.span)
}

fn op_debug<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(NatU8(n), span) = instr.parse_args(scope)?;
    if n > 0xef {
        return Err(AsmError::OutOfRange(span));
    }
    write_op_1sr_l(ctx, 0xfe, 8, n).with_span(instr.span)
}

fn op_debugstr<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Slice(s), span) = instr.parse_args(scope)?;
    let bit_len = s.bit_len();
    if bit_len % 8 != 0 {
        return Err(AsmError::WrongUsage {
            details: "arg bit len is not multiple of 8",
            span,
        });
    } else if bit_len == 0 {
        return Err(AsmError::WrongUsage {
            details: "expected a non-empty string",
            span,
        });
    } else if bit_len > 64 {
        return Err(AsmError::WrongUsage {
            details: "arg bit len is too big",
            span,
        });
    }

    fn write_debugstr(ctx: &mut Context, s: &DynCell) -> Result<(), Error> {
        let bit_len = s.bit_len();
        let b = ctx.get_builder(12 + 4 + bit_len);
        b.store_u16(0xfef0 | ((bit_len / 8) - 1))?;
        b.store_raw(s.data(), bit_len)
    }
    write_debugstr(ctx, s.as_ref()).with_span(instr.span)
}

fn op_dumpstktop<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(NatU4(n), span) = instr.parse_args(scope)?;
    if n == 0 {
        return Err(AsmError::OutOfRange(span));
    }
    write_op_1sr(ctx, 0xfe0, 12, n).with_span(instr.span)
}

fn op_setcp<'s>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let WithSpan(Nat(n), span) = instr.parse_args(scope)?;
    match n.to_i16() {
        Some(n @ -14..=239) => write_op_1sr_l(ctx, 0xff, 8, n as u8).with_span(instr.span),
        _ => Err(AsmError::OutOfRange(span)),
    }
}

fn op_simple<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    instr.parse_args::<()>(scope)?;
    write_op(ctx, BASE, BITS).with_span(instr.span)
}

fn op_1sr<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let SReg(s1) = instr.parse_args(scope)?;
    write_op_1sr(ctx, BASE, BITS, s1).with_span(instr.span)
}

fn op_u4<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU4(s1) = instr.parse_args(scope)?;
    write_op_1sr(ctx, BASE, BITS, s1).with_span(instr.span)
}

fn op_u8<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU8(s1) = instr.parse_args(scope)?;
    write_op_1sr_l(ctx, BASE, BITS, s1).with_span(instr.span)
}

fn op_u8_minus1<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU8minus::<1>(s1) = instr.parse_args(scope)?;
    write_op_1sr_l(ctx, BASE, BITS, s1).with_span(instr.span)
}

fn op_i8<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatI8(s1) = instr.parse_args(scope)?;
    write_op_1sr_l(ctx, BASE, BITS, s1 as u8).with_span(instr.span)
}

fn op_u12<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let NatU12(n) = instr.parse_args(scope)?;
    ctx.get_builder(24)
        .store_uint(0xdb4000 | (n as u64), 24)
        .with_span(instr.span)
}

fn op_2sr<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (SReg(s1), SReg(s2)) = instr.parse_args(scope)?;
    write_op_2sr(ctx, BASE, BITS, s1, s2).with_span(instr.span)
}

fn op_2sr_adj<'s, const BASE: u32, const BITS: u16, const ADJ: u32>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (mut s1 @ FullSReg(..), mut s2 @ FullSReg(..)) = instr.parse_args(scope)?;
    s1.0 += ((ADJ >> 4) & 0xf) as i16;
    s2.0 += (ADJ & 0xf) as i16;
    let (SReg(s1), SReg(s2)) = if ctx.allow_invalid {
        (s1.try_into(), s2.try_into()).join_results()?
    } else {
        (s1.try_into()?, s2.try_into()?)
    };
    write_op_2sr(ctx, BASE, BITS, s1, s2).with_span(instr.span)
}

fn op_3sr<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (SReg(s1), SReg(s2), SReg(s3)) = instr.parse_args(scope)?;
    write_op_3sr(ctx, BASE, BITS, s1, s2, s3).with_span(instr.span)
}

fn op_3sr_adj<'s, const BASE: u32, const BITS: u16, const ADJ: u32>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (mut s1 @ FullSReg(..), mut s2 @ FullSReg(..), mut s3 @ FullSReg(..)) =
        instr.parse_args(scope)?;
    s1.0 += ((ADJ >> 8) & 0xf) as i16;
    s2.0 += ((ADJ >> 4) & 0xf) as i16;
    s3.0 += (ADJ & 0xf) as i16;
    let (SReg(s1), SReg(s2), SReg(s3)) = if ctx.allow_invalid {
        (s1.try_into(), s2.try_into(), s3.try_into()).join_results()?
    } else {
        (s1.try_into()?, s2.try_into()?, s3.try_into()?)
    };
    write_op_3sr(ctx, BASE, BITS, s1, s2, s3).with_span(instr.span)
}

fn op_1cr<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let CReg(c) = instr.parse_args(scope)?;
    write_op_1sr(ctx, BASE, BITS, c).with_span(instr.span)
}

fn op_1ref<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let c = instr
        .parse_args::<SliceOrCont>(scope)?
        .into_cell(ctx.make_child_context(), scope.make_child_scope())?;
    write_op_1ref(ctx, BASE, BITS, c).with_span(instr.span)
}

fn op_2ref<'s, const BASE: u32, const BITS: u16>(
    ctx: &mut Context,
    instr: &ast::Instr<'s>,
    scope: &mut Scope<'_, 's>,
) -> Result<(), AsmError> {
    let (c1 @ SliceOrCont(..), c2 @ SliceOrCont(..)) = instr.parse_args(scope)?;
    let (c1, c2) = if ctx.allow_invalid {
        (
            c1.into_cell(ctx.make_child_context(), scope.make_child_scope()),
            c2.into_cell(ctx.make_child_context(), scope.make_child_scope()),
        )
            .join_results()?
    } else {
        (
            c1.into_cell(ctx.make_child_context(), scope.make_child_scope())?,
            c2.into_cell(ctx.make_child_context(), scope.make_child_scope())?,
        )
    };

    write_op_2ref(ctx, BASE, BITS, c1, c2).with_span(instr.span)
}

fn write_op(ctx: &mut Context, base: u32, bits: u16) -> Result<(), Error> {
    ctx.get_builder(bits).store_uint(base as _, bits)
}

fn write_op_1sr(ctx: &mut Context, base: u32, bits: u16, s1: u8) -> Result<(), Error> {
    ctx.get_builder(bits + 4)
        .store_uint(((base << 4) | s1 as u32) as _, bits + 4)
}

fn write_op_1sr_l(ctx: &mut Context, base: u32, bits: u16, s1: u8) -> Result<(), Error> {
    ctx.get_builder(bits + 8)
        .store_uint(((base << 8) | s1 as u32) as _, bits + 8)
}

fn write_op_2sr(ctx: &mut Context, base: u32, bits: u16, s1: u8, s2: u8) -> Result<(), Error> {
    ctx.get_builder(bits + 8).store_uint(
        ((base << 8) | (s1 << 4) as u32 | (s2 & 0xf) as u32) as _,
        bits + 8,
    )
}

fn write_op_3sr(
    ctx: &mut Context,
    base: u32,
    bits: u16,
    s1: u8,
    s2: u8,
    s3: u8,
) -> Result<(), Error> {
    let args = (((s1 & 0xf) as u32) << 8) | (((s2 & 0xf) as u32) << 4) | ((s3 & 0xf) as u32);
    ctx.get_builder(bits + 12)
        .store_uint(((base << 12) | args) as _, bits + 12)
}

fn write_op_1ref(ctx: &mut Context, base: u32, bits: u16, r: Cell) -> Result<(), Error> {
    let b = ctx.get_builder_ext(bits, 2);
    b.store_uint(base as _, bits)?;
    b.store_reference(r)
}

fn write_op_2ref(ctx: &mut Context, base: u32, bits: u16, r1: Cell, r2: Cell) -> Result<(), Error> {
    let b = ctx.get_builder_ext(bits, 3);
    b.store_uint(base as _, bits)?;
    b.store_reference(r1)?;
    b.store_reference(r2)
}

fn write_slice_padding(padding: u16, b: &mut CellBuilder) -> Result<(), Error> {
    debug_assert!((1..=8).contains(&padding), "Invalid slice padding");
    b.store_bit_one()?;
    b.store_zeros(padding - 1)
}

impl<'c, 's> SliceOrCont<'c, 's> {
    fn into_cell(self, mut ctx: Context, mut scope: Scope<'c, 's>) -> Result<Cell, AsmError> {
        match self.0 {
            Either::Left(cell) => Ok(cell),
            Either::Right((items, block_span)) => {
                let opcodes = cp0();
                if ctx.allow_invalid {
                    let mut errors = Vec::new();

                    for item in items {
                        if let Err(e) = ctx.add_stmt(opcodes, item, &mut scope) {
                            errors.push(e);
                        }
                    }

                    match ctx
                        .into_builder(block_span)
                        .and_then(|b| b.build().with_span(block_span))
                    {
                        res if errors.is_empty() => res,
                        res => {
                            if let Err(e) = res {
                                errors.push(e);
                            }
                            Err(AsmError::Multiple(errors.into_boxed_slice()))
                        }
                    }
                } else {
                    for item in items {
                        ctx.add_stmt(opcodes, item, &mut scope)?;
                    }

                    ctx.into_builder(block_span)?.build().with_span(block_span)
                }
            }
        }
    }
}

trait WithSpan<T> {
    fn with_span(self, span: ast::Span) -> Result<T, AsmError>;
}

impl<T> WithSpan<T> for Result<T, Error> {
    #[inline]
    fn with_span(self, span: ast::Span) -> Result<T, AsmError> {
        self.map_err(|e| AsmError::StoreError { inner: e, span })
    }
}
