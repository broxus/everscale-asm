/// Prevents using `From::from` for plain error conversion.
macro_rules! ok {
    ($e:expr $(,)?) => {
        match $e {
            core::result::Result::Ok(val) => val,
            core::result::Result::Err(err) => return core::result::Result::Err(err),
        }
    };
}

use everscale_types::error::Error;
use everscale_types::prelude::*;

pub mod ast;

pub const MAX_OPCODE_BITS: usize = 24;
pub const MAX_OPCODE: u32 = 1 << MAX_OPCODE_BITS;

pub enum Opcode {
    Simple { value: u32, bits: u16 },
    Block(Vec<Opcode>),
    Cell(Cell),
}

impl Opcode {
    pub const fn simple(value: u32, bits: u16) -> Self {
        Self::Simple { value, bits }
    }

    pub const fn fixed_s(value: u32, bits: u16, s: u8) -> Self {
        Self::Simple {
            value: (value << 4) | (s as u32),
            bits: bits + 4,
        }
    }
}

impl Store for Opcode {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            Self::Simple { value, bits } => builder.store_uint(*value as _, *bits),
            Self::Block(opcodes) => {
                for opcode in opcodes {
                    ok!(opcode.store_into(builder, context));
                }
                Ok(())
            }
            Self::Cell(cell) => builder.store_reference(cell.clone()),
        }
    }
}
