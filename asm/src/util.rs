use std::borrow::Cow;

use everscale_types::error::Error;
use everscale_types::prelude::CellBuilder;
use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;

pub fn bitsize(int: &BigInt, signed: bool) -> u16 {
    let mut bits = int.bits() as u16;
    if signed {
        match int.sign() {
            Sign::NoSign => bits,
            Sign::Plus => bits + 1,
            Sign::Minus => {
                // Check if `int` magnitude is not a power of 2
                let mut digits = int.iter_u64_digits().rev();
                if let Some(hi) = digits.next() {
                    if !hi.is_power_of_two() || !digits.all(|digit| digit == 0) {
                        bits += 1;
                    }
                }
                bits
            }
        }
    } else {
        bits
    }
}

/// Stores `bits`-width int to the builder.
pub fn store_int_to_builder(
    x: &BigInt,
    bits: u16,
    signed: bool,
    builder: &mut CellBuilder,
) -> Result<(), Error> {
    let int_bits = bitsize(x, signed);
    if bits < int_bits {
        return Err(Error::IntOverflow);
    }
    store_int_to_builder_unchecked(x, bits, signed, builder)
}

pub fn store_int_to_builder_unchecked(
    x: &BigInt,
    bits: u16,
    signed: bool,
    builder: &mut CellBuilder,
) -> Result<(), Error> {
    match x.to_u64() {
        Some(value) => builder.store_uint(value, bits),
        None => {
            let int = if bits % 8 != 0 {
                let align = 8 - bits % 8;
                Cow::Owned(x.clone() << align)
            } else {
                Cow::Borrowed(x)
            };

            let minimal_bytes = bits.div_ceil(8) as usize;

            let (prefix, mut bytes) = if signed {
                let bytes = int.to_signed_bytes_le();
                (
                    bytes
                        .last()
                        .map(|first| (first >> 7) * 255)
                        .unwrap_or_default(),
                    bytes,
                )
            } else {
                (0, int.to_bytes_le().1)
            };
            bytes.resize(minimal_bytes, prefix);
            bytes.reverse();

            builder.store_raw(&bytes, bits)
        }
    }
}
