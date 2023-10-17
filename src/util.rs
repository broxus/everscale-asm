use everscale_types::error::Error;
use everscale_types::prelude::CellBuilder;
use num_bigint::{BigInt, Sign};
use num_traits::{One, ToPrimitive, Zero};

pub fn bitsize(int: &BigInt) -> u16 {
    let mut bits = int.bits() as u16;
    if int.is_zero() || int.sign() == Sign::Minus && int.magnitude().is_one() {
        return 1;
    } else if int.sign() == Sign::Plus {
        return bits + 1;
    }

    let mut modpow2 = int.magnitude().clone();
    modpow2 &= &modpow2 - 1u32;
    if !modpow2.is_zero() {
        bits += 1;
    }

    bits
}

pub fn store_int_to_builder(
    builder: &mut CellBuilder,
    int: &BigInt,
    bits: u16,
) -> Result<(), Error> {
    use std::borrow::Cow;

    let int_bits = bitsize(int);
    if int_bits > bits {
        return Err(Error::IntOverflow);
    }

    match int.to_u64() {
        Some(value) => builder.store_uint(value, bits)?,
        None => {
            let int = if bits % 8 != 0 {
                let align = 8 - bits % 8;
                Cow::Owned(int.clone() << align)
            } else {
                Cow::Borrowed(int)
            };

            let minimal_bytes = ((bits + 7) / 8) as usize;

            let mut bytes = int.to_signed_bytes_le();
            let prefix = bytes
                .last()
                .map(|first| (first >> 7) * 255)
                .unwrap_or_default();

            bytes.resize(minimal_bytes, prefix);
            bytes.reverse();

            builder.store_raw(&bytes, bits)?;
        }
    };

    Ok(())
}
