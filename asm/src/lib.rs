use everscale_types::prelude::*;

pub use asm::{ArgType, AsmError, ExpectedArgType};
pub use ast::{ParserError, Span};

mod asm;
mod ast;
mod util;

pub struct Code<'a> {
    text: &'a str,
    ast: Option<ast::Code<'a>>,
    parser_errors: Vec<ast::ParserError>,
}

impl<'a> Code<'a> {
    pub fn assemble(text: &'a str) -> anyhow::Result<Cell> {
        let cell = Self::parse(text).try_into_valid()?.assemble()?;
        Ok(cell)
    }

    pub fn parse(text: &'a str) -> Self {
        let (ast, parser_errors) = ast::parse(text).into_output_errors();

        Self {
            text,
            ast,
            parser_errors,
        }
    }

    pub fn check(&self) -> Vec<AsmError> {
        if let Some(ast::Code { items, span }) = &self.ast {
            asm::check(items, *span)
        } else {
            Vec::new()
        }
    }

    pub fn try_into_valid(self) -> Result<ValidCode<'a>, ast::ParserError> {
        if self.parser_errors.is_empty() {
            if let Some(ast::Code { items, span }) = self.ast {
                return Ok(ValidCode {
                    _text: self.text,
                    span,
                    ast: items,
                });
            }
        }

        Err(self
            .parser_errors
            .into_iter()
            .next()
            .unwrap_or(ast::ParserError::UnknownError))
    }

    pub fn parser_errors(&self) -> &[ast::ParserError] {
        &self.parser_errors
    }
}

pub struct ValidCode<'a> {
    _text: &'a str,
    span: ast::Span,
    ast: Vec<ast::Stmt<'a>>,
}

impl ValidCode<'_> {
    pub fn assemble(&self) -> Result<Cell, asm::AsmError> {
        asm::assemble(&self.ast, self.span)
    }

    pub fn check(self) -> Vec<asm::AsmError> {
        asm::check(&self.ast, self.span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preprocessed_wallet() -> anyhow::Result<()> {
        let cell = Code::assemble(
            r##"
            SETCP0 IFNOTRET                 // msg
            LDREF SWAP DUP HASHCU           // sign msg' hash
            SWAP CTOS LDU 64 LDU 16 PLDREF  // sign hash valid_until msg_seqno actions
            PUSH c4 CTOS                    // sign hash valid_until msg_seqno actions c4s
            LDU 256 PLDU 16                 // sign hash valid_until msg_seqno actions key seqno
            DUP INC PUSHPOW2 16 MOD PUSH s2 // sign hash valid_until msg_seqno actions key seqno new_seqno key
            NEWC STU 256 STU 16 ENDC POP c4 // sign hash valid_until msg_seqno actions key seqno
            XCHG3 s4, s3, s0                // sign hash actions key valid_until seqno
            XCHG s4, s6                     // actions hash sign key valid_until seqno
            EQUAL THROWIFNOT 33             // actions hash sign key valid_until
            NOW GEQ THROWIFNOT 34           // actions hash sign key
            CHKSIGNU THROWIFNOT 35          // actions
            ACCEPT                          // actions
            POP c5
            "##,
        )?;

        assert_eq!(
            cell.repr_hash(),
            &"45ebbce9b5d235886cb6bfe1c3ad93b708de058244892365c9ee0dfe439cb7b5"
                .parse::<HashBytes>()
                .unwrap()
        );

        println!("{}", cell.display_tree());

        Ok(())
    }

    #[test]
    fn stack_ops() -> anyhow::Result<()> {
        let cell = Code::assemble(
            r##"
            XCHG s1, s2
            NOP
            SWAP
            XCHG3 s1, s2, s3
            "##,
        )?;

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
        let cell_tiny = Code::assemble("INT 7")?;
        assert_eq!(cell_tiny.data(), &[0x77]);

        let cell_byte = Code::assemble("INT 120")?;
        assert_eq!(cell_byte.data(), &[0x80, 120]);

        let cell_short = Code::assemble("INT 16000")?;
        assert_eq!(
            cell_short.data(),
            &[0x81, ((16000 >> 8) & 0xff) as u8, ((16000) & 0xff) as u8]
        );

        let cell_big = Code::assemble("INT 123123123123123123")?;
        assert_eq!(cell_big.data(), hex::decode("8229b56bd40163f3b3")?);

        let cell_max = Code::assemble(
            "INT 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        )?;
        assert_eq!(
            cell_max.data(),
            hex::decode("82f0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")?
        );

        let cell_neg_max = Code::assemble(
            "INT -0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        )?;
        assert_eq!(
            cell_neg_max.data(),
            hex::decode("82f70000000000000000000000000000000000000000000000000000000000000001")?
        );

        Ok(())
    }

    #[test]
    fn pushintx() -> anyhow::Result<()> {
        let cell_tiny = Code::assemble("INTX 7")?;
        assert_eq!(cell_tiny.data(), &[0x77]);

        let cell_byte = Code::assemble("INTX 120")?;
        assert_eq!(cell_byte.data(), &[0x80, 120]);

        let cell_short = Code::assemble("INTX 16000")?;
        assert_eq!(
            cell_short.data(),
            &[0x81, ((16000 >> 8) & 0xff) as u8, ((16000) & 0xff) as u8]
        );

        let cell_big = Code::assemble("INTX 123123123123123123")?;
        assert_eq!(cell_big.data(), hex::decode("8229b56bd40163f3b3")?);

        let cell_big = Code::assemble("INTX 90596966400")?;
        assert_eq!(cell_big.data(), hex::decode("8102a3aa1a")?);

        let cell_max = Code::assemble(
            "INTX 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        )?;
        assert_eq!(cell_max.data(), hex::decode("84ff")?);

        let cell_neg_max = Code::assemble(
            "INTX -0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        )?;
        assert_eq!(
            cell_neg_max.data(),
            hex::decode("82f70000000000000000000000000000000000000000000000000000000000000001")?
        );

        Ok(())
    }

    #[test]
    fn display() -> anyhow::Result<()> {
        let code = Code::assemble("PUSHSLICE x{6_}")?;
        println!("{}", code.display_tree());
        Ok(())
    }

    #[test]
    fn complex_asm() -> anyhow::Result<()> {
        const CODE: &str = include_str!("tests/walletv3.tvm");

        let output = Code::assemble(CODE).unwrap();
        assert_eq!(
            output.repr_hash(),
            &"84dafa449f98a6987789ba232358072bc0f76dc4524002a5d0918b9a75d2d599"
                .parse::<HashBytes>()?
        );
        Ok(())
    }

    #[test]
    fn contops() -> anyhow::Result<()> {
        let code = Code::assemble(
            r##"
            CALLXARGS 0, 2
            CALLXARGS 15, 14
            CALLXARGS 1, -1

            CALLCCARGS 0, 2
            CALLCCARGS 15, 14
            CALLCCARGS 1, -1

            SETCONTARGS 0, 2
            SETCONTARGS 15, 14
            SETCONTARGS 1, -1

            BLESSARGS 0, 2
            BLESSARGS 15, 14
            BLESSARGS 1, -1
            "##,
        )?;
        assert_eq!(
            code.repr_hash(),
            &"edb0041119c9381c6426a99abf45236c8192383e14c368775e77aa13e0c5fa79"
                .parse::<HashBytes>()?
        );

        let code1 = Code::assemble(
            r##"
            SETCONTARGS 0, 2
            BLESSARGS 0, 3
            "##,
        )?;
        let code2 = Code::assemble(
            r##"
            SETNUMARGS 2
            BLESSNUMARGS 3
            "##,
        )?;
        assert_eq!(code1, code2);
        Ok(())
    }

    #[test]
    fn stsliceconst() -> anyhow::Result<()> {
        let code = Code::assemble("STSLICECONST x{cf_}")?;
        assert_eq!(code.as_slice_allow_exotic().load_uint(24)?, 0xcf873c);
        Ok(())
    }

    #[test]
    fn runvm() -> anyhow::Result<()> {
        let code = Code::assemble("RUNVM 128")?;
        assert_eq!(code.as_slice_allow_exotic().load_uint(24)?, 0xdb4000 | 128);
        Ok(())
    }

    #[test]
    fn raw_cell() -> anyhow::Result<()> {
        let child_code = "te6ccgEBBAEAHgABFP8A9KQT9LzyyAsBAgLOAwIABaNUQAAJ0IPAWpI=";
        let child_cell = Boc::decode_base64(child_code)?;

        let code = Code::assemble(&format!("PUSHREF {child_code}"))?;
        assert_eq!(code.reference(0).unwrap(), child_cell.as_ref());
        Ok(())
    }

    #[test]
    fn new_cell() -> anyhow::Result<()> {
        let code = Code::assemble("NOP @newcell NOP")?;
        let child_cell = Code::assemble("NOP")?;
        assert_eq!(code.reference(0).unwrap(), child_cell.as_ref());
        Ok(())
    }

    #[test]
    fn dictpushconst() -> anyhow::Result<()> {
        let code = Code::assemble(
            r#"
            SETCP 0
            DICTPUSHCONST 19, [
                0 => {
                    DUP
                    CALLDICT 22
                    INC
                }
                22 => {
                    MUL
                }
            ]
            DICTIGETJMPZ
            THROWARG 11
            "#,
        )?;

        let expected =
            Boc::decode_base64("te6ccgEBBAEAHgABFP8A9KQT9LzyyAsBAgLOAwIABaNUQAAJ0IPAWpI=")?;
        assert_eq!(code, expected);
        Ok(())
    }
}
