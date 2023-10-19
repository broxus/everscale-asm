use everscale_types::prelude::*;

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
    ast: Vec<ast::Instr<'a>>,
}

impl ValidCode<'_> {
    pub fn assemble(self) -> Result<Cell, asm::AsmError> {
        asm::assemble(&self.ast, self.span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
