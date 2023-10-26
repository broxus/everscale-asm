use std::cell::RefCell;

use everscale_asm::Code;
use everscale_types::boc::Boc;
use proc_macro::TokenStream;
use quote::quote;
use quote::ToTokens;
use syn::punctuated::Punctuated;

#[proc_macro]
pub fn tvmasm(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input with Punctuated::<syn::LitStr, syn::Token![,]>::parse_terminated);
    compile(input).unwrap_or_else(to_compile_errors).into()
}

fn compile(
    input: Punctuated<syn::LitStr, syn::Token![,]>,
) -> Result<proc_macro2::TokenStream, Vec<syn::Error>> {
    let source = Source::new(input.iter());

    let ctxt = Ctxt::default();

    let code = Code::parse(&source.text);
    let compiled = if !code.parser_errors().is_empty() {
        for error in code.parser_errors() {
            let span = error.span().and_then(|span| source.find_lit_by_span(span));
            match span {
                None => ctxt.error_spanned_by(&input, error),
                Some(s) => ctxt.error_spanned_by(s, error),
            }
        }

        print_asm_errors(&input, &source, &code.check(), &ctxt);
        ctxt.check()?;

        Vec::new()
    } else {
        let code = code.try_into_valid().unwrap();
        match code.assemble() {
            Ok(code) => Boc::encode(code),
            Err(asm_error) => {
                print_asm_errors(&input, &source, &[asm_error], &ctxt);
                ctxt.check()?;
                Vec::new()
            }
        }
    };

    Ok(quote!( &[#(#compiled),*] ))
}

fn print_asm_errors(
    input: &dyn ToTokens,
    source: &Source,
    errors: &[everscale_asm::AsmError],
    ctxt: &Ctxt,
) {
    for error in errors {
        match error {
            everscale_asm::AsmError::Multiple(errors) => {
                print_asm_errors(input, source, errors, ctxt)
            }
            everscale_asm::AsmError::ArgTypeMismatch {
                found: everscale_asm::ArgType::Invalid,
                ..
            } => continue,
            _ => {
                let span = source.find_lit_by_span(error.span());
                match span {
                    None => ctxt.error_spanned_by(input, error),
                    Some(s) => ctxt.error_spanned_by(s, error),
                }
            }
        }
    }
}

struct Source<'a> {
    text: String,
    parts: Vec<(&'a syn::LitStr, usize)>,
}

impl<'a> Source<'a> {
    fn new<I: Iterator<Item = &'a syn::LitStr>>(input: I) -> Self {
        let mut text = String::new();
        let mut parts = Vec::new();

        for part in input {
            let part_text = part.value();
            let part_len = part_text.len() + 1;

            text.reserve(part_len);
            text.push_str(&part_text);
            text.push('\n');

            parts.push((part, part_len));
        }

        Self { text, parts }
    }

    fn find_lit_by_span(&self, span: everscale_asm::Span) -> Option<&syn::LitStr> {
        let mut offset = 0;
        for (part, part_len) in &self.parts {
            offset += part_len;
            if span.start <= offset {
                return Some(part);
            }
        }

        None
    }
}

#[derive(Default)]
struct Ctxt {
    errors: RefCell<Vec<syn::Error>>,
}

impl Ctxt {
    pub fn error_spanned_by<T, M>(&self, object: T, message: M)
    where
        T: ToTokens,
        M: std::fmt::Display,
    {
        self.errors
            .borrow_mut()
            .push(syn::Error::new_spanned(object.into_token_stream(), message));
    }

    pub fn check(self) -> Result<(), Vec<syn::Error>> {
        let errors = std::mem::take(&mut *self.errors.borrow_mut());
        match errors.len() {
            0 => Ok(()),
            _ => Err(errors),
        }
    }
}

fn to_compile_errors(errors: Vec<syn::Error>) -> proc_macro2::TokenStream {
    let compile_errors = errors.iter().map(syn::Error::to_compile_error);
    quote!(#(#compile_errors)*)
}
