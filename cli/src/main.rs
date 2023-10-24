use std::io::{IsTerminal, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result};
use argh::FromArgs;
use console::style;
use everscale_types::boc::Boc;
use unicode_width::UnicodeWidthStr;

use crate::util::*;

mod util;

fn main() -> ExitCode {
    let ArgsOrVersion::<App>(app) = argh::from_env();
    let res = match app.cmd {
        Cmd::Build(cmd) => cmd.run(),
    };

    match res {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e:?}");
            ExitCode::FAILURE
        }
    }
}

/// TVM Assembler
#[derive(FromArgs)]
struct App {
    #[argh(subcommand)]
    cmd: Cmd,
}

#[derive(FromArgs)]
#[argh(subcommand)]
enum Cmd {
    Build(CmdBuild),
}

/// Builds .tvm file into a new cell with code
#[derive(FromArgs)]
#[argh(subcommand, name = "build")]
struct CmdBuild {
    /// path to the input file with assembly code
    #[argh(positional)]
    input: PathBuf,
    /// optional path to the output file
    #[argh(option, short = 'o')]
    out: Option<PathBuf>,
    /// output build info as JSON by default
    #[argh(switch)]
    json: bool,
}

impl CmdBuild {
    fn run(self) -> Result<()> {
        let code = std::fs::read_to_string(&self.input).with_context(|| {
            format!(
                "Failed to read assembly code from `{}`",
                self.input.display()
            )
        })?;

        let out = match self.out {
            Some(path) => path,
            None => {
                let mut out = self.input.clone();
                out.set_extension("boc");
                out
            }
        };
        anyhow::ensure!(self.input != out, "Output file must not be an input file");

        let meta = SourceMeta::new(&code);

        let parsed = everscale_asm::Code::parse(&code);
        if !parsed.parser_errors().is_empty() {
            for error in parsed.parser_errors() {
                if let Some(error) = error.as_report(&self.input, &code, &meta) {
                    eprintln!("{error}\n");
                }
            }

            print_asm_errors(&self.input, &code, &meta, &parsed.check());
            anyhow::bail!("Build failed");
        }

        let parsed = parsed.try_into_valid()?;
        match parsed.assemble() {
            Ok(code) => {
                let mut file = std::fs::File::create(&out)
                    .with_context(|| format!("Failed to open output file `{}`", out.display()))?;

                file.write_all(&Boc::encode(&code))
                    .context("Failed to write the code")?;

                let stats = code
                    .compute_unique_stats(10000)
                    .context("Code is too big")?;

                if !self.json && std::io::stdin().is_terminal() {
                    eprintln!(
                        "Code path:\t{}\n\
                        Code hash:\t{}\n\
                        Unique cells:\t{}\n\
                        Unique bits:\t{}",
                        out.display(),
                        code.repr_hash(),
                        stats.cell_count,
                        stats.bit_count,
                    );
                } else {
                    let output = serde_json::to_string_pretty(&serde_json::json!({
                        "code_path": out.display().to_string(),
                        "code_hash": code.repr_hash().to_string(),
                        "cell_count": stats.cell_count,
                        "bit_count": stats.bit_count,
                    }))?;
                    println!("{output}");
                }
                Ok(())
            }
            Err(_) => {
                print_asm_errors(&self.input, &code, &meta, &parsed.check());
                anyhow::bail!("Build failed");
            }
        }
    }
}

fn print_asm_errors(
    path: &Path,
    code: &str,
    meta: &SourceMeta,
    errors: &[everscale_asm::AsmError],
) {
    for error in errors {
        match error {
            everscale_asm::AsmError::Multiple(errors) => print_asm_errors(path, code, meta, errors),
            everscale_asm::AsmError::ArgTypeMismatch {
                found: everscale_asm::ArgType::Invalid,
                ..
            } => continue,
            _ => {
                if let Some(error) = error.as_report(path, code, meta) {
                    eprintln!("{error}\n");
                }
            }
        }
    }
}

trait AsReport {
    fn as_report<'a>(
        &'a self,
        path: &'a Path,
        code: &'a str,
        meta: &'a SourceMeta,
    ) -> Option<Report<'a>>;
}

impl AsReport for everscale_asm::ParserError {
    fn as_report<'a>(
        &'a self,
        path: &'a Path,
        code: &'a str,
        meta: &'a SourceMeta,
    ) -> Option<Report<'a>> {
        let span = self.span()?;
        Some(Report {
            start: meta.byte_index_to_position(span.start).unwrap(),
            end: meta.byte_index_to_position(span.end).unwrap(),
            file_name: path,
            code,
            origin: "parser",
            error: self,
        })
    }
}

impl AsReport for everscale_asm::AsmError {
    fn as_report<'a>(
        &'a self,
        path: &'a Path,
        code: &'a str,
        meta: &'a SourceMeta,
    ) -> Option<Report<'a>> {
        let span = self.span();
        Some(Report {
            start: meta.byte_index_to_position(span.start).unwrap(),
            end: meta.byte_index_to_position(span.end).unwrap(),
            file_name: path,
            code,
            origin: "asm",
            error: self,
        })
    }
}

struct Report<'a> {
    start: Position,
    end: Position,
    file_name: &'a Path,
    code: &'a str,
    origin: &'a str,
    error: &'a dyn std::fmt::Display,
}

impl std::fmt::Display for Report<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let line_number = (self.start.line + 1).to_string();
        let offset_len = line_number.len();
        let offset = format!("{:offset_len$}", "");

        let arrow = style("-->").blue().bold();
        let block = style("|").blue().bold();
        let line_number = style(line_number).blue().bold();

        let line = self.code[self.start.first_char_pos..self.start.last_char_pos].trim_end();
        let word_start = std::cmp::min(self.start.character, line.len());
        let word_end = std::cmp::min(
            {
                if self.end.line == self.start.line {
                    self.end.character
                } else {
                    self.start.last_char_pos
                }
            },
            line.len(),
        );
        let (line_start, rest) = line.split_at(word_start);
        let (underlined, line_end) = rest.split_at(word_end - word_start);

        let line_start_len = UnicodeWidthStr::width(line_start);
        let underlined_len = UnicodeWidthStr::width(underlined);

        write!(
            f,
            "{}{}\n\
            {offset}{arrow} {}:{}:{}\n\
            {offset} {block}\n\
            {line_number} {block} {}{}{}\n\
            {offset} {block} {:line_start_len$}{}\n\
            {offset} {block}",
            style(format!("error[{}]: ", self.origin)).red(),
            style(self.error).bold(),
            self.file_name.display(),
            self.start.line + 1,
            self.start.character + 1,
            line_start,
            style(underlined).red(),
            line_end,
            "",
            style(format!("{:->1$}", "", underlined_len)).red(),
        )
    }
}
