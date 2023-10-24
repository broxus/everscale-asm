pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub struct SourceMeta {
    pub line_lengths: Vec<usize>,
}

impl SourceMeta {
    pub fn new(text: &str) -> Self {
        let line_lengths = text.split_inclusive('\n').map(|x| x.len()).collect();
        Self { line_lengths }
    }

    pub fn byte_index_to_position(&self, index: usize) -> anyhow::Result<Position> {
        if index == 0 {
            return Ok(Position::default());
        }

        let mut chars_read = 0;
        for (i, &line_length) in self.line_lengths.iter().enumerate() {
            let line_number = i;
            let first_char_pos = chars_read;
            let last_char_pos = chars_read + line_length;
            if index >= first_char_pos
                && (index < last_char_pos
                    || i + 1 == self.line_lengths.len() && index == last_char_pos)
            {
                return Ok(Position {
                    line: line_number,
                    character: (index - first_char_pos),
                    first_char_pos,
                    last_char_pos,
                    line_length,
                });
            }
            chars_read += line_length;
        }
        anyhow::bail!("Source index out of range: {index}");
    }
}

#[derive(Default)]
pub struct Position {
    pub line: usize,
    pub character: usize,
    pub first_char_pos: usize,
    pub last_char_pos: usize,
    pub line_length: usize,
}

pub struct ArgsOrVersion<T>(pub T);

impl<T: argh::FromArgs> argh::TopLevelCommand for ArgsOrVersion<T> {}

impl<T: argh::FromArgs> argh::FromArgs for ArgsOrVersion<T> {
    fn from_args(command_name: &[&str], args: &[&str]) -> Result<Self, argh::EarlyExit> {
        /// Also use argh for catching `--version`-only invocations
        #[derive(Debug, argh::FromArgs)]
        struct Version {
            /// print version information and exit
            #[argh(switch, short = 'v')]
            pub version: bool,
        }

        match Version::from_args(command_name, args) {
            Ok(v) if v.version => Err(argh::EarlyExit {
                output: format!("{} {}", command_name.first().unwrap_or(&""), VERSION),
                status: Ok(()),
            }),
            Err(exit) if exit.status.is_ok() => {
                let help = match T::from_args(command_name, &["--help"]) {
                    Ok(_) => unreachable!(),
                    Err(exit) => exit.output,
                };
                Err(argh::EarlyExit {
                    output: format!("{help}  -v, --version     print version information and exit"),
                    status: Ok(()),
                })
            }
            _ => T::from_args(command_name, args).map(|app| Self(app)),
        }
    }
}
