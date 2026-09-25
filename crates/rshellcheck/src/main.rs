mod report;
mod sources;

use std::io::{IsTerminal, Write};
use std::process::ExitCode;
use std::rc::Rc;

use clap::{Parser, ValueEnum};

use report::{Checked, Comment, Edit, FileComments, Format, Level, Line, Outcome, Report, Span};
use sources::{Config, IoFailure, Sources};

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[derive(Parser)]
#[command(
    name = "rshellcheck",
    disable_version_flag = true,
    args_override_self = true,
    about = "ShellCheck's analysis, compiled from its Haskell source to Rust"
)]
struct Cli {
    /// Include warnings from sourced files.
    #[arg(short = 'a', long)]
    check_sourced: bool,
    /// Use color.
    #[arg(
        short = 'C',
        long,
        value_enum,
        value_name = "WHEN",
        default_value_t = Color::Auto,
        num_args = 0..=1,
        require_equals = true,
        default_missing_value = "always"
    )]
    color: Color,
    /// Consider only given types of warnings.
    #[arg(short = 'i', long, value_delimiter = ',', value_name = "CODE1,CODE2..")]
    include: Vec<String>,
    /// Exclude types of warnings.
    #[arg(short = 'e', long, value_delimiter = ',', value_name = "CODE1,CODE2..")]
    exclude: Vec<String>,
    /// Perform dataflow analysis (default true).
    #[arg(long, value_name = "BOOL")]
    extended_analysis: Option<bool>,
    /// Output format.
    #[arg(short = 'f', long, value_enum, default_value_t = Format::Tty)]
    format: Format,
    /// List checks disabled by default.
    #[arg(long)]
    list_optional: bool,
    /// Don't look for .shellcheckrc files.
    #[arg(long)]
    norc: bool,
    /// Prefer the specified configuration file over searching for one.
    #[arg(long, value_name = "RCFILE")]
    rcfile: Option<String>,
    /// List of optional checks to enable (or 'all').
    #[arg(
        short = 'o',
        long,
        value_delimiter = ',',
        value_name = "check1,check2.."
    )]
    enable: Vec<String>,
    /// Specify path when looking for sourced files ("SCRIPTDIR" for script's dir).
    #[arg(short = 'P', long, value_delimiter = ':', value_name = "SOURCEPATHS")]
    source_path: Vec<String>,
    /// Specify dialect.
    #[arg(short = 's', long, value_parser = SHELLS, value_name = "SHELLNAME")]
    shell: Option<String>,
    /// Minimum severity of errors to consider.
    #[arg(short = 'S', long, value_enum, default_value_t = Severity::Style)]
    severity: Severity,
    /// Print version information.
    #[arg(short = 'V', long)]
    version: bool,
    /// The number of wiki links to show, when applicable.
    #[arg(short = 'W', long, default_value_t = 3, value_name = "NUM")]
    wiki_link_count: usize,
    /// Allow 'source' outside of FILES.
    #[arg(short = 'x', long)]
    external_sources: bool,
    /// Read input files from FILE (one per line, or '-' for stdin).
    #[arg(long, value_name = "FILE")]
    files_from: Vec<String>,
    /// Scripts to check; `-` reads standard input.
    #[arg(required_unless_present_any = ["files_from", "version", "list_optional"])]
    files: Vec<String>,
}

const SHELLS: [&str; 12] = [
    "sh",
    "bash",
    "bats",
    "busybox",
    "busybox sh",
    "busybox ash",
    "dash",
    "ash",
    "ksh",
    "ksh88",
    "ksh93",
    "oksh",
];

#[derive(Clone, Copy, ValueEnum)]
enum Color {
    Auto,
    Always,
    Never,
}

#[derive(Clone, Copy, ValueEnum)]
enum Severity {
    Error,
    Warning,
    Info,
    Style,
}

fn main() -> ExitCode {
    let mut arguments = std::env::args_os();
    let program = arguments.next().unwrap_or_default();
    let environment = std::env::var_os("SHELLCHECK_OPTS")
        .map(|options| {
            options
                .to_string_lossy()
                .split(' ')
                .filter(|option| !option.is_empty())
                .map(Into::into)
                .collect::<Vec<std::ffi::OsString>>()
        })
        .unwrap_or_default();
    let cli =
        match Cli::try_parse_from(std::iter::once(program).chain(environment).chain(arguments)) {
            Ok(cli) => cli,
            Err(error) => {
                let usage = error.use_stderr();
                return match error.print() {
                    Ok(()) => ExitCode::from(if usage { 3 } else { 0 }),
                    Err(_) => ExitCode::FAILURE,
                };
            }
        };
    let (included, excluded) = match (codes(&cli.include), codes(&cli.exclude)) {
        (Ok(included), Ok(excluded)) => (included, excluded),
        (Err(error), _) | (_, Err(error)) => {
            eprintln!("{error}");
            return ExitCode::from(3);
        }
    };
    ExitCode::from(shellcheck_core::on_program_stack(move || {
        if cli.version {
            print_version();
            0
        } else if cli.list_optional {
            print_optional();
            0
        } else {
            run(&cli, included, excluded)
        }
    }))
}

fn print_version() {
    println!("ShellCheck - shell script analysis tool");
    println!("version: {}", shellcheck_core::version());
    println!("license: GNU General Public License, version 3");
    println!("website: https://www.shellcheck.net");
}

fn print_optional() {
    for (name, description, example, fix) in shellcheck_core::optional() {
        println!("name:    {name}");
        println!("desc:    {description}");
        println!("example: {example}");
        println!("fix:     {fix}");
        println!();
    }
}

fn codes(texts: &[String]) -> Result<Vec<i64>, String> {
    texts
        .iter()
        .filter(|text| !text.is_empty())
        .map(|text| {
            let mut number = text.as_str();
            while let Some(rest) = number.strip_prefix("SC") {
                number = rest;
            }
            number
                .parse()
                .ok()
                .filter(|_| number.bytes().all(|byte| byte.is_ascii_digit()))
                .ok_or_else(|| format!("Invalid number: {number}"))
        })
        .collect()
}

fn haskell_space(c: char) -> bool {
    match c {
        ' ' | '\t'..='\r' | '\u{a0}' => true,
        '\u{2028}' | '\u{2029}' => false,
        c => c > '\u{377}' && c.is_whitespace(),
    }
}

fn file_list(path: &str) -> Result<Vec<String>, String> {
    let text = if path == "-" {
        let mut text = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin().lock(), &mut text)
            .map_err(|error| IoFailure::new("<stdin>", "hGetContents", &error).to_string())?;
        text
    } else {
        let bytes = std::fs::read(path)
            .map_err(|error| IoFailure::new(path, "openFile", &error).to_string())?;
        match String::from_utf8(bytes) {
            Ok(text) => text,
            Err(_) => {
                return Err(format!(
                    "{path}: hGetContents: invalid argument (invalid byte sequence)"
                ));
            }
        }
    };
    Ok(text
        .lines()
        .map(|line| line.trim_matches(haskell_space))
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_string)
        .collect())
}

fn run(cli: &Cli, included: Vec<i64>, excluded: Vec<i64>) -> u8 {
    let mut files = Vec::new();
    for path in &cli.files_from {
        match file_list(path) {
            Ok(listed) => files.extend(listed),
            Err(error) => {
                eprintln!("Could not read file list: {path}: {error}");
                return 2;
            }
        }
    }
    files.extend(cli.files.iter().cloned());
    let color = match cli.color {
        Color::Always => true,
        Color::Never => false,
        Color::Auto => {
            std::io::stdout().is_terminal()
                && std::env::var("TERM").is_ok_and(|term| !term.is_empty() && term != "dumb")
        }
    };
    let checker = Checker {
        cli,
        included,
        excluded,
        color,
        sources: Rc::new(Sources::new(
            cli.external_sources,
            &files,
            cli.source_path
                .iter()
                .map(|path| {
                    if path.is_empty() {
                        ".".into()
                    } else {
                        path.clone()
                    }
                })
                .collect(),
        )),
        config: Config::new(cli.rcfile.clone()),
    };
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    checker.report(&files, &mut out).expect("writing to stdout")
}

struct Checker<'a> {
    cli: &'a Cli,
    included: Vec<i64>,
    excluded: Vec<i64>,
    color: bool,
    sources: Rc<Sources>,
    config: Config,
}

impl Checker<'_> {
    fn report(&self, files: &[String], out: &mut impl Write) -> std::io::Result<u8> {
        let mut report = Report::new(self.cli.format, self.color, self.cli.wiki_link_count);
        let mut status = 0;
        report.header(out)?;
        for file in files {
            let outcome = match self.sources.read(None, file) {
                Ok(script) => Outcome::Checked(self.check(file, script)),
                Err(error) => Outcome::Unreadable {
                    file: file.clone(),
                    error,
                },
            };
            let problems = match &outcome {
                Outcome::Checked(checked) => u8::from(checked.has_comments()),
                Outcome::Unreadable { .. } => 2,
            };
            if self.cli.format == Format::Quiet && problems > 0 {
                return Ok(1);
            }
            status = status.max(problems);
            report.file(out, &outcome)?;
        }
        report.footer(out)?;
        out.flush()?;
        Ok(status)
    }

    fn check(&self, file: &str, script: String) -> Checked {
        let cli = self.cli;
        let severity = match cli.severity {
            Severity::Error => 0,
            Severity::Warning => 1,
            Severity::Info => 2,
            Severity::Style => 3,
        };
        let finder = self.sources.clone();
        let reader = self.sources.clone();
        let (groups, diffs) = shellcheck_core::lint(
            cli.check_sourced,
            cli.norc,
            self.excluded.clone(),
            (!self.included.is_empty()).then(|| self.included.clone()),
            cli.shell.clone(),
            severity,
            cli.extended_analysis,
            cli.enable.clone(),
            if cli.norc {
                None
            } else {
                self.config.lookup(file)
            },
            Rc::new(move |current, external, annotations, original| {
                finder.find(&current, external, &annotations, &original)
            }),
            Rc::new(move |external, file| reader.read(external, &file)),
            cli.format == Format::Tty,
            matches!(cli.format, Format::Json | Format::Json1),
            (cli.format == Format::Diff).then_some(self.color),
            file.to_string(),
            script,
        );
        Checked {
            file: file.to_string(),
            groups: groups
                .into_iter()
                .map(|(name, lines)| FileComments {
                    name,
                    lines: lines
                        .into_iter()
                        .map(|(number, source, fixed, comments)| Line {
                            number,
                            source,
                            fixed,
                            comments: comments.into_iter().map(comment).collect(),
                        })
                        .collect(),
                })
                .collect(),
            diffs,
        }
    }
}

type RawSpan = (i64, i64, i64, i64);
type RawEdit = (RawSpan, bool, i64, String);

fn span((line, column, end_line, end_column): RawSpan) -> Span {
    Span {
        line,
        column,
        end_line,
        end_column,
    }
}

fn edits(raw: Option<Vec<RawEdit>>) -> Option<Vec<Edit>> {
    raw.map(|edits| {
        edits
            .into_iter()
            .map(|(range, after_end, precedence, replacement)| Edit {
                span: span(range),
                after_end,
                precedence,
                replacement,
            })
            .collect()
    })
}

type RawComment = (
    i64,
    i64,
    String,
    RawSpan,
    RawSpan,
    Option<Vec<RawEdit>>,
    Option<Vec<RawEdit>>,
);

fn comment((level, code, message, expanded, real, expanded_fix, real_fix): RawComment) -> Comment {
    Comment {
        level: Level::from_index(level),
        code,
        message,
        expanded: span(expanded),
        real: span(real),
        expanded_fix: edits(expanded_fix),
        real_fix: edits(real_fix),
    }
}
