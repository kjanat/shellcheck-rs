//! Generates the completion scripts from the option table. The build script
//! compiles this file and writes the scripts the binary embeds.

use fujo_complete::{CompletionOptions, generate_with_config};
use fujo_core::command::{CommandSchema, ProgramSchema};
use fujo_core::parse::ParseOptions;
use fujo_core::schema::{Flag, InputSchema, arg, flag, value};
use rshellcheck_core::{Dialect, optional_checks};

use crate::option_table::{ArgKind, COLORS, OPTS, OptDef, SEVERITIES, SUPPORTED_FORMATS, Shell};

const NAME: &str = "rshellcheck";

fn finish<T, P>(input: Flag<T, P>, def: &OptDef) -> InputSchema {
    let input = input.describe(def.help);
    match def.short {
        Some(short) => input.alias(short.to_string()),
        None => input,
    }
    .into_schema()
}

/// The fujo declaration of one option, with the values its argument takes.
fn declare(def: &OptDef) -> Result<InputSchema, String> {
    if def.kind == ArgKind::None {
        return Ok(finish(flag::boolean(def.long), def));
    }
    Ok(match def.key {
        // A bare `--color` means `always`; only `--color=WHEN` and `-CWHEN`
        // carry a value, and `--color FILE` leaves the word as an input.
        "color" => finish(
            flag::enumeration(def.long, COLORS).optional_value("always".to_string()),
            def,
        ),
        "format" => finish(flag::enumeration(def.long, SUPPORTED_FORMATS), def),
        "shell" => finish(
            flag::enumeration(def.long, Dialect::ALL.map(Dialect::name)),
            def,
        ),
        "severity" => finish(flag::enumeration(def.long, SEVERITIES), def),
        "extended-analysis" => finish(flag::enumeration(def.long, ["true", "false"]), def),
        // A bare `--completions` detects the shell at run time. fujo wants
        // one of the choices as the value of the flag alone; only its own
        // parser reads it, and rshellcheck parses its arguments itself.
        "completions" => finish(
            flag::enumeration(def.long, Shell::ALL.map(Shell::name))
                .optional_value(Shell::Bash.name().to_string()),
            def,
        ),
        "enable" => {
            let names =
                std::iter::once("all").chain(optional_checks().iter().map(|check| check.name));
            finish(
                flag::array(def.long, value::enumeration(names)).separator(','),
                def,
            )
        }
        "rcfile" | "files-from" => finish(flag::path(def.long), def),
        "source-path" => finish(flag::array(def.long, value::path()).separator(':'), def),
        "include" | "exclude" | "jobs" | "wiki-link-count" => {
            finish(flag::string(def.long).value_hint(def.arg), def)
        }
        other => {
            return Err(format!(
                "--{}: no completion declared for `{other}`",
                def.long
            ));
        }
    })
}

/// The completion script for `shell`, generated from the option table.
///
/// # Errors
///
/// An option without a completion declaration, or a table fujo rejects.
pub fn generate(shell: Shell) -> Result<String, String> {
    let command = OPTS
        .iter()
        .map(declare)
        .try_fold(CommandSchema::new(NAME), |command, flag| {
            flag.map(|flag| command.flag(flag))
        })?
        .arg(arg::path("files").variadic().into_schema());
    command.validate().map_err(|e| e.message)?;
    // `ProgramSchema::new` enables no builtins: rshellcheck declares its own
    // `--help` and `--version`.
    let program = ProgramSchema::new(NAME).default(command);
    let shell = match shell {
        Shell::Bash => fujo_complete::Shell::Bash,
        Shell::Zsh => fujo_complete::Shell::Zsh,
        Shell::Fish => fujo_complete::Shell::Fish,
        Shell::Powershell => fujo_complete::Shell::PowerShell,
    };
    Ok(generate_with_config(
        &program,
        shell,
        CompletionOptions {
            // `case_parity` would add spellings such as `--checkSourced` that
            // rshellcheck rejects.
            parse: ParseOptions { case_parity: false },
            // The option parser resolves a unique prefix such as `--for`.
            abbreviate_long_options: true,
        },
    ))
}

#[cfg(test)]
mod tests {
    use fujo_core::schema::ValueArity;

    use super::*;
    use crate::completions;

    fn option(key: &'static str, kind: ArgKind) -> OptDef {
        OptDef {
            short: None,
            long: "probe",
            key,
            kind,
            arg: "VALUE",
            help: "",
        }
    }

    #[test]
    fn a_value_option_without_a_declaration_is_an_error() {
        assert_eq!(
            declare(&option("probe", ArgKind::Required)).map(|_| ()),
            Err("--probe: no completion declared for `probe`".to_string())
        );
        assert_eq!(
            declare(&option("probe", ArgKind::Optional)).map(|_| ()),
            Err("--probe: no completion declared for `probe`".to_string())
        );
        assert!(declare(&option("probe", ArgKind::None)).is_ok());
    }

    #[test]
    fn every_option_declares_the_argument_kind_of_the_table() {
        for def in OPTS {
            let schema = declare(def).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(schema.name, def.long);
            let arity = match def.kind {
                ArgKind::None => ValueArity::None,
                ArgKind::Required => ValueArity::Required,
                ArgKind::Optional => ValueArity::Optional,
            };
            assert_eq!(schema.value_arity, arity, "--{}", def.long);
        }
    }

    #[test]
    fn the_embedded_scripts_are_the_generated_ones() {
        for shell in Shell::ALL {
            assert_eq!(generate(shell).as_deref(), Ok(completions::script(shell)));
        }
    }
}
