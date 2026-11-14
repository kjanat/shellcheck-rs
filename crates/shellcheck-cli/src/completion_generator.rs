//! Generates the completion scripts from the option table. The build script
//! compiles this file and writes the scripts the binary embeds.

use fujo_complete::generate_with_options;
use fujo_core::command::{Builtins, CommandSchema, ProgramSchema};
use fujo_core::parse::ParseOptions;
use fujo_core::schema::{Flag, InputSchema, arg, flag, value};
use rshellcheck_core::{Dialect, optional_checks};

use crate::option_table::{ArgKind, OPTS, OptDef, SEVERITIES, SUPPORTED_FORMATS, Shell};

const NAME: &str = "rshellcheck";

/// fujo takes choices as a fixed-size array, so a runtime list names its
/// length at the call site.
fn choices<const N: usize>(
    option: &str,
    names: Vec<&'static str>,
) -> Result<[&'static str; N], String> {
    let found = names.len();
    <[&str; N]>::try_from(names)
        .map_err(|_| format!("--{option}: expected {N} choices, found {found}"))
}

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
    // fujo has no optional option argument: a value-taking flag consumes
    // the next word, which `--color FILE` must leave as an input.
    if def.kind != ArgKind::Required {
        return Ok(finish(flag::boolean(def.long), def));
    }
    Ok(match def.key {
        "format" => finish(
            flag::enumeration(
                def.long,
                choices::<7>(def.long, SUPPORTED_FORMATS.to_vec())?,
            ),
            def,
        ),
        "shell" => finish(
            flag::enumeration(def.long, Dialect::ALL.map(Dialect::name)),
            def,
        ),
        "severity" => finish(flag::enumeration(def.long, SEVERITIES), def),
        "extended-analysis" => finish(flag::enumeration(def.long, ["true", "false"]), def),
        "completions" => finish(
            flag::enumeration(def.long, Shell::ALL.map(Shell::name)),
            def,
        ),
        "enable" => {
            let names = std::iter::once("all")
                .chain(optional_checks().iter().map(|check| check.name))
                .collect();
            let names = choices::<14>(def.long, names)?;
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
/// An option without a completion declaration, a choice list whose length
/// differs from the declared one, or a table fujo rejects.
pub fn generate(shell: Shell) -> Result<String, String> {
    let command = CommandSchema {
        name: NAME.to_string(),
        description: String::new(),
        aliases: vec![],
        hidden: false,
        flags: OPTS.iter().map(declare).collect::<Result<_, _>>()?,
        args: vec![arg::path("files").variadic().into_schema()],
        commands: vec![],
        examples: vec![],
    };
    command.validate().map_err(|e| e.message)?;
    let program = ProgramSchema {
        name: NAME.to_string(),
        version: None,
        description: String::new(),
        commands: vec![],
        default: Some(command),
        // rshellcheck declares its own `--help` and `--version`.
        builtins: Builtins {
            help: false,
            json: false,
            quiet: false,
            explain: false,
        },
        completions: false,
        config: false,
        flags: vec![],
    };
    let shell = match shell {
        Shell::Bash => fujo_complete::Shell::Bash,
        Shell::Zsh => fujo_complete::Shell::Zsh,
        Shell::Fish => fujo_complete::Shell::Fish,
        Shell::Powershell => fujo_complete::Shell::PowerShell,
    };
    // `case_parity` would add spellings such as `--checkSourced` that
    // rshellcheck rejects.
    Ok(generate_with_options(
        &program,
        shell,
        ParseOptions { case_parity: false },
    ))
}

#[cfg(test)]
mod tests {
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
        assert!(declare(&option("probe", ArgKind::None)).is_ok());
        assert!(declare(&option("probe", ArgKind::Optional)).is_ok());
    }

    #[test]
    fn a_choice_list_of_another_length_is_an_error() {
        assert_eq!(choices::<2>("probe", vec!["a", "b"]), Ok(["a", "b"]));
        assert_eq!(
            choices::<2>("probe", vec!["a"]),
            Err("--probe: expected 2 choices, found 1".to_string())
        );
    }

    #[test]
    fn every_option_has_a_declaration_and_an_optional_argument_takes_no_word() {
        for def in OPTS {
            let schema = declare(def).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(schema.name, def.long);
            assert_eq!(
                schema.expects_value(),
                def.kind == ArgKind::Required,
                "--{}",
                def.long
            );
        }
    }

    #[test]
    fn the_embedded_scripts_are_the_generated_ones() {
        for shell in Shell::ALL {
            assert_eq!(generate(shell).as_deref(), Ok(completions::script(shell)));
        }
    }
}
