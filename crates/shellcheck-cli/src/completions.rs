//! Shell completion scripts for `rshellcheck`.
//!
//! The scripts in `completions/` are generated from the option table by
//! `cargo completions` and embedded in the binary, so a default build pulls in
//! no completion generator. The `completions` feature holds the generator.

/// A shell `--generate-completions` writes a script for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shell {
    /// GNU Bash.
    Bash,
    /// Zsh.
    Zsh,
    /// Fish.
    Fish,
    /// PowerShell.
    PowerShell,
}

impl Shell {
    /// Every shell with a completion script.
    pub const ALL: [Self; 4] = [Self::Bash, Self::Zsh, Self::Fish, Self::PowerShell];

    /// The `--generate-completions` value naming this shell.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Bash => "bash",
            Self::Zsh => "zsh",
            Self::Fish => "fish",
            Self::PowerShell => "powershell",
        }
    }

    /// The shell a `--generate-completions` value names.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|shell| shell.name() == name)
    }

    /// The script's file name in `completions/` and in release archives, as
    /// each shell's completion directory expects it.
    #[must_use]
    pub const fn file_name(self) -> &'static str {
        match self {
            Self::Bash => "rshellcheck.bash",
            Self::Zsh => "_rshellcheck",
            Self::Fish => "rshellcheck.fish",
            Self::PowerShell => "rshellcheck.ps1",
        }
    }

    /// The completion script for this shell.
    #[must_use]
    pub const fn script(self) -> &'static str {
        match self {
            Self::Bash => include_str!("../completions/rshellcheck.bash"),
            Self::Zsh => include_str!("../completions/_rshellcheck"),
            Self::Fish => include_str!("../completions/rshellcheck.fish"),
            Self::PowerShell => include_str!("../completions/rshellcheck.ps1"),
        }
    }
}

#[cfg(feature = "completions")]
mod generator {
    use fujo_complete::generate_with_options;
    use fujo_core::command::{Builtins, CommandSchema, ProgramSchema};
    use fujo_core::parse::ParseOptions;
    use fujo_core::schema::{Flag, InputSchema, arg, flag, value};
    use rshellcheck_core::{Dialect, optional_checks};

    use super::Shell;
    use crate::options::{ArgKind, OPTS, OptDef, SEVERITIES, SUPPORTED_FORMATS};

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
                finish(flag::string(def.long), def)
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
            Shell::PowerShell => fujo_complete::Shell::PowerShell,
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
    }
}

#[cfg(feature = "completions")]
pub use generator::generate;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_shell_is_named_by_its_own_name_only() {
        for shell in Shell::ALL {
            assert_eq!(Shell::from_name(shell.name()), Some(shell));
        }
        assert_eq!(Shell::from_name("pwsh"), None);
    }

    #[test]
    fn every_shell_has_its_own_script() {
        for shell in Shell::ALL {
            assert!(shell.script().contains("rshellcheck"), "{}", shell.name());
        }
        assert!(Shell::Zsh.script().starts_with("#compdef rshellcheck\n"));
        assert!(Shell::Bash.script().contains("complete -F"));
        assert!(Shell::Fish.script().contains("complete -c 'rshellcheck'"));
        assert!(
            Shell::PowerShell
                .script()
                .contains("Register-ArgumentCompleter")
        );
    }
}
