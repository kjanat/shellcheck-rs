//! Shell completion scripts for `rshellcheck`.
//!
//! The build script generates them from the option table with
//! `fujo-complete`, and the binary embeds the result.

pub use crate::option_table::Shell;

/// The shell a `--generate-completions` value names.
#[must_use]
pub fn from_name(name: &str) -> Option<Shell> {
    Shell::ALL.into_iter().find(|shell| shell.name() == name)
}

/// The completion script for `shell`.
#[must_use]
pub const fn script(shell: Shell) -> &'static str {
    match shell {
        Shell::Bash => include_str!(concat!(env!("OUT_DIR"), "/rshellcheck.bash")),
        Shell::Zsh => include_str!(concat!(env!("OUT_DIR"), "/_rshellcheck")),
        Shell::Fish => include_str!(concat!(env!("OUT_DIR"), "/rshellcheck.fish")),
        Shell::Powershell => include_str!(concat!(env!("OUT_DIR"), "/rshellcheck.ps1")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_shell_is_named_by_its_own_name_only() {
        for shell in Shell::ALL {
            assert_eq!(from_name(shell.name()), Some(shell));
        }
        assert_eq!(from_name("pwsh"), None);
    }

    #[test]
    fn every_shell_has_its_own_script() {
        assert!(script(Shell::Zsh).starts_with("#compdef rshellcheck\n"));
        assert!(script(Shell::Bash).contains("complete -F"));
        assert!(script(Shell::Fish).contains("complete -c 'rshellcheck'"));
        assert!(script(Shell::Powershell).contains("Register-ArgumentCompleter"));
    }
}
