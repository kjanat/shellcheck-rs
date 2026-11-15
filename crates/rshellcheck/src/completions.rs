//! Shell completion scripts for `rshellcheck`.
//!
//! The build script generates them from the option table with
//! `fujo-complete`, and the binary embeds the result.

use std::ffi::OsString;

pub use crate::option_table::Shell;

/// The shell a `--completions` value names: a bare name (`zsh`), an
/// interpreter path (`/bin/zsh`) or a Windows executable (`pwsh.exe`).
#[must_use]
pub fn from_name(raw: &str) -> Option<Shell> {
    let base = raw.rsplit(['/', '\\']).next().unwrap_or(raw);
    let name = [".exe", ".cmd", ".bat"]
        .iter()
        .find_map(|extension| {
            base.len()
                .checked_sub(extension.len())
                .filter(|&at| {
                    base.is_char_boundary(at) && base[at..].eq_ignore_ascii_case(extension)
                })
                .map(|at| &base[..at])
        })
        .unwrap_or(base);
    if name == "pwsh" {
        return Some(Shell::Powershell);
    }
    Shell::ALL.into_iter().find(|shell| shell.name() == name)
}

/// The shell a bare `--completions` writes for. `$SHELL` wins when it names
/// a supported shell; PowerShell sets no `$SHELL` but always exports
/// `PSModulePath`.
#[must_use]
pub fn detect(env: &dyn Fn(&str) -> Option<OsString>) -> Option<Shell> {
    env("SHELL")
        .and_then(|shell| from_name(&shell.to_string_lossy()))
        .or_else(|| env("PSModulePath").map(|_| Shell::Powershell))
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
    fn a_shell_is_named_by_its_name_path_or_executable() {
        for shell in Shell::ALL {
            assert_eq!(from_name(shell.name()), Some(shell));
        }
        for (raw, shell) in [
            ("/bin/zsh", Shell::Zsh),
            ("/usr/local/bin/fish", Shell::Fish),
            ("pwsh", Shell::Powershell),
            (
                "C:\\Program Files\\PowerShell\\7\\pwsh.exe",
                Shell::Powershell,
            ),
            ("powershell.EXE", Shell::Powershell),
            ("bash.cmd", Shell::Bash),
        ] {
            assert_eq!(from_name(raw), Some(shell), "{raw}");
        }
        for raw in ["", "Bash", "/bin/sh", "/bin/dash", "zsh.sh", "exe"] {
            assert_eq!(from_name(raw), None, "{raw}");
        }
    }

    fn env(pairs: &'static [(&'static str, &'static str)]) -> impl Fn(&str) -> Option<OsString> {
        move |key| {
            pairs
                .iter()
                .find(|(name, _)| *name == key)
                .map(|(_, value)| OsString::from(value))
        }
    }

    #[test]
    fn the_login_shell_wins_and_powershell_is_its_fallback() {
        assert_eq!(detect(&env(&[("SHELL", "/bin/zsh")])), Some(Shell::Zsh));
        assert_eq!(
            detect(&env(&[("SHELL", "/bin/bash"), ("PSModulePath", "C:\\m")])),
            Some(Shell::Bash)
        );
        assert_eq!(
            detect(&env(&[("SHELL", "/bin/dash"), ("PSModulePath", "C:\\m")])),
            Some(Shell::Powershell)
        );
        assert_eq!(
            detect(&env(&[("PSModulePath", "")])),
            Some(Shell::Powershell)
        );
        assert_eq!(detect(&env(&[("SHELL", "/bin/dash")])), None);
        assert_eq!(detect(&env(&[])), None);
    }

    #[test]
    fn every_shell_has_its_own_script() {
        assert!(script(Shell::Zsh).starts_with("#compdef rshellcheck\n"));
        assert!(script(Shell::Bash).contains("complete -F"));
        assert!(script(Shell::Fish).contains("complete -c 'rshellcheck'"));
        assert!(script(Shell::Powershell).contains("Register-ArgumentCompleter"));
    }
}
