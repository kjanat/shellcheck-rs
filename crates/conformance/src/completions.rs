use std::path::Path;

use rshellcheck::completions::{Shell, generate};

pub const DIR: &str = "crates/shellcheck-cli/completions";

pub fn write_to(dir: &Path) -> Result<(), String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for shell in Shell::ALL {
        let path = dir.join(shell.file_name());
        std::fs::write(&path, generate(shell)?).map_err(|e| format!("{}: {e}", path.display()))?;
        println!("wrote {}", path.display());
    }
    Ok(())
}

pub fn run() -> Result<bool, String> {
    write_to(Path::new(DIR)).map(|()| true)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn committed(shell: Shell) {
        assert_eq!(
            generate(shell).unwrap(),
            shell.script(),
            "run `cargo completions`"
        );
    }

    #[test]
    fn the_bash_completion_is_committed() {
        committed(Shell::Bash);
    }

    #[test]
    fn the_zsh_completion_is_committed() {
        committed(Shell::Zsh);
    }

    #[test]
    fn the_fish_completion_is_committed() {
        committed(Shell::Fish);
    }

    #[test]
    fn the_powershell_completion_is_committed() {
        committed(Shell::PowerShell);
    }
}
