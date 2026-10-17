//! Which codes an added dialect keeps, decided by what the validity matrix
//! recorded for it in `dialect_rules.rs`.

use crate::ast::{InnerToken, Token};
use crate::ast_lib::{basename, oversimplify};
use crate::dialect::Dialect;
use crate::dialect_rules::RULES;

/// What the validity matrix recorded for one diagnostic in one cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// The snippet shows the bug and the fix removes it.
    Reproduces,
    /// Both scripts behave like the fix: the shell lacks the bug.
    Absent,
    /// Some other output.
    Differs,
    /// The shell rejects the snippet or the fix.
    Unparsable,
    /// The run exceeded its limit.
    Timeout,
    /// The port disagreed with the shell about the snippet or the fix.
    PortMiss,
}

/// One recorded cell: the diagnostic's code, the cell's dialect and version.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rule {
    /// The diagnostic the spec claims.
    pub code: i64,
    /// The cell's shell.
    pub dialect: Dialect,
    /// The cell's version.
    pub version: &'static str,
    /// What the cell recorded.
    pub outcome: Outcome,
}

/// The codes one script keeps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Policy {
    /// Every code of the floor dialect.
    Floor,
    /// The codes the matrix recorded for an added dialect under its default options.
    Measured(Dialect),
}

impl Policy {
    /// `Measured` for an added dialect whose script keeps the default options.
    #[must_use]
    pub fn of(dialect: Dialect, root: &Token) -> Self {
        if dialect.is_added() && keeps_default_options(dialect, root) {
            Self::Measured(dialect)
        } else {
            Self::Floor
        }
    }

    /// Whether the script keeps `code`.
    #[must_use]
    pub fn keeps(self, code: i64) -> bool {
        match self {
            Self::Floor => true,
            Self::Measured(dialect) => applies_by(RULES, code, dialect),
        }
    }
}

fn keeps_default_options(dialect: Dialect, root: &Token) -> bool {
    let mut keeps = true;
    root.visit_preorder(&mut |t| {
        let changes = match &*t.inner {
            InnerToken::T_Script { shebang, .. } => {
                matches!(&*shebang.inner, InnerToken::T_Literal(s) if shebang_sets_options(s))
            }
            InnerToken::T_SimpleCommand { .. } => sets_options(&oversimplify(t)),
            InnerToken::T_Assignment { var, .. } => {
                dialect == Dialect::Zsh
                    && matches!(
                        var.as_str(),
                        "options"
                            | "functions"
                            | "dis_functions"
                            | "aliases"
                            | "dis_aliases"
                            | "galiases"
                            | "dis_galiases"
                            | "saliases"
                            | "dis_saliases"
                    )
            }
            _ => false,
        };
        if changes {
            keeps = false;
        }
    });
    keeps
}

fn shebang_sets_options(shebang: &str) -> bool {
    let (first, rest) = shebang
        .trim_start()
        .split_once(char::is_whitespace)
        .unwrap_or_else(|| (shebang.trim(), ""));
    if basename(first) != "env" {
        return has_option_flag(&rest.split_whitespace().collect::<Vec<_>>());
    }
    env_shebang_sets_options(rest)
}

fn env_shebang_sets_options(mut rest: &str) -> bool {
    while !rest.trim_start().is_empty() {
        rest = rest.trim_start();
        let (word, tail) = rest.split_once(char::is_whitespace).unwrap_or((rest, ""));
        let split = rest
            .strip_prefix("-S")
            .or_else(|| rest.strip_prefix("--split-string="))
            .or_else(|| (word == "--split-string").then_some(tail));
        if let Some(payload) = split {
            return crate::env_split::split(payload)
                .is_none_or(|words| env_words_set_options(&words));
        }
        if !env_prefix_word(word) {
            return word.starts_with('-')
                || has_option_flag(&tail.split_whitespace().collect::<Vec<_>>());
        }
        rest = tail;
    }
    true
}

fn env_words_set_options(words: &[String]) -> bool {
    for (index, word) in words.iter().enumerate() {
        if !env_prefix_word(word) {
            // Unknown env options, including nested -S, cannot establish
            // the interpreter's default options without more evaluation.
            return word.is_empty()
                || word.starts_with('-')
                || has_option_flag(&words[index + 1..]);
        }
    }
    true
}

fn env_prefix_word(word: &str) -> bool {
    matches!(
        word,
        "-" | "--" | "-i" | "--ignore-environment" | "-v" | "--debug"
    ) || (!word.starts_with('-') && word.contains('='))
}

const PRECOMMAND_MODIFIERS: [&str; 6] = ["-", "builtin", "command", "exec", "nocorrect", "noglob"];

fn sets_options(words: &[String]) -> bool {
    let start = words
        .iter()
        .take_while(|w| PRECOMMAND_MODIFIERS.contains(&w.as_str()))
        .count();
    match words[start..].split_first() {
        Some((name, _))
            if matches!(
                name.as_str(),
                "setopt" | "unsetopt" | "emulate" | "eval" | "." | "source" | "alias"
            ) =>
        {
            true
        }
        Some((name, args)) if name == "set" => has_option_flag(args),
        _ => false,
    }
}

fn has_option_flag<S: AsRef<str>>(args: &[S]) -> bool {
    args.iter()
        .map(AsRef::as_ref)
        .take_while(|a| *a != "--" && *a != "-")
        .any(|a| a.len() > 1 && (a.starts_with('-') || a.starts_with('+')))
}

fn applies_by(rules: &[Rule], code: i64, dialect: Dialect) -> bool {
    let mut absent = false;
    for rule in rules
        .iter()
        .filter(|r| r.code == code && r.dialect == dialect)
    {
        match rule.outcome {
            Outcome::Reproduces => return true,
            Outcome::Absent => absent = true,
            Outcome::Differs | Outcome::Unparsable | Outcome::Timeout | Outcome::PortMiss => {}
        }
    }
    !absent
}

#[cfg(test)]
mod tests {
    use super::*;

    const fn rule(code: i64, dialect: Dialect, version: &'static str, outcome: Outcome) -> Rule {
        Rule {
            code,
            dialect,
            version,
            outcome,
        }
    }

    #[test]
    fn a_code_with_no_row_for_the_dialect_applies() {
        let rules = [rule(2086, Dialect::Zsh, "5.9", Outcome::Absent)];
        assert!(applies_by(&rules, 2086, Dialect::Mksh));
        assert!(applies_by(&rules, 2164, Dialect::Zsh));
        assert!(applies_by(&[], 2086, Dialect::Zsh));
    }

    #[test]
    fn one_reproducing_version_keeps_the_code_despite_absent_ones() {
        let rules = [
            rule(2086, Dialect::Zsh, "5.8.1", Outcome::Absent),
            rule(2086, Dialect::Zsh, "5.9", Outcome::Reproduces),
            rule(2086, Dialect::Zsh, "5.9.1", Outcome::Absent),
        ];
        assert!(applies_by(&rules, 2086, Dialect::Zsh));
    }

    #[test]
    fn a_code_absent_in_every_version_is_dropped() {
        let rules = [
            rule(2086, Dialect::Zsh, "5.8.1", Outcome::Absent),
            rule(2086, Dialect::Zsh, "5.9", Outcome::Absent),
            rule(2086, Dialect::Zsh, "5.9.1", Outcome::Differs),
        ];
        assert!(!applies_by(&rules, 2086, Dialect::Zsh));
    }

    #[test]
    fn rows_without_a_verdict_carry_no_weight() {
        for outcome in [
            Outcome::Differs,
            Outcome::Unparsable,
            Outcome::Timeout,
            Outcome::PortMiss,
        ] {
            let rules = [rule(2086, Dialect::Osh, "0.38.0", outcome)];
            assert!(applies_by(&rules, 2086, Dialect::Osh), "{outcome:?}");
        }
    }

    fn policy(dialect: Dialect, script: &str) -> Policy {
        let root = crate::parser::parse_script("-", script)
            .root
            .expect("script parses");
        Policy::of(dialect, &root)
    }

    #[test]
    fn the_recorded_table_drops_sc2086_for_zsh_and_keeps_it_for_bash() {
        assert!(!policy(Dialect::Zsh, "echo $x\n").keeps(2086));
        assert!(policy(Dialect::Zsh, "echo $x\n").keeps(2164));
        assert!(policy(Dialect::Bash, "echo $x\n").keeps(2086));
    }

    #[test]
    fn a_script_that_changes_its_options_keeps_the_floor_codes() {
        for script in [
            "setopt SH_WORD_SPLIT\necho $x\n",
            "setopt shwordsplit; echo $x\n",
            "unsetopt NO_SH_WORD_SPLIT\necho $x\n",
            "emulate sh\necho $x\n",
            "set -o shwordsplit\necho $x\n",
            "set +o shwordsplit\necho $x\n",
            "set -y\necho $x\n",
            "set -ey\necho $x\n",
            "set +y\necho $x\n",
            "set -e\necho $x\n",
            "f() { setopt localoptions shwordsplit; echo $x; }\n",
            "builtin setopt SH_WORD_SPLIT\necho $x\n",
            "noglob builtin set -y\necho $x\n",
            "exec emulate sh\necho $x\n",
            "#!/bin/zsh -y\necho $x\n",
            "#!/bin/zsh -o shwordsplit\necho $x\n",
            "#!/bin/zsh --shwordsplit\necho $x\n",
            "#!/usr/bin/env -S zsh -y\necho $x\n",
            "#!/usr/bin/env -Szsh -y\necho $x\n",
            "#!/usr/bin/env -Szsh -o shwordsplit\necho $x\n",
            "#!/usr/bin/env -Szsh -S\necho $x\n",
            "#!/usr/bin/env zsh -S\necho $x\n",
            "#!/usr/bin/env -SLC_ALL=C zsh +y\necho $x\n",
            "#!/usr/bin/env --split-string=zsh -y\necho $x\n",
            "#!/usr/bin/env -S LC_ALL=C zsh +y\necho $x\n",
            "options[SH_WORD_SPLIT]=on\necho $x\n",
            "options[shwordsplit]=on\necho $x\n",
            "options[$name]=on\necho $x\n",
            "options=(shwordsplit on)\necho $x\n",
            "options+=(shwordsplit on)\necho $x\n",
        ] {
            assert_eq!(policy(Dialect::Zsh, script), Policy::Floor, "{script:?}");
            assert!(policy(Dialect::Zsh, script).keeps(2086), "{script:?}");
        }
    }

    #[test]
    fn setting_positional_parameters_keeps_the_measured_codes() {
        for script in [
            "set -- a b\necho $x\n",
            "set a b\necho $x\n",
            "set - a\necho $x\n",
            "set -- -e\necho $x\n",
            "echo setopt $x\n",
            "builtin echo setopt $x\n",
            "command printf '%s' set -e $x\n",
            "#!/bin/zsh\necho $x\n",
            "#!/bin/zsh -\necho $x\n",
            "#!/usr/bin/env zsh\necho $x\n",
            "#!/usr/bin/env -S zsh\necho $x\n",
            "#!/usr/bin/env -Szsh\necho $x\n",
            "#!/usr/bin/env -SLC_ALL=C zsh\necho $x\n",
            "#!/usr/bin/env -S LC_ALL=C zsh\necho $x\n",
            "echo \"${options[shwordsplit]}\"\necho $x\n",
            "echo 'options[shwordsplit]=on'\necho $x\n",
            "other_options[shwordsplit]=on\necho $x\n",
        ] {
            assert_eq!(
                policy(Dialect::Zsh, script),
                Policy::Measured(Dialect::Zsh),
                "{script:?}"
            );
        }
    }

    #[test]
    fn env_split_strings_decode_flags_or_conservatively_keep_the_floor() {
        for arguments in [
            "-S zsh '-y'",
            "-S zsh \"-y\"",
            "-Szsh -'y'",
            "--split-string=zsh '-y'",
            "--split-string zsh '-y'",
            r"-S zsh\_-y",
            "-S zsh ${FLAGS}",
            "-S zsh \"${FLAGS}\"",
            "-S zsh '-y",
            r"-S zsh \q",
            "-S zsh '-S'",
            "-S -u NAME zsh",
            "-S '-S zsh -y'",
            "-vS zsh '-y'",
        ] {
            let script = format!("#!/usr/bin/env {arguments}\necho $x\n");
            assert_eq!(
                policy(Dialect::Zsh, &script),
                Policy::Floor,
                "{arguments:?}"
            );
        }
    }

    #[test]
    fn env_split_literals_and_terminators_do_not_create_flags() {
        for arguments in [
            "-S zsh # '-y'",
            r"-S zsh\c -y",
            "-S zsh '--' '-y'",
            "-S zsh '-'",
            "-S zsh ''",
            "-S LC_ALL='C' zsh",
            "-S zsh '${FLAGS}'",
            r"-S zsh '\_ -y'",
        ] {
            let script = format!("#!/usr/bin/env {arguments}\necho $x\n");
            assert_eq!(
                policy(Dialect::Zsh, &script),
                Policy::Measured(Dialect::Zsh),
                "{arguments:?}"
            );
        }
    }

    #[test]
    fn eval_may_change_options_in_the_current_shell() {
        for script in [
            "eval 'setopt SH_WORD_SPLIT'; echo $x\n",
            "builtin eval 'set -y'; echo $x\n",
            "noglob builtin eval \"$command\"; echo $x\n",
            "eval \"$command\"; echo $x\n",
        ] {
            assert_eq!(policy(Dialect::Zsh, script), Policy::Floor, "{script:?}");
        }
        for script in ["echo eval $x\n", "builtin printf '%s' eval $x\n"] {
            assert_eq!(
                policy(Dialect::Zsh, script),
                Policy::Measured(Dialect::Zsh),
                "{script:?}"
            );
        }
    }

    #[test]
    fn source_may_change_options_in_the_current_shell() {
        for script in [
            ". <(printf 'setopt SH_WORD_SPLIT\\n'); echo $x\n",
            "source \"$path\"; echo $x\n",
            "builtin source \"$path\"; echo $x\n",
            "noglob . \"$path\"; echo $x\n",
        ] {
            assert_eq!(policy(Dialect::Zsh, script), Policy::Floor, "{script:?}");
        }
        for script in ["echo source $x\n", "builtin printf '%s' . $x\n"] {
            assert_eq!(
                policy(Dialect::Zsh, script),
                Policy::Measured(Dialect::Zsh),
                "{script:?}"
            );
        }
    }

    #[test]
    fn aliases_may_change_options_in_the_current_shell() {
        for script in [
            "alias split='setopt SH_WORD_SPLIT'\nsplit\necho $x\n",
            "builtin alias split='set -y'\nsplit\necho $x\n",
            "noglob alias \"$definition\"\nsplit\necho $x\n",
        ] {
            assert_eq!(policy(Dialect::Zsh, script), Policy::Floor, "{script:?}");
        }
        for script in ["echo alias $x\n", "builtin printf '%s' alias $x\n"] {
            assert_eq!(
                policy(Dialect::Zsh, script),
                Policy::Measured(Dialect::Zsh),
                "{script:?}"
            );
        }
    }

    #[test]
    fn function_parameter_writes_may_change_zsh_options() {
        for script in [
            "functions[split]='setopt SH_WORD_SPLIT'; split; echo $x\n",
            "functions[$name]=$body; echo $x\n",
            "functions+=(split 'setopt SH_WORD_SPLIT'); echo $x\n",
            "dis_functions[split]='setopt SH_WORD_SPLIT'; enable -f split; split; echo $x\n",
        ] {
            assert_eq!(policy(Dialect::Zsh, script), Policy::Floor, "{script}");
        }
        for script in [
            "echo \"${functions[split]}\"; echo $x\n",
            "echo 'functions[split]=setopt'; echo $x\n",
            "other_functions[split]=body; echo $x\n",
        ] {
            assert_eq!(policy(Dialect::Zsh, script), Policy::Measured(Dialect::Zsh));
        }
        assert_eq!(
            policy(Dialect::Mksh, "functions[0]=body; echo $x\n"),
            Policy::Measured(Dialect::Mksh)
        );
    }

    #[test]
    fn alias_parameter_writes_may_change_zsh_options() {
        for name in [
            "aliases",
            "dis_aliases",
            "galiases",
            "dis_galiases",
            "saliases",
            "dis_saliases",
        ] {
            let script = format!("{name}[split]='setopt SH_WORD_SPLIT'\nsplit\necho $x\n");
            assert_eq!(policy(Dialect::Zsh, &script), Policy::Floor, "{name}");
            let read = format!("echo \"${{{name}[split]}}\"\necho $x\n");
            assert_eq!(policy(Dialect::Zsh, &read), Policy::Measured(Dialect::Zsh));
            assert_eq!(
                policy(Dialect::Mksh, &script),
                Policy::Measured(Dialect::Mksh)
            );
        }
    }

    #[test]
    fn options_is_an_ordinary_variable_in_other_added_dialects() {
        assert_eq!(
            policy(Dialect::Mksh, "options[0]=on\necho $x\n"),
            Policy::Measured(Dialect::Mksh)
        );
    }
}
