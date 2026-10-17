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
            InnerToken::T_Assignment { var, .. } => dialect == Dialect::Zsh && var == "options",
            _ => false,
        };
        if changes {
            keeps = false;
        }
    });
    keeps
}

fn shebang_sets_options(shebang: &str) -> bool {
    let words: Vec<&str> = shebang.split_whitespace().collect();
    let Some((first, rest)) = words.split_first() else {
        return false;
    };
    if basename(first) != "env" {
        return has_option_flag(rest);
    }
    let interpreter_args: Vec<&str> = rest
        .iter()
        .filter_map(|w| match w.strip_prefix("--split-string=") {
            Some("") => None,
            Some(w) => Some(w),
            None => Some(*w),
        })
        .skip_while(|a| a.starts_with('-') || a.contains('='))
        .skip(1)
        .collect();
    has_option_flag(&interpreter_args)
}

const PRECOMMAND_MODIFIERS: [&str; 6] = ["-", "builtin", "command", "exec", "nocorrect", "noglob"];

fn sets_options(words: &[String]) -> bool {
    let start = words
        .iter()
        .take_while(|w| PRECOMMAND_MODIFIERS.contains(&w.as_str()))
        .count();
    match words[start..].split_first() {
        Some((name, _)) if matches!(name.as_str(), "setopt" | "unsetopt" | "emulate") => true,
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
    fn options_is_an_ordinary_variable_in_other_added_dialects() {
        assert_eq!(
            policy(Dialect::Mksh, "options[0]=on\necho $x\n"),
            Policy::Measured(Dialect::Mksh)
        );
    }
}
