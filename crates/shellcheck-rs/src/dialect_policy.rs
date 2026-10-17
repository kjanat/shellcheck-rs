//! Which codes an added dialect keeps, decided by what the validity matrix
//! recorded for it in `dialect_rules.rs`.

use crate::ast::{InnerToken, Token};
use crate::ast_lib::oversimplify;
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
        if dialect.is_added() && keeps_default_options(root) {
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

fn keeps_default_options(root: &Token) -> bool {
    let mut keeps = true;
    root.visit_preorder(&mut |t| {
        if matches!(&*t.inner, InnerToken::T_SimpleCommand { .. }) && sets_options(&oversimplify(t))
        {
            keeps = false;
        }
    });
    keeps
}

fn sets_options(words: &[String]) -> bool {
    match words.split_first() {
        Some((name, _)) if matches!(name.as_str(), "setopt" | "unsetopt" | "emulate") => true,
        Some((name, args)) if name == "set" => args
            .iter()
            .take_while(|a| *a != "--" && *a != "-")
            .any(|a| a.len() > 1 && (a.starts_with('-') || a.starts_with('+'))),
        _ => false,
    }
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
        ] {
            assert_eq!(
                policy(Dialect::Zsh, script),
                Policy::Measured(Dialect::Zsh),
                "{script:?}"
            );
        }
    }
}
