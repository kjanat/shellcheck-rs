//! Which codes an added dialect keeps, decided by what the validity matrix
//! recorded for it in `dialect_rules.rs`.

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

/// Whether `code` applies to `dialect`: yes with no rows or any `Reproduces`
/// row, no when every weighted row is `Absent`. `Differs`, `Unparsable`,
/// `Timeout` and `PortMiss` rows carry no weight.
#[must_use]
pub fn applies(code: i64, dialect: Dialect) -> bool {
    applies_by(RULES, code, dialect)
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

    #[test]
    fn the_recorded_table_drops_sc2086_for_zsh_and_keeps_it_for_bash() {
        assert!(!applies(2086, Dialect::Zsh));
        assert!(applies(2086, Dialect::Bash));
        assert!(applies(2164, Dialect::Zsh));
    }
}
