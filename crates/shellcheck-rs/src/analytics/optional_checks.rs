//! Authoritative optional-check catalogue shared by the engine and embedders.

use super::{conditions, flow, loops, quoting, redirections};
use crate::analyzer_lib::Checker;

/// One named, opt-in check supported by the engine.
///
/// Obtain descriptors from [`optional_checks`]. The special selector `all`
/// enables every optional check; it is not itself a check in this catalogue.
#[derive(Clone, Copy, Debug)]
pub struct OptionalCheck {
    /// Stable name accepted by `CheckSpec::optional_checks` and `enable=` directives.
    pub name: &'static str,
    /// Human-readable summary of the check.
    pub description: &'static str,
    /// Shell source that demonstrates the problem.
    pub example: &'static str,
    /// Corresponding shell source with the problem corrected.
    pub fix: &'static str,
    implementation: Implementation,
}

#[derive(Clone, Copy, Debug)]
enum Implementation {
    ClarifyParseErrors,
    Analysis(fn(&mut Checker)),
}

impl OptionalCheck {
    pub(crate) fn register(self, checker: &mut Checker) {
        if let Implementation::Analysis(register) = self.implementation {
            register(checker);
        }
    }

    pub(crate) const fn clarifies_parse_errors(self) -> bool {
        matches!(self.implementation, Implementation::ClarifyParseErrors)
    }
}

/// All optional checks, with Rust extensions followed by upstream checks.
///
/// Names, descriptions and examples come from the same catalogue used to
/// enable checks in the engine. The special selector `all` is omitted.
///
/// ```
/// use shellcheck_rs::optional_checks;
///
/// let names: Vec<_> = optional_checks().iter().map(|check| check.name).collect();
/// assert!(names.contains(&"clarify-parse-errors"));
/// assert!(!names.contains(&"all"));
/// ```
#[must_use]
pub const fn optional_checks() -> &'static [OptionalCheck] {
    OPTIONAL_CHECKS
}

pub fn clarify_parse_errors_enabled(name: &str) -> bool {
    name == "all"
        || OPTIONAL_CHECKS
            .iter()
            .any(|check| check.name == name && check.clarifies_parse_errors())
}

const OPTIONAL_CHECKS: &[OptionalCheck] = &[
    OptionalCheck {
        name: "clarify-parse-errors",
        description: "Clarify fatal parser context and empty error messages (Rust extension)",
        example: "((())",
        fix: "((1))",
        implementation: Implementation::ClarifyParseErrors,
    },
    OptionalCheck {
        name: "add-default-case",
        description: "Suggest adding a default case in `case` statements",
        example: "case $? in 0) echo 'Success';; esac",
        fix: "case $? in 0) echo 'Success';; *) echo 'Fail' ;; esac",
        implementation: Implementation::Analysis(|c| c.node(loops::check_default_case)),
    },
    OptionalCheck {
        name: "avoid-negated-conditions",
        description: "Suggest removing unnecessary comparison negations",
        example: "[ ! \"$var\" -eq 1 ]",
        fix: "[ \"$var\" -ne 1 ]",
        implementation: Implementation::Analysis(|c| {
            c.node(conditions::check_unnecessarily_inverted_test);
        }),
    },
    OptionalCheck {
        name: "avoid-nullary-conditions",
        description: "Suggest explicitly using -n in `[ $var ]`",
        example: "[ \"$var\" ]",
        fix: "[ -n \"$var\" ]",
        implementation: Implementation::Analysis(|c| {
            c.node(conditions::check_nullary_expansion_test);
        }),
    },
    OptionalCheck {
        name: "check-extra-masked-returns",
        description: "Check for additional cases where exit codes are masked",
        example: "rm -r \"$(get_chroot_dir)/home\"",
        fix: "set -e; dir=\"$(get_chroot_dir)\"; rm -r \"$dir/home\"",
        implementation: Implementation::Analysis(|c| c.tree(flow::check_extra_masked_returns)),
    },
    OptionalCheck {
        name: "check-set-e-suppressed",
        description: "Notify when set -e is suppressed during function invocation",
        example: "set -e; func() { cp *.txt ~/backup; rm *.txt; }; func && echo ok",
        fix: "set -e; func() { cp *.txt ~/backup; rm *.txt; }; func; echo ok",
        implementation: Implementation::Analysis(|c| c.tree(flow::check_set_e_suppressed)),
    },
    OptionalCheck {
        name: "check-unassigned-uppercase",
        description: "Warn when uppercase variables are unassigned",
        example: "echo $VAR",
        fix: "VAR=hello; echo $VAR",
        implementation: Implementation::Analysis(|c| {
            c.tree(flow::check_unassigned_references_uppercase);
        }),
    },
    OptionalCheck {
        name: "deprecate-which",
        description: "Suggest 'command -v' instead of 'which'",
        example: "which javac",
        fix: "command -v javac",
        implementation: Implementation::Analysis(|c| {
            c.node(crate::checks::commands::coreutils::check_which());
        }),
    },
    OptionalCheck {
        name: "quote-safe-variables",
        description: "Suggest quoting variables without metacharacters",
        example: "var=hello; echo $var",
        fix: "var=hello; echo \"$var\"",
        implementation: Implementation::Analysis(|c| c.node(flow::check_verbose_spacefulness_cfg)),
    },
    OptionalCheck {
        name: "require-double-brackets",
        description: "Require [[ and warn about [ in Bash/Ksh",
        example: "[ -e /etc/issue ]",
        fix: "[[ -e /etc/issue ]]",
        implementation: Implementation::Analysis(|c| {
            c.tree(conditions::check_require_double_bracket);
        }),
    },
    OptionalCheck {
        name: "require-double-equals",
        description: "Require == and warn about = in Bash tests",
        example: "[[ \"$x\" = \"$y\" ]]",
        fix: "[[ \"$x\" == \"$y\" ]]",
        implementation: Implementation::Analysis(|c| {
            c.tree(conditions::check_require_double_equals);
        }),
    },
    OptionalCheck {
        name: "require-variable-braces",
        description: "Suggest putting braces around all variable references",
        example: "var=hello; echo $var",
        fix: "var=hello; echo ${var}",
        implementation: Implementation::Analysis(|c| c.node(quoting::check_variable_braces)),
    },
    OptionalCheck {
        name: "useless-use-of-cat",
        description: "Check for Useless Use Of Cat (UUOC)",
        example: "cat foo | grep bar",
        fix: "grep bar foo",
        implementation: Implementation::Analysis(|c| c.node(redirections::check_uuoc)),
    },
];

#[cfg(test)]
mod tests {
    use super::optional_checks;
    use crate::{CheckSpec, check_script};
    use std::collections::HashSet;

    #[test]
    fn catalogue_names_are_unique_and_exclude_the_all_selector() {
        let mut names = HashSet::new();
        for check in optional_checks() {
            assert_ne!(check.name, "");
            assert_ne!(check.description, "");
            assert!(names.insert(check.name), "duplicate name: {}", check.name);
            assert_ne!(check.name, "all");
        }
    }

    #[test]
    fn catalogue_enables_the_same_checks_as_all() {
        for check in optional_checks() {
            let mut spec = CheckSpec {
                filename: "test.bash".into(),
                script: check.example.into(),
                optional_checks: vec!["all".into()],
                ..CheckSpec::default()
            };
            let all = check_script(&spec);
            spec.optional_checks = optional_checks()
                .iter()
                .map(|check| check.name.into())
                .collect();
            assert_eq!(check_script(&spec), all, "{}", check.name);
        }
    }
}
