//! Port of `ShellCheck.Analytics` (SC2xxx). Checks are added incrementally and
//! each is validated against the conformance harness. `checker` assembles the
//! registered checks into a [`Checker`].

use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::interface::Shell;

/// Assemble the Analytics checks into a Checker.
pub fn checker() -> Checker {
    let mut c = Checker::new();
    c.tree(check_shebang);
    c.node(check_for_in_quoted);
    c
}

/// `checkShebang` (SC2148 / SC2239 / SC2246 / SC2187).
fn check_shebang(params: &Parameters, t: &Token, out: &mut Out) {
    // Unwrap the T_Annotation root; skip entirely if a ShellOverride is present.
    let script = match &*t.inner {
        InnerToken::T_Annotation { annotations, token } => {
            if annotations.iter().any(|a| matches!(a, Annotation::ShellOverride(_))) {
                return;
            }
            token
        }
        _ => t,
    };
    if let InnerToken::T_Script { shebang, .. } = &*script.inner {
        if let InnerToken::T_Literal(sb) = &*shebang.inner {
            let id = shebang.id();
            if !params.shell_type_specified {
                if sb.is_empty() {
                    err(out, id, 2148,
                        "Tips depend on target shell and yours is unknown. Add a shebang or a 'shell' directive.");
                }
                if astlib::executable_from_shebang(sb) == "ash" {
                    warn(out, id, 2187,
                        "Ash scripts will be checked as Dash. Add '# shellcheck shell=dash' to silence.");
                }
            }
            if !sb.is_empty() {
                if !sb.starts_with('/') {
                    err(out, id, 2239, "Ensure the shebang uses an absolute path to the interpreter.");
                }
                if let Some(first) = sb.split_whitespace().next() {
                    if first.ends_with('/') {
                        err(out, id, 2246, "This shebang specifies a directory. Ensure the interpreter is a file.");
                    }
                }
            }
        }
    }
}

/// `checkForInQuoted` (SC2066 / SC2041 ...): a minimal port covering the common
/// `for f in "$(...)"` / `for f in "literal with spaces"` cases. Kept
/// conservative; refined against the harness.
fn check_for_in_quoted(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_ForIn { items, .. } = &*t.inner {
        if items.len() == 1 {
            let word = &items[0];
            if let InnerToken::T_NormalWord(parts) = &*word.inner {
                // Single double-quoted part that isn't purely "$@"/"$*"/array.
                if parts.len() == 1 {
                    if let InnerToken::T_DoubleQuoted(inner) = &*parts[0].inner {
                        let is_special = inner.len() == 1
                            && matches!(&*inner[0].inner,
                                InnerToken::T_DollarBraced { .. });
                        let has_space_literal = inner.iter().any(|p| matches!(&*p.inner, InnerToken::T_Literal(s) if s.contains(' ')));
                        if !is_special && has_space_literal {
                            err(out, word.id(), 2066,
                                "Since you double quoted this, it will not word split, and the loop will only run once.");
                        }
                    }
                }
            }
        }
    }
}

/// Analytics entry: analyze a parsed script and return diagnostics.
/// (The full Haskell `analyzeScript` also runs Commands/ControlFlow/ShellSupport
/// checkers; those are merged in as they are ported.)
pub fn analyze(params: &Parameters) -> Out {
    let c = checker();
    run_checker(params, &c)
}

#[allow(dead_code)]
fn shell_is_sh(shell: Shell) -> bool {
    matches!(shell, Shell::Sh | Shell::Dash | Shell::BusyboxSh)
}
