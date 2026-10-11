//! Diagnostics beyond the upstream rule set (SC9001–SC9002).
use crate::analyzer_lib::{Out, Parameters, get_command_name, warn};
use crate::ast::{InnerToken, Token};
use crate::ast_lib::{get_literal_string, get_literal_string_ext};

/// Exactly one insertion, deletion, substitution, or adjacent transposition.
/// Directory separators must stay intact: compare components, not path bytes.
fn one_typo(a: &str, b: &str) -> bool {
    let a: Vec<_> = a.chars().collect();
    let b: Vec<_> = b.chars().collect();
    if a == b || a.len().abs_diff(b.len()) > 1 {
        return false;
    }
    let first = a
        .iter()
        .zip(&b)
        .position(|(a, b)| a != b)
        .unwrap_or_else(|| a.len().min(b.len()));
    match a.len().cmp(&b.len()) {
        std::cmp::Ordering::Less => a[first..] == b[first + 1..],
        std::cmp::Ordering::Greater => a[first + 1..] == b[first..],
        std::cmp::Ordering::Equal => {
            a[first + 1..] == b[first + 1..]
                || (first + 1 < a.len()
                    && a[first] == b[first + 1]
                    && a[first + 1] == b[first]
                    && a[first + 2..] == b[first + 2..])
        }
    }
}

fn interpreter_suggestion(path: &str) -> Option<String> {
    const DIRECTORIES: &[&str] = &[
        "/bin",
        "/sbin",
        "/usr/bin",
        "/usr/sbin",
        "/usr/local/bin",
        "/usr/local/sbin",
    ];
    const INTERPRETERS: &[&str] = &["env", "sh", "bash", "dash", "ksh", "zsh", "ash", "busybox"];
    if !path.starts_with('/') {
        return None;
    }
    let (directory, interpreter) = path.rsplit_once('/')?;
    // A custom interpreter or an exact standard directory gives no evidence
    // of a directory typo. Never probe the checking machine's filesystem.
    if !INTERPRETERS.contains(&interpreter) || DIRECTORIES.contains(&directory) {
        return None;
    }
    let components: Vec<_> = directory.split('/').collect();
    let mut candidates = DIRECTORIES.iter().filter(|candidate| {
        let expected: Vec<_> = candidate.split('/').collect();
        if components.len() != expected.len() {
            return false;
        }
        let differences: Vec<_> = components
            .iter()
            .zip(expected)
            .filter(|(a, b)| **a != *b)
            .collect();
        differences.len() == 1 && one_typo(differences[0].0, differences[0].1)
    });
    let candidate = candidates.next()?;
    // Do not choose arbitrarily when more than one standard location is near.
    if candidates.next().is_some() {
        return None;
    }
    Some(format!("{candidate}/{interpreter}"))
}

pub(super) fn check_interpreter_path(_params: &Parameters, root: &Token, out: &mut Out) {
    root.visit_preorder(&mut |token| {
        let InnerToken::T_Script { shebang, .. } = &*token.inner else { return };
        let Some(text) = get_literal_string(shebang) else { return };
        let Some(path) = text.split_whitespace().next() else { return };
        if let Some(suggestion) = interpreter_suggestion(path) {
            warn(out, shebang.id(), 9001, &format!(
                "Possible interpreter-path typo: did you mean {suggestion}? Keep this path if it is intentional."
            ));
        }
    });
}

// Retain simple parameter identities when a double-quoted action expands at
// trap registration. Unknown substitutions remain unknown, never executable.
fn trap_action(token: &Token) -> Option<String> {
    get_literal_string_ext(token, &|part| {
        let InnerToken::T_DollarBraced { op, .. } = part else {
            return None;
        };
        let name = get_literal_string(op)?;
        crate::cfg::is_variable_name(&name).then(|| format!("${{{name}}}"))
    })
}

fn trap(token: &Token) -> Option<(String, Vec<String>)> {
    let InnerToken::T_SimpleCommand { words, .. } = &*token.inner else {
        return None;
    };
    if get_command_name(token).as_deref() != Some("trap") {
        return None;
    }
    let mut args = words.iter().skip(1);
    let mut action = trap_action(args.next()?)?;
    if action == "--" {
        action = trap_action(args.next()?)?;
    }
    if action.is_empty() || action == "-" {
        return None;
    }
    let signals: Option<Vec<_>> = args.map(get_literal_string).collect();
    Some((action, signals?))
}

fn cleans_up(action: &str) -> bool {
    let parsed =
        crate::parser::parse_script_with("-", action, true, Some(crate::interface::Shell::Bash));
    let Some(root) = parsed.root else {
        return false;
    };
    let mut cleanup = false;
    root.visit_preorder(&mut |t| {
        let InnerToken::T_SimpleCommand { words, .. } = &*t.inner else {
            return;
        };
        let name = get_command_name(t);
        cleanup |= matches!(name.as_deref(), Some("rm" | "rmdir" | "kill" | "cleanup"));
        let engine = matches!(name.as_deref(), Some("docker" | "podman"))
            || (name.is_none()
                && words.first().is_some_and(|word| {
                    let mut variable = false;
                    word.visit_preorder(&mut |part| {
                        variable |= matches!(&*part.inner, InnerToken::T_DollarBraced { .. });
                    });
                    variable
                }));
        cleanup |= engine
            && words
                .get(1)
                .and_then(get_literal_string)
                .is_some_and(|verb| matches!(verb.as_str(), "stop" | "rm" | "kill"));
    });
    cleanup
}

pub(super) fn check_cleanup_traps(_params: &Parameters, root: &Token, out: &mut Out) {
    fn scope(root: &Token, out: &mut Out) {
        fn collect<'a>(
            token: &'a Token,
            traps: &mut Vec<(&'a Token, String, Vec<String>)>,
            out: &mut Out,
        ) {
            // A trap in a function/subshell/substitution cannot establish an
            // EXIT handler in the enclosing execution scope.
            if matches!(
                &*token.inner,
                InnerToken::T_Function { .. }
                    | InnerToken::T_Subshell(_)
                    | InnerToken::T_DollarExpansion(_)
                    | InnerToken::T_Backticked(_)
            ) {
                scope(token, out);
                return;
            }
            if let Some((action, signals)) = trap(token) {
                traps.push((token, action, signals));
            }
            for child in token.children() {
                collect(child, traps, out);
            }
        }
        let mut traps = Vec::new();
        for child in root.children() {
            collect(child, &mut traps, out);
        }
        for (token, action, signals) in &traps {
            let exit = |s: &String| matches!(s.as_str(), "EXIT" | "0");
            if signals.iter().any(exit)
                || !signals.iter().any(|s| {
                    matches!(
                        s.as_str(),
                        "INT" | "SIGINT" | "2" | "TERM" | "SIGTERM" | "15" | "HUP" | "SIGHUP" | "1"
                    )
                })
            {
                continue;
            }
            if traps
                .iter()
                .any(|(_, other, sigs)| other == action && sigs.iter().any(exit))
            {
                continue;
            }
            if cleans_up(action) {
                warn(
                    out,
                    token.id(),
                    9002,
                    "This cleanup trap only handles signals. Consider EXIT to also clean up after errors, end of input, and normal exit.",
                );
            }
        }
    }
    scope(root, out);
}

#[cfg(test)]
mod tests {
    use crate::{check_script, interface::CheckSpec};
    fn codes(script: &str, enable: &[&str]) -> Vec<i64> {
        check_script(&CheckSpec {
            filename: "test.bash".into(),
            script: script.into(),
            optional_checks: enable.iter().map(|s| (*s).into()).collect(),
            ..CheckSpec::default()
        })
        .comments
        .into_iter()
        .map(|c| c.comment.code)
        .collect()
    }
    #[test]
    fn directory_typos_use_spelling_distance() {
        for (bad, expected) in [
            ("/use/bin/bash", "/usr/bin/bash"),
            ("/usr/bni/env", "/usr/bin/env"),
            ("/usrr/bin/sh", "/usr/bin/sh"),
            ("/ur/bin/dash", "/usr/bin/dash"),
            ("/usr/locla/bin/bash", "/usr/local/bin/bash"),
            ("/usr/local/bim/ksh", "/usr/local/bin/ksh"),
        ] {
            assert_eq!(
                super::interpreter_suggestion(bad).as_deref(),
                Some(expected),
                "{bad}"
            );
        }
        for valid in [
            "/opt/company/bin/bash",
            "/nix/store/abc/bin/bash",
            "/usr/bin/bash",
            "/usr/local/bin/bash",
            "/usr/custom/bash",
            "x/bin/bash",
            "usr/bin/bash",
            "/use/bin/company-shell",
        ] {
            assert_eq!(super::interpreter_suggestion(valid), None, "{valid}");
        }
        assert!(super::one_typo("bni", "bin"));
        assert!(!super::one_typo("bin", "bin"));
        assert!(!super::one_typo("company", "bin"));
    }

    #[test]
    fn interpreter_typo_is_default_and_preserves_custom_paths() {
        assert!(!codes("\n#!'/bin/sh", &[]).contains(&9001));
        let bad = "#!/use/bin/env bash\necho ok";
        assert!(codes(bad, &[]).contains(&9001));
        assert!(
            !codes(
                "#!/use/bin/env bash\n# shellcheck disable=9001\necho ok",
                &[]
            )
            .contains(&9001)
        );
        for path in [
            "/usr/bin/env bash",
            "/opt/custom/bash",
            "/use/bin/custom-shell",
            "/nix/store/custom/bin/bash",
        ] {
            assert!(!codes(&format!("#!{path}\necho ok"), &[]).contains(&9001));
        }
    }
    #[test]
    fn issue_4_expanded_container_cleanup_is_detected_by_default() {
        // kjanat/zed-editor@65953ede7e, script/mitm-proxy.sh:19.
        let script = r#"#!/usr/bin/env bash
set -euo pipefail
ENGINE=docker
CONTAINER_ID=container
trap "${ENGINE} stop \"$CONTAINER_ID\" 1> /dev/null || true; exit 1" SIGINT
read
http_proxy=http://localhost:9876 cargo run
${ENGINE} stop "${CONTAINER_ID}" 2>/dev/null || true
"#;
        assert!(codes(script, &[]).contains(&9002));
        let covered = script.replace("SIGINT", "EXIT SIGINT");
        assert!(!codes(&covered, &[]).contains(&9002));
    }

    #[test]
    fn signal_cleanup_needs_exit_coverage_in_the_same_scope() {
        for script in [
            "trap 'docker stop \"$id\"' INT",
            "trap '\"$ENGINE\" stop \"$CONTAINER_ID\"' SIGINT",
            r#"ENGINE=docker; CONTAINER_ID=abc; trap "$ENGINE stop $CONTAINER_ID" SIGINT"#,
            "trap -- 'rm -f \"$tmp\"' 2 15",
            "trap 'cleanup' TERM; f() { trap 'cleanup' EXIT; }",
            "trap 'cleanup' INT; (trap 'cleanup' EXIT)",
            "f() { trap 'cleanup' INT; }; trap 'cleanup' EXIT",
            "trap 'cleanup' INT; trap 'echo done' EXIT",
        ] {
            assert!(codes(script, &[]).contains(&9002), "{script}");
        }
        for script in [
            "trap 'docker stop \"$id\"' EXIT INT",
            "trap 'cleanup' 0 2",
            "trap 'cleanup' INT; trap 'cleanup' EXIT",
            "trap 'echo interrupted' INT",
            "trap '' INT",
            "trap - INT",
        ] {
            assert!(!codes(script, &[]).contains(&9002), "{script}");
        }
        assert!(codes("trap 'cleanup' INT", &[]).contains(&9002));
        assert!(!codes("# shellcheck disable=9002\ntrap 'cleanup' INT", &[]).contains(&9002));
    }
}
