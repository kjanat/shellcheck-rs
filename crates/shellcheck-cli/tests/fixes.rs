//! `verifyTreeFix`: applying every suggested fix to a script gives the
//! expected result. Upstream keeps these properties next to the checks; the
//! port's fixer lives in this crate, so they run here.
#![allow(non_snake_case)]

use shellcheck_cli::formatter::fixer::{apply_fix, fix_mconcat, lines};
use shellcheck_rs::interface::CheckSpec;

fn verify_tree_fix(optional: &str, script: &str, expected: &str) -> bool {
    let result = shellcheck_rs::check_script(&CheckSpec {
        filename: "test".to_string(),
        script: script.to_string(),
        optional_checks: vec![optional.to_string()],
        ..CheckSpec::default()
    });
    let fixes: Vec<_> = result
        .comments
        .iter()
        .filter_map(|c| c.fix.clone())
        .collect();
    apply_fix(&fix_mconcat(&fixes), &lines(script)) == lines(expected)
}

#[test]
fn prop_checkRequireDoubleBracket5() {
    assert!(verify_tree_fix(
        "require-double-brackets",
        "[ -x foo ]",
        "[[ -x foo ]]"
    ));
}

#[test]
fn prop_checkRequireDoubleBracket6() {
    assert!(verify_tree_fix(
        "require-double-brackets",
        "[ -x foo ]]",
        "[[ -x foo ]]"
    ));
}
