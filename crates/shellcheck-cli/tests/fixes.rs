//! `prop_checkRequireDoubleBracket5` and `6` from upstream `Analytics.hs`.
//! They apply fixes with `formatter::fixer`, which only this crate has.
#![allow(non_snake_case)]

use rshellcheck::formatter::fixer::{apply_fix, fix_mconcat, lines};
use rshellcheck_core::interface::CheckSpec;

fn verify_tree_fix(optional: &str, script: &str, expected: &str) -> bool {
    let result = rshellcheck_core::check_script(&CheckSpec {
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
