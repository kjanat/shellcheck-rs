//! Shared test harness for the `prop_` tests, mirroring the Haskell `verify` /
//! `verifyNot` / `verifyTree` helpers: parse a script, run one check over it
//! and report what it emitted, after the same annotation filtering the real
//! checker applies.
#![cfg(test)]

use crate::analyzer_lib::{Check, Out, Parameters, get_path, make_parameters};
use crate::ast::{Annotation, InnerToken, Token};
use crate::interface::{Code, Shell};
use crate::parser::parse_script;

/// The message of the first `code` that the whole pipeline reports on `script`.
pub fn message_of(script: &str, code: Code) -> String {
    crate::check_script(&crate::interface::CheckSpec {
        script: script.to_string(),
        ..crate::interface::CheckSpec::default()
    })
    .comments
    .into_iter()
    .find(|c| c.comment.code == code)
    .map_or_else(
        || panic!("SC{code} does not fire on {script:?}"),
        |c| c.comment.message,
    )
}

pub fn params_for(script: &str) -> Parameters {
    let p = parse_script("test", script);
    let root = p.root.expect("parse produced no root");
    make_parameters(root, p.positions, None, None)
}

pub fn params_for_shell(script: &str, shell: Shell) -> Parameters {
    let p = parse_script("test", script);
    let root = p.root.expect("parse produced no root");
    make_parameters(root, p.positions, Some(shell), None)
}

/// `filterByAnnotation`: drop comments a `# shellcheck disable=` covers.
fn is_ignored(params: &Parameters, code: Code, id: crate::ast::Id) -> bool {
    let Some(token) = params.id_map.get(&id).cloned() else {
        return false;
    };
    get_path(params, &token).iter().any(|p| {
        if let InnerToken::T_Annotation { annotations, .. } = &*p.inner {
            annotations.iter().any(|a| match a {
                Annotation::DisableComment(from, to) => code >= *from && code < *to,
                _ => false,
            })
        } else {
            false
        }
    })
}

/// `runAndGetComments`: run a tree check on the root, then `filterByAnnotation`.
fn run_and_get_comments(params: &Parameters, f: impl FnOnce(&Parameters, &Token) -> Out) -> Out {
    // Exercise the optimized dispatcher and its exhaustive reference on every
    // check fixture, including all optional checks, before testing one rule.
    let _ = crate::analytics::analyze_with(params, &["all".to_string()]);
    let mut out = f(params, &params.root);
    out.retain(|c| !is_ignored(params, c.comment.code, c.id));
    out
}

/// `checkNode`: `producesComments (runNodeAnalysis f)`.
fn run_node(params: &Parameters, f: impl Check) -> Out {
    run_and_get_comments(params, move |params, root| {
        let mut out = Out::new();
        root.visit_preorder(&mut |t| f.run(params, t, &mut out));
        out
    })
}

/// Every comment a node check emits over the script.
pub fn collect(f: impl Check, s: &str) -> Out {
    run_node(&params_for(s), f)
}

/// `verify`: does the node check emit anything?
pub fn produces(f: impl Check, s: &str) -> bool {
    !collect(f, s).is_empty()
}
pub fn emits(f: impl Check, s: &str) -> bool {
    produces(f, s)
}
pub fn node_emits(f: impl Check, s: &str) -> bool {
    produces(f, s)
}

/// `verifyTree`: run a tree check on the root only.
pub fn tree_emits(f: impl Check, s: &str) -> bool {
    !run_and_get_comments(&params_for(s), move |params, root| {
        let mut out = Out::new();
        f.run(params, root, &mut out);
        out
    })
    .is_empty()
}

pub fn emits_code(f: impl Check, s: &str, code: i64) -> bool {
    collect(f, s).iter().any(|c| c.comment.code == code)
}

/// The distinct codes a node check emits, sorted.
pub fn codes(f: impl Check, s: &str) -> Vec<i64> {
    let mut v: Vec<i64> = collect(f, s).iter().map(|c| c.comment.code).collect();
    v.sort_unstable();
    v.dedup();
    v
}

pub fn emits_shell(f: impl Check, s: &str, shell: Shell) -> bool {
    !run_node(&params_for_shell(s, shell), f).is_empty()
}

pub fn emits_code_shell(f: impl Check, s: &str, code: i64, shell: Shell) -> bool {
    run_node(&params_for_shell(s, shell), f)
        .iter()
        .any(|c| c.comment.code == code)
}
