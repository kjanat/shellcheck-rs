//! Shared test harness for the `prop_` tests, mirroring the Haskell `verify` /
//! `verifyNot` / `verifyTree` helpers: parse a script, run one check over it
//! and report what it emitted, after the same annotation filtering the real
//! checker applies.
#![cfg(test)]

use crate::analyzer_lib::{Out, Parameters, get_path, make_parameters};
use crate::ast::{Annotation, InnerToken, Token};
use crate::interface::{Code, Shell};
use crate::parser::parse_script;

type Check = fn(&Parameters, &Token, &mut Out);

pub(crate) fn params_for(script: &str) -> Parameters {
    let p = parse_script("test", script);
    let root = p.root.expect("parse produced no root");
    make_parameters(root, p.positions, None, None)
}

pub(crate) fn params_for_shell(script: &str, shell: Shell) -> Parameters {
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

fn run_node(params: &Parameters, f: Check) -> Out {
    let mut out = Out::new();
    params.root.visit_preorder(&mut |t| f(params, t, &mut out));
    out.retain(|c| !is_ignored(params, c.comment.code, c.id));
    out
}

/// Every comment a node check emits over the script.
pub(crate) fn collect(f: Check, s: &str) -> Out {
    run_node(&params_for(s), f)
}

/// `verify`: does the node check emit anything?
pub(crate) fn produces(f: Check, s: &str) -> bool {
    !collect(f, s).is_empty()
}
pub(crate) fn emits(f: Check, s: &str) -> bool {
    produces(f, s)
}
pub(crate) fn node_emits(f: Check, s: &str) -> bool {
    produces(f, s)
}

/// `verifyTree`: run a tree check on the root only.
pub(crate) fn tree_emits(f: Check, s: &str) -> bool {
    let params = params_for(s);
    let mut out = Out::new();
    f(&params, &params.root, &mut out);
    out.retain(|c| !is_ignored(&params, c.comment.code, c.id));
    !out.is_empty()
}

pub(crate) fn emits_code(f: Check, s: &str, code: i64) -> bool {
    collect(f, s).iter().any(|c| c.comment.code == code)
}

/// The distinct codes a node check emits, sorted.
pub(crate) fn codes(f: Check, s: &str) -> Vec<i64> {
    let mut v: Vec<i64> = collect(f, s).iter().map(|c| c.comment.code).collect();
    v.sort();
    v.dedup();
    v
}

pub(crate) fn emits_shell(f: Check, s: &str, shell: Shell) -> bool {
    !run_node(&params_for_shell(s, shell), f).is_empty()
}

pub(crate) fn emits_code_shell(f: Check, s: &str, code: i64, shell: Shell) -> bool {
    run_node(&params_for_shell(s, shell), f)
        .iter()
        .any(|c| c.comment.code == code)
}
