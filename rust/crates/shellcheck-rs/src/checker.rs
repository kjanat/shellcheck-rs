//! Port of `ShellCheck.Checker`: the parse -> analyze -> resolve -> filter ->
//! sort pipeline that turns a `CheckSpec` into a `CheckResult`.

use crate::analytics;
use crate::analyzer_lib;
use crate::ast::Id;
use crate::interface::{
    CheckResult, CheckSpec, Comment, Position, PositionedComment, Severity, Shell, TokenComment,
};
use crate::parser::{self, ParseNote};

/// `checkScript`.
pub fn check_script(spec: &CheckSpec) -> CheckResult {
    let parse = parser::parse_script(&spec.filename, &spec.script);

    // Parse comments (SC1xxx): already positioned.
    let mut positioned: Vec<PositionedComment> =
        parse.notes.iter().map(note_to_positioned).collect();

    // Analysis comments (SC2xxx/SC3xxx): resolved from ids via the position map.
    if let Some(root) = parse.root.clone() {
        let params = analyzer_lib::make_parameters_ext(
            root,
            parse.positions.clone(),
            spec.shell_type_override,
            shell_from_filename(&spec.filename),
            spec.extended_analysis,
        );
        let analysis = analytics::analyze(&params);
        for tc in analysis {
            if annotation_ignores(&params, tc.id, tc.comment.code) {
                continue;
            }
            positioned.push(token_to_position(&tc, &parse.positions));
        }
    }

    // Filter by severity / include / exclude.
    positioned.retain(|pc| should_include(pc, spec));

    // nub: remove exact duplicates, preserving first occurrence.
    positioned = nub(positioned);

    // sort by (file, line, column, severity, code, message).
    positioned.sort_by_key(order_key);

    CheckResult {
        filename: spec.filename.clone(),
        comments: positioned,
    }
}

/// Port of `filterByAnnotation` / `isAnnotationIgnoringCode`: a comment is
/// ignored if any ancestor `T_Annotation` disables its code.
fn annotation_ignores(params: &analyzer_lib::Parameters, id: Id, code: i64) -> bool {
    use crate::ast::{Annotation, InnerToken};
    let mut cur = id;
    // Walk from the comment's token up to the root via the parent map, checking
    // each ancestor token (getPath semantics).
    while let Some(&pid) = params.parent_map.get(&cur) {
        if let Some(tok) = params.id_map.get(&pid) {
            if let InnerToken::T_Annotation { annotations, .. } = &*tok.inner {
                for a in annotations {
                    if let Annotation::DisableComment(from, to) = a {
                        if code >= *from && code < *to {
                            return true;
                        }
                    }
                }
            }
        }
        cur = pid;
    }
    false
}

fn note_to_positioned(n: &ParseNote) -> PositionedComment {
    PositionedComment {
        start: n.start.clone(),
        end: n.end.clone(),
        comment: Comment {
            severity: n.severity,
            code: n.code,
            message: n.message.clone(),
        },
        fix: None,
    }
}

fn token_to_position(
    tc: &TokenComment,
    positions: &std::collections::BTreeMap<Id, (Position, Position)>,
) -> PositionedComment {
    let (start, end) = positions.get(&tc.id).cloned().unwrap_or_default();
    PositionedComment {
        start,
        end,
        comment: tc.comment.clone(),
        fix: tc.fix.clone(),
    }
}

fn should_include(pc: &PositionedComment, spec: &CheckSpec) -> bool {
    let code = pc.comment.code;
    let severity = pc.comment.severity;
    if severity > spec.min_severity {
        return false;
    }
    match &spec.included_warnings {
        None => !spec.excluded_warnings.contains(&code),
        Some(included) => included.contains(&code),
    }
}

fn nub(v: Vec<PositionedComment>) -> Vec<PositionedComment> {
    let mut out: Vec<PositionedComment> = Vec::with_capacity(v.len());
    for pc in v {
        if !out.iter().any(|x| x == &pc) {
            out.push(pc);
        }
    }
    out
}

type OrderKey = (String, i64, i64, Severity, i64, String);

fn order_key(pc: &PositionedComment) -> OrderKey {
    (
        pc.start.file.clone(),
        pc.start.line,
        pc.start.column,
        pc.comment.severity,
        pc.comment.code,
        pc.comment.message.clone(),
    )
}

/// `shellFromFilename`: infer a fallback shell from the file extension.
fn shell_from_filename(filename: &str) -> Option<Shell> {
    let candidates = [
        (".ksh", Shell::Ksh),
        (".bash", Shell::Bash),
        (".bats", Shell::Bash),
        (".dash", Shell::Dash),
        (".envrc", Shell::Bash),
    ];
    for (ext, sh) in candidates {
        if filename.ends_with(ext) {
            return Some(sh);
        }
    }
    None
}
