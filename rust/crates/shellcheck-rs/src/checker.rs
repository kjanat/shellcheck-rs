//! Port of `ShellCheck.Checker`: the parse -> analyze -> resolve -> filter ->
//! sort pipeline that turns a `CheckSpec` into a `CheckResult`.

use crate::analytics;
use crate::analyzer_lib;
use crate::ast::Id;
use crate::interface::{
    CheckResult, CheckSpec, Comment, NoExternalSources, Position, PositionedComment,
    RcParseProblem, Severity, Shell, SystemInterface, TokenComment,
};
use crate::parser::{self, ParseNote};
use std::rc::Rc;

/// `checkScript` with the default interface: no sourced file is ever read, and
/// the refusal is worded as the CLI words it without `-x`.
pub fn check_script(spec: &CheckSpec) -> CheckResult {
    check_script_with(Rc::new(NoExternalSources), spec)
}

/// `checkScript`, with the interface a sourced file is read through.
///
/// Upstream every caller passes a `SystemInterface`; here [`check_script`]
/// supplies a default so that an embedder that never sources anything does not
/// have to.
pub fn check_script_with(sys: Rc<dyn SystemInterface>, spec: &CheckSpec) -> CheckResult {
    let parse = parser::parse_script_spec(&parser::ParseSpec {
        filename: spec.filename.clone(),
        script: spec.script.clone(),
        check_sourced: spec.check_sourced,
        shell_flag_specified: spec.shell_type_override.is_some(),
        shell_hint: spec
            .shell_type_override
            .or_else(|| shell_from_filename(&spec.filename)),
        sys,
    });

    // Parse comments (SC1xxx): already positioned.
    let mut positioned: Vec<PositionedComment> =
        parse.notes.iter().map(note_to_positioned).collect();

    // An unparsable rc file is a parse *problem* on this script
    // (`readConfigFile` -> `parseProblem ErrorC 1134`), emitted at the start of
    // the file whether or not the script itself parses.
    if let Some(problem) = spec.rc.as_ref().and_then(|rc| rc.parse_problem.as_ref()) {
        positioned.push(rc_problem_comment(&spec.filename, problem));
    }

    // Analysis comments (SC2xxx/SC3xxx): resolved from ids via the position map.
    if let Some(root) = parse.root.clone() {
        // `asOptionalChecks = getEnableDirectives root ++ csOptionalChecks spec`
        let mut optional = analyzer_lib::get_enable_directives(&root);
        optional.extend(spec.optional_checks.iter().cloned());
        let params = analyzer_lib::make_parameters_ext(
            root,
            parse.positions.clone(),
            spec.shell_type_override,
            shell_from_filename(&spec.filename),
            spec.extended_analysis,
        );
        let analysis = analytics::analyze_with(&params, &optional);
        for tc in analysis {
            if annotation_ignores(&params, tc.id, tc.comment.code, spec.check_sourced) {
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
/// ignored if any ancestor `T_Annotation` disables its code -- or if it comes
/// from inside a sourced file (`T_Include`) and `--check-sourced` was not given
/// (`shouldIgnoreFor _ T_Include {} = not $ asCheckSourced asSpec`).
fn annotation_ignores(
    params: &analyzer_lib::Parameters,
    id: Id,
    code: i64,
    check_sourced: bool,
) -> bool {
    use crate::ast::{Annotation, InnerToken};
    let mut cur = id;
    // Walk from the comment's token up to the root via the parent map, checking
    // each ancestor token (getPath semantics).
    while let Some(&pid) = params.parent_map.get(&cur) {
        if let Some(tok) = params.id_map.get(&pid) {
            if !check_sourced && matches!(&*tok.inner, InnerToken::T_Include(_)) {
                return true;
            }
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

/// `readConfigFile`'s failure branch: `parseProblem ErrorC 1134 $ errorFor ..`,
/// reported at the start of the script that pulled in the rc file.
fn rc_problem_comment(script: &str, problem: &RcParseProblem) -> PositionedComment {
    let pos = Position {
        file: script.to_string(),
        line: 1,
        column: 1,
    };
    PositionedComment {
        start: pos.clone(),
        end: pos,
        comment: Comment {
            severity: Severity::ErrorC,
            code: 1134,
            message: format!(
                "Failed to process {}, line {}: {} Fix any mentioned problems and try again.",
                crate::ast_lib::e4m(&problem.filename),
                problem.line,
                problem.suggestion
            ),
        },
        fix: None,
    }
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
    // rc `disable=` ranges are annotations upstream, so they suppress a code
    // independently of the include/exclude lists. Membership is tested against
    // the endpoints (`code >= n && code < m`), never enumerated.
    if let Some(rc) = &spec.rc {
        if rc.disabled_ranges.iter().any(|r| r.contains(code)) {
            return false;
        }
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

#[cfg(test)]
#[allow(non_snake_case)]
mod source_tests {
    //! The source-following properties of `ShellCheck.Checker`, which upstream
    //! runs against `mockedSystemInterface`.
    use super::*;
    use crate::interface::{ErrorMessage, MockSystemInterface};
    use std::cell::RefCell;

    /// `getErrors`: the codes, sorted.
    fn errors(sys: Rc<dyn SystemInterface>, spec: &CheckSpec) -> Vec<i64> {
        let mut codes: Vec<i64> = check_script_with(sys, spec)
            .comments
            .iter()
            .map(|c| c.comment.code)
            .collect();
        codes.sort_unstable();
        codes
    }

    /// `checkWithIncludes`: SC2148 excluded, sources read from the mock.
    fn check_with_includes(includes: &[(&str, &str)], script: &str) -> Vec<i64> {
        errors(
            Rc::new(MockSystemInterface::new(includes)),
            &CheckSpec {
                script: script.to_string(),
                excluded_warnings: vec![2148],
                ..CheckSpec::default()
            },
        )
    }

    /// `checkRecursive`: as above with `csCheckSourced`.
    fn check_recursive(includes: &[(&str, &str)], script: &str) -> Vec<i64> {
        errors(
            Rc::new(MockSystemInterface::new(includes)),
            &CheckSpec {
                script: script.to_string(),
                excluded_warnings: vec![2148],
                check_sourced: true,
                ..CheckSpec::default()
            },
        )
    }

    /// `check`: no includes at all, so every source fails to resolve.
    fn check(script: &str) -> Vec<i64> {
        check_with_includes(&[], script)
    }

    /// A mock whose `siFindSource` is a caller-supplied function, recording what
    /// it was asked -- `checkWithIncludesAndSourcePath`, whose mapper is a
    /// pattern match that fails the test when the arguments are unexpected.
    /// What one `siFindSource` call was given: script, external-sources hint,
    /// source paths, name.
    type FindArgs = (String, Option<bool>, Vec<String>, String);

    /// The mapper `checkWithIncludesAndSourcePath` is given.
    type Finder = dyn Fn(&str, Option<bool>, &[String], &str) -> String;

    struct FindSourceMock {
        files: MockSystemInterface,
        find: Box<Finder>,
        asked: RefCell<Vec<FindArgs>>,
    }

    impl SystemInterface for FindSourceMock {
        fn read_file(
            &self,
            external_sources: Option<bool>,
            file: &str,
        ) -> Result<String, ErrorMessage> {
            self.files.read_file(external_sources, file)
        }

        fn find_source(
            &self,
            current_script: &str,
            external_sources: Option<bool>,
            source_paths: &[String],
            name: &str,
        ) -> String {
            self.asked.borrow_mut().push((
                current_script.to_string(),
                external_sources,
                source_paths.to_vec(),
                name.to_string(),
            ));
            (self.find)(current_script, external_sources, source_paths, name)
        }
    }

    #[test]
    fn prop_canParseDevNull() {
        assert!(check("source /dev/null").is_empty());
    }

    #[test]
    fn prop_failsWhenNotSourcing() {
        assert_eq!(check("source lol; echo \"$bar\""), vec![1091, 2154]);
    }

    #[test]
    fn prop_worksWhenSourcing() {
        assert!(check_with_includes(&[("lib", "bar=1")], "source lib; echo \"$bar\"").is_empty());
    }

    #[test]
    fn prop_worksWhenSourcingWithDashDash() {
        assert!(
            check_with_includes(&[("lib", "bar=1")], "source -- lib; echo \"$bar\"").is_empty()
        );
    }

    #[test]
    fn prop_worksWhenSourcingWithDashP() {
        assert!(
            check_with_includes(
                &[("lib", "bar=1")],
                "source -p \"$MYPATH\" lib; echo \"$bar\""
            )
            .is_empty()
        );
    }

    #[test]
    fn prop_worksWhenDotting() {
        assert!(check_with_includes(&[("lib", "bar=1")], ". lib; echo \"$bar\"").is_empty());
    }

    #[test]
    fn prop_noInfiniteSourcing() {
        // The recursion guard stops at the second frame, and SC1093 is squashed
        // without --check-sourced (upstream's FIXME).
        assert!(check_with_includes(&[("lib", "source lib")], "source lib").is_empty());
        assert_eq!(
            check_recursive(&[("lib", "source lib")], "source lib"),
            vec![1093]
        );
    }

    #[test]
    fn prop_canSourceBadSyntax() {
        assert_eq!(
            check_with_includes(&[("lib", "for f; do")], "source lib; echo $1"),
            vec![1094, 2086]
        );
    }

    #[test]
    fn prop_cantSourceDynamic() {
        assert_eq!(check_with_includes(&[("lib", "")], ". \"$1\""), vec![1090]);
    }

    #[test]
    fn prop_cantSourceDynamic2() {
        assert_eq!(
            check_with_includes(&[("lib", "")], "source ~/foo"),
            vec![1090]
        );
    }

    #[test]
    fn prop_canStripPrefixAndSource() {
        assert!(check_with_includes(&[("./lib", "")], "source \"$MYDIR/lib\"").is_empty());
    }

    #[test]
    fn prop_canStripPrefixAndSource2() {
        assert!(
            check_with_includes(
                &[("./utils.sh", "")],
                "source \"$(dirname \"${BASH_SOURCE[0]}\")/utils.sh\""
            )
            .is_empty()
        );
    }

    #[test]
    fn prop_canSourceDynamicWhenRedirected() {
        assert!(check_with_includes(&[("lib", "")], "#shellcheck source=lib\n. \"$1\"").is_empty());
    }

    #[test]
    fn prop_canRedirectWithSpaces() {
        assert!(
            check_with_includes(
                &[("my file", "")],
                "#shellcheck source=\"my file\"\n. \"$1\""
            )
            .is_empty()
        );
    }

    #[test]
    fn prop_recursiveAnalysis() {
        assert_eq!(
            check_recursive(&[("lib", "echo $1")], "source lib"),
            vec![2086]
        );
    }

    #[test]
    fn prop_recursiveParsing() {
        assert_eq!(
            check_recursive(&[("lib", "echo \"$10\"")], "source lib"),
            vec![1037]
        );
    }

    #[test]
    fn prop_nonRecursiveAnalysis() {
        assert!(check_with_includes(&[("lib", "echo $1")], "source lib").is_empty());
    }

    #[test]
    fn prop_nonRecursiveParsing() {
        assert!(check_with_includes(&[("lib", "echo \"$10\"")], "source lib").is_empty());
    }

    #[test]
    fn prop_sourceDirectiveDoesntFollowFile() {
        // The directive applies to the `.` it precedes, not to the `source bar`
        // inside the file it names, so `baz` is never defined.
        assert!(
            check_with_includes(
                &[("foo", "source bar"), ("bar", "baz=3")],
                "#shellcheck source=foo\n. \"$1\"; echo \"$baz\""
            )
            .is_empty()
        );
    }

    #[test]
    fn prop_sourcePartOfOriginalScript() {
        // #1181: following a source must not disable the posix warning on the
        // `source` keyword itself.
        assert!(
            check_with_includes(
                &[("./saywhat.sh", "echo foo")],
                "#!/bin/sh\nsource ./saywhat.sh"
            )
            .contains(&3046)
        );
    }

    #[test]
    fn prop_sourcedFileUsesOriginalShellExtension() {
        // The dialect comes from the script being checked, not from the name of
        // the file it sources.
        assert_eq!(
            errors(
                Rc::new(MockSystemInterface::new(&[("file.ksh", "(( 3.14 ))")])),
                &CheckSpec {
                    filename: "file.bash".to_string(),
                    script: "source file.ksh".to_string(),
                    check_sourced: true,
                    ..CheckSpec::default()
                }
            ),
            vec![2079]
        );
    }

    #[test]
    fn prop_sourceWithHereDocWorks() {
        // The sourced file is read between the `<<` and its body, and the
        // caller's pending here document survives that.
        assert!(
            check_with_includes(&[("bar", "true\n")], "source bar << eof\nlol\neof").is_empty()
        );
    }

    #[test]
    fn prop_sourcePathRedirectsName() {
        let sys = Rc::new(FindSourceMock {
            files: MockSystemInterface::new(&[("foo/lib", "echo $1")]),
            find: Box::new(|_, _, _, name| {
                assert_eq!(name, "lib");
                "foo/lib".to_string()
            }),
            asked: RefCell::new(Vec::new()),
        });
        let codes = errors(
            Rc::clone(&sys) as Rc<dyn SystemInterface>,
            &CheckSpec {
                filename: "dir/myscript".to_string(),
                script: "#!/bin/bash\nsource lib".to_string(),
                check_sourced: true,
                ..CheckSpec::default()
            },
        );
        assert_eq!(codes, vec![2086]);
        // `f "dir/myscript" _ _ "lib"`: the script the check started from, not
        // the file the `source` was written in.
        assert_eq!(sys.asked.borrow()[0].0, "dir/myscript");
    }

    #[test]
    fn prop_sourcePathAddsAnnotation() {
        let sys = Rc::new(FindSourceMock {
            files: MockSystemInterface::new(&[("foo/lib", "echo $1")]),
            find: Box::new(|_, _, paths, _| {
                assert_eq!(paths, ["mypath".to_string()]);
                "foo/lib".to_string()
            }),
            asked: RefCell::new(Vec::new()),
        });
        assert_eq!(
            errors(
                sys,
                &CheckSpec {
                    filename: "dir/myscript".to_string(),
                    script: "#!/bin/bash\n# shellcheck source-path=mypath\nsource lib".to_string(),
                    check_sourced: true,
                    ..CheckSpec::default()
                }
            ),
            vec![2086]
        );
    }

    #[test]
    fn prop_sourcePathWorksWithSpaces() {
        let sys = Rc::new(FindSourceMock {
            files: MockSystemInterface::new(&[("foo/lib", "echo $1")]),
            find: Box::new(|_, _, paths, _| {
                assert_eq!(paths, ["my path".to_string()]);
                "foo/lib".to_string()
            }),
            asked: RefCell::new(Vec::new()),
        });
        assert_eq!(
            errors(
                sys,
                &CheckSpec {
                    filename: "dir/myscript".to_string(),
                    script: "#!/bin/bash\n# shellcheck source-path='my path'\nsource lib"
                        .to_string(),
                    check_sourced: true,
                    ..CheckSpec::default()
                }
            ),
            vec![2086]
        );
    }

    #[test]
    fn prop_sourcePathRedirectsDirective() {
        // The `source=` directive names what is looked up; the resolver still
        // gets a say in where it comes from.
        let sys = Rc::new(FindSourceMock {
            files: MockSystemInterface::new(&[("foo/lib", "echo $1")]),
            find: Box::new(|_, _, _, name| {
                if name == "lib" {
                    "foo/lib".to_string()
                } else {
                    "/dev/null".to_string()
                }
            }),
            asked: RefCell::new(Vec::new()),
        });
        assert_eq!(
            errors(
                sys,
                &CheckSpec {
                    filename: "dir/myscript".to_string(),
                    script: "#!/bin/bash\n# shellcheck source=lib\nsource kittens".to_string(),
                    check_sourced: true,
                    ..CheckSpec::default()
                }
            ),
            vec![2086]
        );
    }

    #[test]
    fn prop_fileCannotEnableExternalSources() {
        // `external-sources=true` in a script is refused (SC1144) and, with the
        // annotation dropped, the source is not followed either.
        let sys = Rc::new(FindSourceMock {
            files: MockSystemInterface::new(&[("foo", "true")]),
            find: Box::new(|_, external, _, name| {
                assert_eq!(
                    external, None,
                    "the refused annotation must not reach the resolver"
                );
                name.to_string()
            }),
            asked: RefCell::new(Vec::new()),
        });
        assert_eq!(
            errors(
                sys,
                &CheckSpec {
                    filename: "dir/myscript".to_string(),
                    script: "#!/bin/bash\n# shellcheck external-sources=true\nsource foo"
                        .to_string(),
                    check_sourced: true,
                    ..CheckSpec::default()
                }
            ),
            vec![1144]
        );
    }

    #[test]
    fn a_file_can_disable_external_sources() {
        // The other half of `external-sources`: `false` does reach the
        // interface, which is how the refusal is worded differently.
        let sys = Rc::new(FindSourceMock {
            files: MockSystemInterface::new(&[]),
            find: Box::new(|_, external, _, name| {
                assert_eq!(external, Some(false));
                name.to_string()
            }),
            asked: RefCell::new(Vec::new()),
        });
        let result = check_script_with(
            sys,
            &CheckSpec {
                filename: "dir/myscript".to_string(),
                script: "#!/bin/bash\n# shellcheck external-sources=false\nsource foo".to_string(),
                ..CheckSpec::default()
            },
        );
        let sc1091 = result
            .comments
            .iter()
            .find(|c| c.comment.code == 1091)
            .expect("SC1091");
        assert_eq!(
            sc1091.comment.message,
            "Not following: File not included in mock."
        );
    }

    #[test]
    fn the_default_interface_refuses_as_the_cli_does_without_x() {
        // What `check_script` (no interface) reports, and what the conformance
        // harness therefore compares against `shellcheck` with no `-x`.
        let result = check_script(&CheckSpec {
            filename: "s.sh".to_string(),
            script: "#!/bin/sh\n. ./lib.sh\n".to_string(),
            ..CheckSpec::default()
        });
        let sc1091 = result
            .comments
            .iter()
            .find(|c| c.comment.code == 1091)
            .expect("SC1091");
        assert_eq!(
            sc1091.comment.message,
            "Not following: ./lib.sh was not specified as input (see shellcheck -x)."
        );
    }

    #[test]
    fn a_followed_source_becomes_a_source_command_node() {
        // The AST shape the checks match on: `T_SourceCommand includer
        // (T_Include script)`, with the sourced file's positions under its own
        // resolved name.
        use crate::ast::InnerToken;
        let parse = crate::parser::parse_script_spec(&crate::parser::ParseSpec {
            filename: "main.sh".to_string(),
            script: "source lib\n".to_string(),
            check_sourced: true,
            sys: Rc::new(MockSystemInterface::new(&[("lib", "echo $x\n")])),
            ..crate::parser::ParseSpec::default()
        });
        let root = parse.root.expect("parses");
        let mut found = None;
        root.visit_preorder(&mut |t| {
            if let InnerToken::T_SourceCommand { includer, included } = &*t.inner {
                found = Some((includer.id(), included.clone()));
            }
        });
        let (includer_id, included) = found.expect("T_SourceCommand");
        // Both wrappers copy the span of the command they replace.
        assert_eq!(
            parse.positions[&includer_id],
            parse.positions[&included.id()]
        );
        let InnerToken::T_Include(script) = &*included.inner else {
            panic!("T_Include");
        };
        // The sourced script's own tokens are positioned in the sourced file.
        let mut files = Vec::new();
        script.visit_preorder(&mut |t| {
            if let Some((start, _)) = parse.positions.get(&t.id()) {
                files.push(start.file.clone());
            }
        });
        assert!(files.iter().all(|f| f == "lib"), "got {files:?}");
        assert!(!files.is_empty());
    }

    #[test]
    fn a_sourced_dev_null_is_still_a_source_command() {
        // DIVERGENCES.md E1: SC3051 matches `T_SourceCommand`, so it can only
        // fire once /dev/null is actually followed.
        let codes = errors(
            Rc::new(MockSystemInterface::new(&[])),
            &CheckSpec {
                script: "source /dev/null".to_string(),
                shell_type_override: Some(Shell::Sh),
                ..CheckSpec::default()
            },
        );
        assert_eq!(codes, vec![3046, 3051]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interface::{DisableRange, RcDirectives, RcParseProblem};

    fn spec(script: &str) -> CheckSpec {
        CheckSpec {
            filename: "s.sh".to_string(),
            script: script.to_string(),
            ..CheckSpec::default()
        }
    }

    fn codes(spec: &CheckSpec) -> Vec<i64> {
        check_script(spec)
            .comments
            .iter()
            .map(|c| c.comment.code)
            .collect()
    }

    fn with_ranges(script: &str, ranges: &[(i64, i64)]) -> CheckSpec {
        CheckSpec {
            rc: Some(Box::new(RcDirectives {
                disabled_ranges: ranges
                    .iter()
                    .map(|&(from, to)| DisableRange { from, to })
                    .collect(),
                parse_problem: None,
            })),
            ..spec(script)
        }
    }

    #[test]
    fn rc_disabled_range_filters_by_membership() {
        assert_eq!(codes(&spec("echo $x\n")), vec![2148, 2154, 2086]);
        // A single code is the range [n, n+1).
        assert_eq!(
            codes(&with_ranges("echo $x\n", &[(2086, 2087)])),
            vec![2148, 2154]
        );
        // A range covers its interior (2086, 2148) and excludes its upper
        // endpoint (2154), which the next code up includes.
        assert_eq!(
            codes(&with_ranges("echo $x\n", &[(2086, 2154)])),
            vec![2154]
        );
        assert!(codes(&with_ranges("echo $x\n", &[(2086, 2155)])).is_empty());
        // `disable=all` is one range, and an enormous range is still two
        // numbers rather than a billion of them.
        assert!(codes(&with_ranges("echo $x\n", &[(0, 1_000_000)])).is_empty());
        assert!(codes(&with_ranges("echo $x\n", &[(1000, 1_000_000_000)])).is_empty());
    }

    #[test]
    fn rc_disabled_range_outranks_the_include_list() {
        // rc disables are annotations upstream, so --include cannot revive one.
        let mut spec = with_ranges("echo $x\n", &[(2086, 2087)]);
        spec.included_warnings = Some(vec![2086, 2154]);
        assert_eq!(codes(&spec), vec![2154]);
    }

    #[test]
    fn unparsable_rc_becomes_sc1134() {
        let spec = CheckSpec {
            rc: Some(Box::new(RcDirectives {
                disabled_ranges: Vec::new(),
                parse_problem: Some(RcParseProblem {
                    filename: "/tmp/.shellcheckrc".to_string(),
                    line: 2,
                    suggestion: "Expected '=' after directive key.".to_string(),
                }),
            })),
            ..spec("echo $x\n")
        };
        let result = check_script(&spec);
        let problem = result
            .comments
            .iter()
            .find(|c| c.comment.code == 1134)
            .expect("SC1134");
        assert_eq!(problem.comment.severity, Severity::ErrorC);
        assert_eq!(
            problem.comment.message,
            "Failed to process /tmp/.shellcheckrc, line 2: Expected '=' after directive key. \
             Fix any mentioned problems and try again."
        );
        // `parseProblem` at the start of the script being checked.
        assert_eq!(problem.start.file, "s.sh");
        assert_eq!((problem.start.line, problem.start.column), (1, 1));
        assert_eq!((problem.end.line, problem.end.column), (1, 1));
        // It sorts before the other errors at 1:1 and is filterable like any
        // other comment.
        assert_eq!(codes(&spec), vec![1134, 2148, 2154, 2086]);
        let excluded = CheckSpec {
            excluded_warnings: vec![1134],
            ..spec.clone()
        };
        assert_eq!(codes(&excluded), vec![2148, 2154, 2086]);
    }

    #[test]
    fn an_unparsable_rc_is_reported_even_when_the_script_does_not_parse() {
        let spec = CheckSpec {
            rc: Some(Box::new(RcDirectives {
                disabled_ranges: Vec::new(),
                parse_problem: Some(RcParseProblem {
                    filename: "rc".to_string(),
                    line: 1,
                    suggestion: String::new(),
                }),
            })),
            ..spec("if true\n")
        };
        let result = check_script(&spec);
        let problem = result
            .comments
            .iter()
            .find(|c| c.comment.code == 1134)
            .expect("SC1134");
        // An empty suggestion leaves the double space the oracle prints.
        assert_eq!(
            problem.comment.message,
            "Failed to process rc, line 1:  Fix any mentioned problems and try again."
        );
        assert!(result.comments.iter().any(|c| c.comment.code == 1072));
    }
}
