//! Parser unit tests (ports of the `Parser.hs` props and regression cases).
use super::*;

#[cfg(test)]
mod arith_tests {
    use super::*;

    /// Mirrors `isOk readArithmeticContents s`: the parser succeeds, consumes
    /// all input (`>> eof`), and produces no notes or problems.
    fn arith_ok(script: &str) -> bool {
        let mut p = Parser::new("-", script);
        match p.read_arithmetic_contents() {
            Ok(_) => p.eof() && p.notes.is_empty() && p.problems.is_empty(),
            Err(()) => false,
        }
    }

    #[test]
    fn prop_a1() {
        assert!(arith_ok(" n++ + ++c"));
    }
    #[test]
    fn prop_a2() {
        assert!(arith_ok("$N*4-(3,2)"));
    }
    #[test]
    fn prop_a3() {
        assert!(arith_ok("n|=2<<1"));
    }
    #[test]
    fn prop_a4() {
        assert!(arith_ok("n &= 2 **3"));
    }
    #[test]
    fn prop_a5() {
        assert!(arith_ok("1 |= 4 && n >>= 4"));
    }
    #[test]
    fn prop_a6() {
        assert!(arith_ok(" 1 | 2 ||3|4"));
    }
    #[test]
    fn prop_a7() {
        assert!(arith_ok("3*2**10"));
    }
    #[test]
    fn prop_a8() {
        assert!(arith_ok("3"));
    }
    #[test]
    fn prop_a9() {
        assert!(arith_ok("a^!-b"));
    }
    #[test]
    fn prop_a10() {
        assert!(arith_ok("! $?"));
    }
    #[test]
    fn prop_a11() {
        assert!(arith_ok("10#08 * 16#f"));
    }
    #[test]
    fn prop_a12() {
        assert!(arith_ok("\"$((3+2))\" + '37'"));
    }
    #[test]
    fn prop_a13() {
        assert!(arith_ok("foo[9*y+x]++"));
    }
    #[test]
    fn prop_a14() {
        assert!(arith_ok("1+`echo 2`"));
    }
    #[test]
    fn prop_a15() {
        assert!(arith_ok("foo[`echo foo | sed s/foo/4/g` * 3] + 4"));
    }
    #[test]
    fn prop_a16() {
        assert!(arith_ok("$foo$bar"));
    }
    #[test]
    fn prop_a17() {
        assert!(arith_ok("i<(0+(1+1))"));
    }
    #[test]
    fn prop_a18() {
        assert!(arith_ok("a?b:c"));
    }
    #[test]
    fn prop_a19() {
        assert!(arith_ok("\\\n3 +\\\n  2"));
    }
    #[test]
    fn prop_a20() {
        assert!(arith_ok("a ? b ? c : d : e"));
    }
    #[test]
    fn prop_a21() {
        assert!(arith_ok("a ? b : c ? d : e"));
    }
    #[test]
    fn prop_a22() {
        assert!(arith_ok("!!a"));
    }
    #[test]
    fn prop_a23() {
        assert!(arith_ok("~0"));
    }
}

#[cfg(test)]
mod redirect_heredoc_tests {
    use super::*;

    // Collect every token whose inner matches the predicate, with its span.
    fn spans_of<F>(script: &str, pred: F) -> Vec<(i64, i64, i64, i64)>
    where
        F: Fn(&InnerToken) -> bool,
    {
        let out = parse_script("-", script);
        let root = out.root.expect("parse produced a tree");
        let mut found = Vec::new();
        root.visit_preorder(&mut |t| {
            if pred(&t.inner) {
                if let Some((s, e)) = out.positions.get(&t.id) {
                    found.push((s.line, s.column, e.line, e.column));
                }
            }
        });
        found
    }

    fn has_problem(script: &str, code: i64) -> bool {
        let out = parse_script("-", script);
        out.notes.iter().any(|n| n.code == code)
    }

    // ---- gap 1: `&>` / `&>>` combined redirect --------------------------

    #[test]
    fn ampersand_redirect_is_single_fd_redirect() {
        // `&>bar` is one T_FdRedirect (fd = "&"), not `&` + `>bar`.
        let redirs = spans_of("ls &>bar", |i| matches!(i, InnerToken::T_FdRedirect { .. }));
        assert_eq!(redirs.len(), 1, "expected one T_FdRedirect for &>");
        // fd source is "&"
        let out = parse_script("-", "ls &>bar");
        let root = out.root.unwrap();
        let mut fds = Vec::new();
        root.visit_preorder(&mut |t| {
            if let InnerToken::T_FdRedirect { fd, .. } = &*t.inner {
                fds.push(fd.clone());
            }
        });
        assert_eq!(fds, vec!["&".to_string()]);
        // Not backgrounded.
        let bg = spans_of("ls &>bar", |i| matches!(i, InnerToken::T_Backgrounded(_)));
        assert!(bg.is_empty(), "`&>` must not parse as backgrounding");
    }

    #[test]
    fn ampersand_dgreat_redirect() {
        let out = parse_script("-", "ls &>>bar");
        let root = out.root.unwrap();
        let mut ops = Vec::new();
        root.visit_preorder(&mut |t| {
            if let InnerToken::T_IoFile { op, .. } = &*t.inner {
                ops.push(matches!(*op.inner, InnerToken::T_DGREAT));
            }
        });
        assert_eq!(ops, vec![true], "&>> should carry a T_DGREAT operator");
    }

    // ---- gap 3: glued fd redirect operator span (SC2210) ----------------

    #[test]
    fn glued_fd_redirect_anchors_iofile_at_operator() {
        // `foo 1>2`: T_IoFile spans the operator `>` (col 6) through `2` (col 8),
        // NOT the fd digit at col 5. This is what SC2210 reports.
        let iofiles = spans_of("foo 1>2", |i| matches!(i, InnerToken::T_IoFile { .. }));
        assert_eq!(iofiles, vec![(1, 6, 1, 8)]);
        // The whole T_FdRedirect still starts at the fd digit (col 5).
        let fds = spans_of("foo 1>2", |i| matches!(i, InnerToken::T_FdRedirect { .. }));
        assert_eq!(fds, vec![(1, 5, 1, 8)]);
    }

    // ---- gap 2: heredoc body expansions ---------------------------------

    #[test]
    fn unquoted_heredoc_parses_command_substitution() {
        // The body `$(rm x)` must become a T_DollarExpansion node, not a flat
        // literal, so stdin-consumer analysis sees it.
        let subs = spans_of("cat << EOF\n$(rm x)\nEOF\n", |i| {
            matches!(i, InnerToken::T_DollarExpansion(_))
        });
        assert_eq!(subs.len(), 1, "expected a command substitution in the body");
    }

    #[test]
    fn unquoted_heredoc_parses_backtick() {
        let subs = spans_of("cat << EOF\n`rm x`\nEOF\n", |i| {
            matches!(i, InnerToken::T_Backticked(_))
        });
        assert_eq!(
            subs.len(),
            1,
            "expected a backtick substitution in the body"
        );
    }

    #[test]
    fn quoted_heredoc_does_not_expand() {
        // With a quoted delimiter the body stays a single literal.
        let subs = spans_of("cat << 'EOF'\n$(rm x)\nEOF\n", |i| {
            matches!(i, InnerToken::T_DollarExpansion(_))
        });
        assert!(subs.is_empty(), "quoted heredoc body must not be expanded");
    }

    #[test]
    fn heredoc_double_quote_is_literal() {
        // A `"` in an unquoted heredoc body is literal (readHereLiteral), and it
        // must not swallow the following expansion.
        let out = parse_script("-", "cat << EOF\na\"b$c\nEOF\n");
        assert!(out.root.is_some());
        let vars = spans_of("cat << EOF\na\"b$c\nEOF\n", |i| {
            matches!(
                i,
                InnerToken::T_DollarBraced { .. } | InnerToken::T_NormalWord(_)
            )
        });
        let _ = vars;
        // The `$c` variable is present.
        let dollar = {
            let out = parse_script("-", "cat << EOF\na\"b$c\nEOF\n");
            let root = out.root.unwrap();
            let mut n = 0;
            root.visit_preorder(&mut |t| {
                if matches!(&*t.inner, InnerToken::T_DollarBraced { .. }) {
                    n += 1;
                }
            });
            n
        };
        assert_eq!(dollar, 1, "the $c variable should be parsed in the body");
    }

    #[test]
    fn heredoc_still_terminates_and_parses_ok() {
        // Regression guard: a heredoc with an expansion parses without a
        // spurious problem (e.g. SC1044 unterminated).
        assert!(!has_problem("cat << EOF\n$(date)\nEOF\n", 1044));
    }
}

#[cfg(test)]
mod parser_gap_tests {
    use super::*;

    fn spans_of<F>(script: &str, pred: F) -> Vec<(i64, i64, i64, i64)>
    where
        F: Fn(&InnerToken) -> bool,
    {
        let out = parse_script("-", script);
        let root = out.root.expect("parse produced a tree");
        let mut found = Vec::new();
        root.visit_preorder(&mut |t| {
            if pred(&t.inner) {
                if let Some((s, e)) = out.positions.get(&t.id) {
                    found.push((s.line, s.column, e.line, e.column));
                }
            }
        });
        found
    }

    fn literals_of(script: &str) -> Vec<String> {
        let out = parse_script("-", script);
        let root = out.root.expect("parse produced a tree");
        let mut found = Vec::new();
        root.visit_preorder(&mut |t| {
            if let InnerToken::T_Literal(s) = &*t.inner {
                found.push(s.clone());
            }
        });
        found
    }

    // ---- gap 1: TC_Unary span anchors on the operator alone ---------------

    #[test]
    fn tc_unary_op_span_is_operator_only() {
        // `[ -M a ]`: the TC_Unary id must span just `-M` (cols 3-5), matching
        // ShellCheck's `readCondUnaryOp` (`endSpan` right after `readOp`), not
        // operator+operand. This is what SC2058/SC2331/... key off.
        let spans = spans_of("[ -M a ]", |i| matches!(i, InnerToken::TC_Unary { .. }));
        assert_eq!(
            spans,
            vec![(1, 3, 1, 5)],
            "TC_Unary must span the operator only"
        );
    }

    #[test]
    fn tc_unary_z_span_is_operator_only() {
        // `[ -z $(fgrep x) ]` (the SC2143 unary branch): `-z` at cols 3-5.
        let spans = spans_of("[ -z $(fgrep x) ]", |i| {
            matches!(i, InnerToken::TC_Unary { .. })
        });
        assert_eq!(spans, vec![(1, 3, 1, 5)]);
    }

    #[test]
    fn tc_unary_bang_span_is_bang_only() {
        // `[ ! x ]`: the negation TC_Unary id must span just `!` (cols 3-4),
        // matching `readCondNot` (`endSpan` right after `char '!'`).
        let spans = spans_of(
            "[ ! x ]",
            |i| matches!(i, InnerToken::TC_Unary { op, .. } if op == "!"),
        );
        assert_eq!(spans, vec![(1, 3, 1, 4)]);
    }

    #[test]
    fn tc_unary_v_span_is_operator_only() {
        // `[ -v var ]`: `-v` at cols 3-5.
        let spans = spans_of("[ -v var ]", |i| matches!(i, InnerToken::TC_Unary { .. }));
        assert_eq!(spans, vec![(1, 3, 1, 5)]);
    }

    // ---- gap 2: regex RHS preserves backslash escapes raw -----------------

    #[test]
    fn regex_rhs_preserves_backslash_escape() {
        // `[[ $x =~ \* ]]`: the regex literal keeps the raw `\*`, not a decoded
        // `*` (Parser.hs `readLiteralForParser` reads the raw span).
        let lits = literals_of("[[ $x =~ \\* ]]");
        assert!(
            lits.iter().any(|s| s == "\\*"),
            "regex `\\*` must stay raw, got {lits:?}"
        );
        assert!(
            !lits.iter().any(|s| s == "*"),
            "regex `\\*` must not decode to `*`, got {lits:?}"
        );
    }

    #[test]
    fn regex_rhs_preserves_dotted_escapes() {
        // `[[ $1 =~ \.a\.c\. ]]`: escaped dots are kept raw.
        let lits = literals_of("[[ $1 =~ \\.a\\.c\\. ]]");
        assert!(
            lits.iter().any(|s| s.contains("\\.")),
            "escaped dots must stay raw, got {lits:?}"
        );
    }

    // ---- gap 3: mid-pipeline `!` becomes T_Banged -------------------------

    #[test]
    fn mid_pipeline_bang_is_banged() {
        // `true | ! true`: the second stage is negated (T_Banged), bang at col 8.
        let spans = spans_of("true | ! true", |i| matches!(i, InnerToken::T_Banged(_)));
        assert_eq!(
            spans,
            vec![(1, 8, 1, 9)],
            "mid-pipeline `!` must produce T_Banged"
        );
    }

    #[test]
    fn leading_bang_still_banged() {
        // Regression guard: `! cat | grep x` keeps the leading bang as T_Banged.
        let spans = spans_of("! cat | grep x", |i| matches!(i, InnerToken::T_Banged(_)));
        assert_eq!(spans, vec![(1, 1, 1, 2)]);
    }

    // ---- gap 4: `${{var}` parses the `${...}` as an expansion -------------

    #[test]
    fn dollar_brace_open_brace_is_expansion() {
        // `${{var}`: the `${...}` is a T_DollarBraced (cols 1-8), whose word is
        // the literal `{var`. Its op word span is used by SC2296 (cols 3-7).
        let spans = spans_of("${{var}", |i| {
            matches!(i, InnerToken::T_DollarBraced { .. })
        });
        assert_eq!(
            spans,
            vec![(1, 1, 1, 8)],
            "expected one T_DollarBraced for ${{{{var}}"
        );
    }

    // ---- gap 5: `time` as a pipeline prefix -------------------------------

    #[test]
    fn time_wraps_pipeline_in_suffix() {
        // `time foo | bar`: the pipeline is a suffix word of the `time` simple
        // command (Parser.hs `readTimeSuffix`), so there is exactly one
        // top-level pipeline containing the `time` command, and a nested
        // pipeline `foo | bar` inside its suffix.
        let out = parse_script("-", "time foo | bar");
        let root = out.root.expect("parse produced a tree");
        // A T_Pipeline with two commands (foo | bar) must exist somewhere.
        let mut multi_stage = 0;
        root.visit_preorder(&mut |t| {
            if let InnerToken::T_Pipeline { commands, .. } = &*t.inner {
                if commands.len() == 2 {
                    multi_stage += 1;
                }
            }
        });
        assert_eq!(
            multi_stage, 1,
            "the `foo | bar` pipeline must be nested under `time`"
        );
    }

    #[test]
    fn bare_time_before_a_pipe_is_a_command() {
        // `readTimeSuffix` fails here without consuming -- `readSimpleCommand`
        // bails on `|` with `fail "Expected a command"` before reading
        // anything -- so `option []` recovers and `time` stands alone as a
        // simple command. In dash it is an ordinary command name, and the
        // `||` that follows belongs to the enclosing and-or.
        for script in ["time |y", "time ||cd"] {
            let out = parse_script("-", script);
            assert!(
                !out.notes.iter().any(|n| n.code == 1072 || n.code == 1073),
                "{script} must parse: {:?}",
                out.notes
            );
        }
    }

    #[test]
    fn time_with_flag_and_compound() {
        // `time -p ( ls -l; )` parses without error.
        let out = parse_script("-", "time -p ( ls -l; )");
        assert!(out.root.is_some());
        // No fatal parse problem (SC1072/SC1073) should be reported.
        assert!(
            !out.notes.iter().any(|n| n.code == 1072 || n.code == 1073),
            "time -p (..) must parse cleanly: {:?}",
            out.notes
        );
    }
}

#[cfg(test)]
mod coproc_glob_dollar_tests {
    use super::*;

    fn count_nodes<F>(script: &str, pred: F) -> usize
    where
        F: Fn(&InnerToken) -> bool,
    {
        let out = parse_script("-", script);
        let root = out.root.expect("parse produced a tree");
        let mut n = 0;
        root.visit_preorder(&mut |t| {
            if pred(&t.inner) {
                n += 1;
            }
        });
        n
    }

    fn has_note(script: &str, code: i64) -> bool {
        parse_script("-", script)
            .notes
            .iter()
            .any(|n| n.code == code)
    }

    // ---- P1: coproc parsing -----------------------------------------------

    #[test]
    fn coproc_compound_with_name() {
        // `coproc foo { echo bar; }`: one T_CoProc whose name is Some, and a
        // T_CoProcBody wrapping the compound command. No spurious SC1072.
        let script = "coproc foo { echo bar; }";
        assert!(!has_note(script, 1072), "coproc must parse without SC1072");
        let out = parse_script("-", script);
        let root = out.root.unwrap();
        let mut named = 0;
        let mut bodies = 0;
        root.visit_preorder(&mut |t| match &*t.inner {
            InnerToken::T_CoProc { name: Some(_), .. } => named += 1,
            InnerToken::T_CoProcBody(_) => bodies += 1,
            _ => {}
        });
        assert_eq!(named, 1, "expected one named T_CoProc");
        assert_eq!(bodies, 1, "expected one T_CoProcBody");
    }

    #[test]
    fn coproc_compound_without_name() {
        // `coproc { echo bar; }`: T_CoProc with name None.
        let script = "coproc { echo bar; }";
        assert!(!has_note(script, 1072));
        let out = parse_script("-", script);
        let root = out.root.unwrap();
        let mut unnamed = 0;
        root.visit_preorder(&mut |t| {
            if let InnerToken::T_CoProc { name: None, .. } = &*t.inner {
                unnamed += 1;
            }
        });
        assert_eq!(unnamed, 1, "expected one unnamed T_CoProc");
    }

    #[test]
    fn coproc_simple_command() {
        // `coproc echo bar`: simple form, T_CoProc name None + T_CoProcBody.
        let script = "coproc echo bar";
        assert!(!has_note(script, 1072));
        assert_eq!(
            count_nodes(script, |i| matches!(
                i,
                InnerToken::T_CoProc { name: None, .. }
            )),
            1
        );
        assert_eq!(
            count_nodes(script, |i| matches!(i, InnerToken::T_CoProcBody(_))),
            1
        );
    }

    #[test]
    fn coproc_named_while_loop() {
        // `coproc foo while true; do true; done`: compound (while) body, named.
        let script = "coproc foo while true; do true; done";
        assert!(
            !has_note(script, 1072),
            "coproc + while must parse without SC1072"
        );
        assert_eq!(
            count_nodes(script, |i| matches!(
                i,
                InnerToken::T_CoProc { name: Some(_), .. }
            )),
            1
        );
        assert_eq!(
            count_nodes(script, |i| matches!(
                i,
                InnerToken::T_WhileExpression { .. }
            )),
            1,
            "the while loop must be parsed as the coproc body"
        );
    }

    // ---- P2: glob class no longer swallows expansions ---------------------

    #[test]
    fn glob_class_stops_at_dollar() {
        // `unset foo[$i]`: `$i` must become a real T_DollarBraced expansion, and
        // no T_Glob may contain the `$` (the class body must not swallow it).
        let script = "unset foo[$i]";
        let out = parse_script("-", script);
        let root = out.root.unwrap();
        let mut dollar_i = 0;
        let mut glob_with_dollar = 0;
        root.visit_preorder(&mut |t| match &*t.inner {
            InnerToken::T_DollarBraced { op, .. } => {
                if let InnerToken::T_NormalWord(parts) = &*op.inner {
                    if let [p] = &parts[..] {
                        if let InnerToken::T_Literal(s) = &*p.inner {
                            if s == "i" {
                                dollar_i += 1;
                            }
                        }
                    }
                }
            }
            InnerToken::T_Glob(g) if g.contains('$') => glob_with_dollar += 1,
            _ => {}
        });
        assert_eq!(dollar_i, 1, "`$i` must parse as a real expansion");
        assert_eq!(glob_with_dollar, 0, "no T_Glob may swallow the `$`");
    }

    #[test]
    fn glob_class_still_parses_valid_class() {
        // A real character class `[abc]` still parses to a single T_Glob("[abc]").
        assert_eq!(
            count_nodes(
                "ls f[abc]",
                |i| matches!(i, InnerToken::T_Glob(g) if g == "[abc]")
            ),
            1
        );
        // POSIX predefined class survives too.
        assert_eq!(
            count_nodes(
                "ls f[[:digit:]]",
                |i| matches!(i, InnerToken::T_Glob(g) if g == "[[:digit:]]")
            ),
            1
        );
    }

    // ---- P3a: SC1037 note is zero-width at the `$` -------------------------

    #[test]
    fn sc1037_note_is_zero_width_at_dollar() {
        // `echo "$12"`: `$` is at column 7, so SC1037 must be zero-width 1:7-1:7.
        let out = parse_script("-", "echo \"$12\"");
        let note = out
            .notes
            .iter()
            .find(|n| n.code == 1037)
            .expect("SC1037 must fire on $12");
        assert_eq!(
            (
                note.start.line,
                note.start.column,
                note.end.line,
                note.end.column
            ),
            (1, 7, 1, 7),
            "SC1037 must be zero-width at the `$`"
        );
    }

    // ---- P3b: inner literal word of `$name` starts after the `$` -----------

    #[test]
    fn dollar_var_inner_word_starts_after_dollar() {
        // `echo $foo`: `$` at column 6; the inner T_NormalWord/T_Literal("foo")
        // must start at column 7 (after the `$`), while the outer T_DollarBraced
        // stays anchored at the `$` (column 6).
        let out = parse_script("-", "echo $foo");
        let root = out.root.unwrap();
        let mut outer: Option<(i64, i64)> = None;
        let mut inner_word: Option<(i64, i64)> = None;
        root.visit_preorder(&mut |t| {
            if let InnerToken::T_DollarBraced { braced: false, op } = &*t.inner {
                if let InnerToken::T_NormalWord(parts) = &*op.inner {
                    if let [p] = &parts[..] {
                        if let InnerToken::T_Literal(s) = &*p.inner {
                            if s == "foo" {
                                if let Some((s0, _)) = out.positions.get(&t.id) {
                                    outer = Some((s0.line, s0.column));
                                }
                                if let Some((s1, _)) = out.positions.get(&op.id) {
                                    inner_word = Some((s1.line, s1.column));
                                }
                            }
                        }
                    }
                }
            }
        });
        assert_eq!(
            outer,
            Some((1, 6)),
            "outer T_DollarBraced anchors at the `$`"
        );
        assert_eq!(inner_word, Some((1, 7)), "inner word starts after the `$`");
    }

    // ---- SC1008: unrecognized shebang -------------------------------------

    #[test]
    fn sc1008_unrecognized_shebang() {
        // `#!/bin/busybox ash`: interpreter "busybox ash" is neither a good nor a
        // known-bad shell, so SC1008 fires at the start of the file.
        let out = parse_script("-", "#!/bin/busybox ash\n");
        let note = out
            .notes
            .iter()
            .find(|n| n.code == 1008)
            .expect("SC1008 must fire on an unrecognized shebang");
        assert_eq!(note.severity, Severity::ErrorC);
        assert_eq!(
            (
                note.start.line,
                note.start.column,
                note.end.line,
                note.end.column
            ),
            (1, 1, 1, 1),
            "SC1008 is anchored at the start of the file"
        );
        assert_eq!(
            note.message,
            "This shebang was unrecognized. ShellCheck only supports sh/bash/dash/ksh/'busybox sh'. Add a 'shell' directive to specify."
        );
    }

    #[test]
    fn sc1008_not_for_recognized_shebang() {
        assert!(!has_note("#!/bin/sh\n", 1008));
        assert!(!has_note("#!/bin/bash\n", 1008));
        assert!(!has_note("#!/bin/busybox sh\n", 1008));
        // An empty shebang is treated as "good" (Just true), so no SC1008.
        assert!(!has_note("echo hi\n", 1008));
    }

    #[test]
    fn sc1008_suppressed_by_shell_directive() {
        // A `# shellcheck shell=...` directive overrides the shebang, so no SC1008.
        assert!(!has_note(
            "#!/bin/busybox ash\n# shellcheck shell=sh\n",
            1008
        ));
    }

    // ---- modifier suffix: an unterminated array assignment ----------------

    #[test]
    fn unterminated_array_after_a_modifier_command_fails_the_command() {
        // `readModifierSuffix`'s assignment is inside `many1`, so a failure
        // that consumed input ends the command: `readonly f=(` is an unclosed
        // array assignment, not the word `(` after `readonly f=`.
        let out = parse_script("-", "readonly f=(");
        let codes: Vec<i64> = out.notes.iter().map(|n| n.code).collect();
        assert!(codes.contains(&1073), "expected SC1073, got {codes:?}");
        assert!(
            !codes.contains(&1036),
            "the `(` must not be re-read as a word: {codes:?}"
        );
        // A well-formed one still parses.
        assert!(!has_note("readonly f=(1 2)\n", 1073));
    }

    // ---- SC1017: a literal carriage return --------------------------------

    #[test]
    fn sc1017_carriage_return_in_a_comment() {
        // `readComment` is `readAnyComment` after the annotation guard, and its
        // body is `many $ noneOf "\r\n"` -- so the CR is left for
        // `carriageReturn`, which is what reports it.
        assert!(has_note("#\r\n", 1017));
        assert!(has_note("# hello\r\necho hi\n", 1017));
        assert!(has_note("{#\r", 1017));
        assert!(!has_note("# hello\necho hi\n", 1017));
    }

    // ---- SC1019: a unary test operator with no argument -------------------

    #[test]
    fn sc1019_missing_argument_to_a_unary_condition() {
        // `orFail = try parser <|> ..`: the argument attempt runs in a `try`,
        // so it is reported whether reading the argument failed having consumed
        // nothing (`[ -n `) or having consumed an unterminated expansion.
        for script in ["[ -n ", "[ -n $(", "[-n$(", "[-z${", "[-a$("] {
            assert!(has_note(script, 1019), "SC1019 must fire on {script:?}");
        }
        assert!(!has_note("[ -n x ]", 1019));
    }

    // ---- SC1133: a line starting with |/||/&& -----------------------------

    #[test]
    fn sc1133_line_starting_with_an_operator() {
        for script in ["echo a\n|| echo b\n", "echo a\n| cat\n", "echo a\n&& b\n"] {
            assert!(has_note(script, 1133), "SC1133 must fire on {script:?}");
        }
        let note = parse_script("-", "echo a\n|| echo b\n")
            .notes
            .into_iter()
            .find(|n| n.code == 1133)
            .expect("SC1133");
        assert_eq!(
            (note.start.line, note.start.column),
            (2, 1),
            "SC1133 points at the start of the offending line"
        );
    }

    #[test]
    fn sc1133_not_for_redirections_or_well_formed_breaks() {
        // `&>` and `&>>` start a redirection, not an operator.
        assert!(!has_note("echo a\n&> /dev/null\n", 1133));
        assert!(!has_note("echo a\n&>> log\n", 1133));
        // The operator at the end of the previous line is the correct spelling.
        assert!(!has_note("echo a ||\necho b\n", 1133));
        assert!(!has_note("echo a\necho b\n", 1133));
    }

    // ---- SC1014: command used as a test operand ---------------------------

    #[test]
    fn sc1014_command_in_single_bracket() {
        // `[ test =~ foo ]`: "test" is a common command, so SC1014 fires at the
        // start of the word (column 3).
        let out = parse_script("-", "[ test =~ foo ]");
        let note = out
            .notes
            .iter()
            .find(|n| n.code == 1014)
            .expect("SC1014 must fire on a common command in [ .. ]");
        assert_eq!(note.severity, Severity::WarningC);
        assert_eq!(
            (
                note.start.line,
                note.start.column,
                note.end.line,
                note.end.column
            ),
            (1, 3, 1, 3),
            "SC1014 is anchored at the start of the operand word"
        );
        assert_eq!(
            note.message,
            "Use 'if cmd; then ..' to check exit code, or 'if [[ $(cmd) == .. ]]' to check output."
        );
    }

    #[test]
    fn sc1014_not_for_ordinary_operand() {
        assert!(!has_note("[ x = y ]", 1014));
        assert!(!has_note("[ -n foo ]", 1014));
        // The lookahead must not consume input: the condition still parses.
        assert!(!has_note("[ test =~ foo ]", 1072));
    }

    #[test]
    fn a_comment_is_spacing_inside_a_condition() {
        // `condSpacing`'s `allspacing` ends in `optional readComment`, so the
        // `#` opens a comment rather than starting a word: the `-x` is left
        // with no argument and the test expression does not parse.
        for script in ["[[# =x ]]", "[ -x# ]"] {
            assert!(
                !parses_as(Some(Shell::Ksh), script),
                "{script} must not parse: the `#` is a comment, not a word"
            );
        }
    }

    // ---- SC1127: command word that looks like a comment -------------------

    #[test]
    fn sc1127_slash_star() {
        // `/*` as a command word: SC1127 spans the whole command word.
        let out = parse_script("-", "/*");
        let note = out
            .notes
            .iter()
            .find(|n| n.code == 1127)
            .expect("SC1127 must fire on a `/*` command word");
        assert_eq!(note.severity, Severity::ErrorC);
        assert_eq!(note.message, "Was this intended as a comment? Use # in sh.");
    }

    #[test]
    fn sc1127_double_slash() {
        assert!(has_note("// this is a comment", 1127));
    }

    #[test]
    fn sc1127_not_for_ordinary_command() {
        assert!(!has_note("echo hi", 1127));
        assert!(!has_note("/bin/sh", 1127));
    }

    // ---- known divergences ------------------------------------------------
    //
    // These assert what the *oracle* does, and are marked `should_panic`
    // because the port does not do it yet — Rust's nearest thing to Vitest's
    // `test.fails` / bun's `test.failing`. Fixing the port makes the assertion
    // pass, which makes the test fail, which is the reminder to delete the
    // marker and the `DIVERGENCES.md` entry together. Only the port-side half
    // of an entry can live here; the oracle's output is not available in a unit
    // test, so the full comparison stays in the conformance harness.

    #[test]
    #[should_panic(expected = "DIVERGENCES.md A3")]
    fn function_as_a_command_name_should_parse() {
        assert!(
            parses_as(Some(Shell::Dash), "function | { x; }"),
            "DIVERGENCES.md A3: `function` piped into a brace group is a command, not a definition"
        );
    }

    #[test]
    #[should_panic(expected = "DIVERGENCES.md B2")]
    fn an_unterminated_quoted_directive_value_should_not_parse() {
        assert!(
            !parses_as(None, "#shellcheck disable=\"\nfor f in $();do :;done\n"),
            "DIVERGENCES.md B2: upstream makes `disable=\"` a parse error"
        );
    }

    // ---- `!` with nothing to negate ---------------------------------------
    //
    // The port's one deliberate departure from upstream's parse decisions: bash
    // negates the null command, upstream rejects the file for every dialect and
    // so analyses none of it. See PARITY-NOTES.md.

    /// Parse as a named dialect, as `--shell` would.
    fn parses_as(shell: Option<Shell>, script: &str) -> bool {
        let out = parse_script_with("-", script, shell.is_some(), shell);
        out.root.is_some()
    }

    #[test]
    fn bare_bang_parses_for_bash() {
        for script in [
            "! ",
            "! # negate what, exactly",
            "! ;",
            "! ; echo hi",
            "! !",
            "if ! ; then echo a; fi",
            "f() { ! ; }",
        ] {
            assert!(
                parses_as(Some(Shell::Bash), script),
                "bash accepts {script:?}"
            );
        }
    }

    #[test]
    fn bare_bang_still_fails_for_posix_shells() {
        // dash rejects every one of these, so upstream's error is right there.
        for shell in [Shell::Sh, Shell::Dash, Shell::Ksh, Shell::BusyboxSh] {
            assert!(
                !parses_as(Some(shell), "! # c"),
                "{shell:?} must still reject a bare `!`"
            );
        }
        // The shebang settles it when no flag does.
        assert!(!parses_as(None, "#!/bin/sh\n! # c\n"));
        assert!(parses_as(None, "#!/bin/bash\n! # c\n"));
        // Nothing said: ShellCheck assumes bash.
        assert!(parses_as(None, "! # c"));
    }

    #[test]
    fn bare_bang_fails_where_bash_itself_fails() {
        // Verified against bash 5.2: only end-of-line and a single `;` are ok.
        for script in ["! &", "! ;;", "! | true", "! && true", "(!)"] {
            assert!(
                !parses_as(Some(Shell::Bash), script),
                "bash rejects {script:?} too"
            );
        }
        // `!#` keeps upstream's reading: the `!` is the negation operator and
        // the missing space is an error. (On line 1 it is the shebang check
        // SC1084 instead, and that parses.)
        assert!(!parses_as(Some(Shell::Bash), "echo hi\n!#\n"));
    }

    #[test]
    fn a_bare_bang_does_not_stop_the_rest_being_analysed() {
        // The point of the deviation: line 3 still gets checked.
        let spec = crate::interface::CheckSpec {
            filename: "-".to_string(),
            script: "#!/bin/bash\n! # c\necho $undefined\n".to_string(),
            ..crate::interface::CheckSpec::default()
        };
        let codes: Vec<i64> = crate::check_script(&spec)
            .comments
            .iter()
            .map(|c| c.comment.code)
            .collect();
        assert!(codes.contains(&2154), "got {codes:?}");
        assert!(
            !codes.iter().any(|c| [1072, 1073, 1009].contains(c)),
            "no fatal parse codes, got {codes:?}"
        );
    }
}
