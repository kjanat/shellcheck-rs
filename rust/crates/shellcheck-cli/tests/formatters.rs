//! Formatter output tests against known-good strings captured from the real
//! `shellcheck` oracle (v0.11.0) on a small autofix script:
//!
//! ```sh
//! #!/bin/bash
//! echo `date`
//! ```
//!
//! which yields SC2046 (warning), SC2005 (style), SC2006 (style, with a fix).

use shellcheck_cli::formatter::{checkstyle, diff, gcc, json, json1, tty};
use shellcheck_rs::interface::{
    Comment, Fix, InsertionPoint, Position, PositionedComment, Replacement, Severity,
};

const CONTENTS: &str = "#!/bin/bash\necho `date`\n";

fn pos(line: i64, col: i64) -> Position {
    Position { file: "fix.sh".to_string(), line, column: col }
}

fn comment(sev: Severity, code: i64, msg: &str, sc: i64, ec: i64, fix: Option<Fix>) -> PositionedComment {
    PositionedComment {
        start: pos(2, sc),
        end: pos(2, ec),
        comment: Comment { severity: sev, code, message: msg.to_string() },
        fix,
    }
}

fn sample() -> Vec<PositionedComment> {
    let fix = Fix {
        replacements: vec![
            Replacement {
                start: pos(2, 6),
                end: pos(2, 7),
                string: "$(".to_string(),
                precedence: 7,
                insertion_point: InsertionPoint::InsertAfter,
            },
            Replacement {
                start: pos(2, 11),
                end: pos(2, 12),
                string: ")".to_string(),
                precedence: 7,
                insertion_point: InsertionPoint::InsertBefore,
            },
        ],
    };
    vec![
        comment(Severity::WarningC, 2046, "Quote this to prevent word splitting.", 6, 12, None),
        comment(Severity::StyleC, 2005, "Useless echo? Instead of 'echo $(cmd)', just use 'cmd'.", 6, 12, None),
        comment(Severity::StyleC, 2006, "Use $(...) notation instead of legacy backticks `...`.", 6, 12, Some(fix)),
    ]
}

#[test]
fn gcc_matches_oracle() {
    let mut out = String::new();
    gcc::render_file("fix.sh", CONTENTS, &sample(), &mut out);
    assert_eq!(
        out,
        "fix.sh:2:6: warning: Quote this to prevent word splitting. [SC2046]\n\
         fix.sh:2:6: note: Useless echo? Instead of 'echo $(cmd)', just use 'cmd'. [SC2005]\n\
         fix.sh:2:6: note: Use $(...) notation instead of legacy backticks `...`. [SC2006]\n"
    );
}

#[test]
fn checkstyle_matches_oracle() {
    let mut out = String::new();
    out.push_str(checkstyle::HEADER);
    checkstyle::render_file("fix.sh", CONTENTS, &sample(), &mut out);
    out.push_str(checkstyle::FOOTER);
    let expected = "<?xml version='1.0' encoding='UTF-8'?>\n\
<checkstyle version='4.3'>\n\
<file name='fix.sh' >\n\
<error line='2' column='6' severity='warning' message='Quote this to prevent word splitting.' source='ShellCheck.SC2046' />\n\
<error line='2' column='6' severity='info' message='Useless echo&#63; Instead of &#39;echo &#36;&#40;cmd&#41;&#39;&#44; just use &#39;cmd&#39;.' source='ShellCheck.SC2005' />\n\
<error line='2' column='6' severity='info' message='Use &#36;&#40;...&#41; notation instead of legacy backticks &#96;...&#96;.' source='ShellCheck.SC2006' />\n\
</file>\n\
</checkstyle>\n";
    assert_eq!(out, expected);
}

#[test]
fn checkstyle_clean_file_has_empty_block() {
    let mut out = String::new();
    out.push_str(checkstyle::HEADER);
    checkstyle::render_file("clean.sh", "#!/bin/sh\n", &[], &mut out);
    out.push_str(checkstyle::FOOTER);
    assert_eq!(
        out,
        "<?xml version='1.0' encoding='UTF-8'?>\n\
         <checkstyle version='4.3'>\n\
         <file name='clean.sh' >\n\
         </file>\n\
         </checkstyle>\n"
    );
}

#[test]
fn json1_matches_oracle() {
    let out = json1::render(&sample());
    let expected = r#"{"comments":[{"file":"fix.sh","line":2,"endLine":2,"column":6,"endColumn":12,"level":"warning","code":2046,"message":"Quote this to prevent word splitting.","fix":null},{"file":"fix.sh","line":2,"endLine":2,"column":6,"endColumn":12,"level":"style","code":2005,"message":"Useless echo? Instead of 'echo $(cmd)', just use 'cmd'.","fix":null},{"file":"fix.sh","line":2,"endLine":2,"column":6,"endColumn":12,"level":"style","code":2006,"message":"Use $(...) notation instead of legacy backticks `...`.","fix":{"replacements":[{"column":6,"endColumn":7,"endLine":2,"insertionPoint":"afterEnd","line":2,"precedence":7,"replacement":"$("},{"column":11,"endColumn":12,"endLine":2,"insertionPoint":"beforeStart","line":2,"precedence":7,"replacement":")"}]}}]}"#;
    assert_eq!(out, expected);
}

#[test]
fn json_legacy_matches_oracle() {
    let out = json::render(&sample());
    let expected = r#"[{"file":"fix.sh","line":2,"endLine":2,"column":6,"endColumn":12,"level":"warning","code":2046,"message":"Quote this to prevent word splitting.","fix":null},{"file":"fix.sh","line":2,"endLine":2,"column":6,"endColumn":12,"level":"style","code":2005,"message":"Useless echo? Instead of 'echo $(cmd)', just use 'cmd'.","fix":null},{"file":"fix.sh","line":2,"endLine":2,"column":6,"endColumn":12,"level":"style","code":2006,"message":"Use $(...) notation instead of legacy backticks `...`.","fix":{"replacements":[{"column":6,"endColumn":7,"endLine":2,"insertionPoint":"afterEnd","line":2,"precedence":7,"replacement":"$("},{"column":11,"endColumn":12,"endLine":2,"insertionPoint":"beforeStart","line":2,"precedence":7,"replacement":")"}]}}]"#;
    assert_eq!(out, expected);
}

#[test]
fn tty_matches_oracle_no_color() {
    let color = shellcheck_cli::formatter::tty_color_func(false);
    let mut wiki: Vec<tty::WikiEntry> = Vec::new();
    let mut out = String::new();
    tty::render_file(&color, "fix.sh", CONTENTS, &sample(), &mut wiki, &mut out);
    tty::render_wiki(&wiki, 3, &mut out);
    // Built without backslash line-continuations, which would strip the
    // load-bearing leading indentation.
    let expected = concat!(
        "\n",
        "In fix.sh line 2:\n",
        "echo `date`\n",
        "     ^----^ SC2046 (warning): Quote this to prevent word splitting.\n",
        "     ^----^ SC2005 (style): Useless echo? Instead of 'echo $(cmd)', just use 'cmd'.\n",
        "     ^----^ SC2006 (style): Use $(...) notation instead of legacy backticks `...`.\n",
        "\n",
        "Did you mean:\n",
        "echo $(date)\n",
        "\n",
        "For more information:\n",
        "  https://www.shellcheck.net/wiki/SC2046 -- Quote this to prevent word splitt...\n",
        "  https://www.shellcheck.net/wiki/SC2005 -- Useless echo? Instead of 'echo $(...\n",
        "  https://www.shellcheck.net/wiki/SC2006 -- Use $(...) notation instead of le...\n",
    );
    assert_eq!(out, expected);
}

#[test]
fn diff_matches_oracle_no_color() {
    let d = diff::render_file(false, "fix.sh", CONTENTS, &sample());
    assert!(d.reported);
    assert_eq!(
        d.text,
        "--- a/fix.sh\n\
         +++ b/fix.sh\n\
         @@ -1,2 +1,2 @@\n\
         \x20#!/bin/bash\n\
         -echo `date`\n\
         +echo $(date)\n\
         \n"
    );
}

#[test]
fn diff_no_trailing_newline_marker() {
    // Same script without a trailing newline emits the no-newline marker.
    let no_nl = "#!/bin/bash\necho `date`";
    let d = diff::render_file(false, "fix.sh", no_nl, &sample());
    assert_eq!(
        d.text,
        "--- a/fix.sh\n\
         +++ b/fix.sh\n\
         @@ -1,2 +1,2 @@\n\
         \x20#!/bin/bash\n\
         -echo `date`\n\
         \\ No newline at end of file\n\
         +echo $(date)\n\
         \n"
    );
}
