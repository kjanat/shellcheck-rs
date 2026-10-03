//! Each case runs through the oracle at `.cache/shellcheck-oracle` and through
//! `rshellcheck`, and both must print the same stdout and stderr and exit alike.

use std::io::{self, Write};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

struct Case {
    args: &'static [&'static str],
    stdin: &'static [u8],
    files: &'static [(&'static str, &'static [u8])],
    unreadable: &'static [&'static str],
    full_stdout: bool,
}

const fn script(stdin: &'static [u8]) -> Case {
    Case {
        args: &["-f", "json1", "-"],
        stdin,
        files: &[],
        unreadable: &[],
        full_stdout: false,
    }
}

const fn files(
    args: &'static [&'static str],
    files: &'static [(&'static str, &'static [u8])],
) -> Case {
    Case {
        args,
        stdin: b"",
        files,
        unreadable: &[],
        full_stdout: false,
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Run {
    code: Option<i32>,
    stdout: String,
    stderr: String,
}

fn oracle() -> io::Result<PathBuf> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../.cache/shellcheck-oracle");
    if path.is_file() {
        Ok(path)
    } else {
        Err(io::Error::other(format!(
            "no oracle at {}; build it with `cabal build shellcheck` and copy `cabal list-bin shellcheck` there",
            path.display()
        )))
    }
}

fn run(binary: &Path, dir: &Path, case: &Case) -> io::Result<Run> {
    let stdout = if case.full_stdout {
        Stdio::from(std::fs::OpenOptions::new().write(true).open("/dev/full")?)
    } else {
        Stdio::piped()
    };
    let mut child = Command::new(binary)
        .args(case.args)
        .current_dir(dir)
        .env_remove("SHELLCHECK_OPTS")
        .env("HOME", dir.join(".home"))
        .env("XDG_CONFIG_HOME", dir.join(".xdg"))
        .stdin(Stdio::piped())
        .stdout(stdout)
        .stderr(Stdio::piped())
        .spawn()?;
    let mut input = child
        .stdin
        .take()
        .ok_or_else(|| io::Error::other("stdin is not piped"))?;
    input.write_all(case.stdin)?;
    drop(input);
    let out = child.wait_with_output()?;
    Ok(Run {
        code: out.status.code(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    })
}

fn assert_parity(name: &str, case: &Case) -> io::Result<()> {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("parity-{name}-{}", std::process::id()));
    if dir.exists() {
        std::fs::remove_dir_all(&dir)?;
    }
    std::fs::create_dir_all(dir.join(".home"))?;
    std::fs::create_dir_all(dir.join(".xdg"))?;
    for (path, contents) in case.files {
        let path = dir.join(path);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, contents)?;
    }
    for path in case.unreadable {
        std::fs::set_permissions(dir.join(path), std::fs::Permissions::from_mode(0o000))?;
    }
    let oracle = run(&oracle()?, &dir, case);
    let port = run(Path::new(env!("CARGO_BIN_EXE_rshellcheck")), &dir, case);
    for path in case.unreadable {
        std::fs::set_permissions(dir.join(path), std::fs::Permissions::from_mode(0o644))?;
    }
    std::fs::remove_dir_all(&dir)?;
    assert_eq!(
        port?, oracle?,
        "{name}: port (left) and oracle (right) differ"
    );
    Ok(())
}

macro_rules! parity {
    ($($name:ident = $case:expr;)*) => {$(
        #[test]
        fn $name() -> io::Result<()> {
            assert_parity(stringify!($name), &$case)
        }
    )*};
}

parity! {
    errexit_in_combined_set_flags = script(b"#!/bin/bash\nset -xe\ncd foo\n! true\necho ok\n");
    errexit_ignored_after_double_dash = script(b"#!/bin/bash\nset -- -e\n! true\nrest\n");
    errexit_in_the_shebang = script(b"#!/bin/bash -e\n! true\necho ok\n");
    noglob_in_the_shebang = script(b"#!/bin/bash -f\nrm *\nls *.txt\n");
    carriage_returns = script(b"#!/bin/sh\necho hi\r\necho there\r\n");
    crlf_heredoc_terminator = script(b"#!/bin/sh\ncat <<EOF\r\nbody\r\nEOF\r\necho $x\r\n");
    leading_byte_order_mark = script(b"\xef\xbb\xbf#!/bin/sh\necho hi\n");
    leading_byte_order_mark_without_a_shebang = script(b"\xef\xbb\xbfecho $1\n");
    leading_byte_order_mark_disabled_file_wide = script(b"\xef\xbb\xbf#!/bin/sh\n# shellcheck disable=SC1082\necho hi\n");
    disable_applies_to_parser_notes = script(b"#!/bin/sh\n# shellcheck disable=SC1037\necho \"$12\"\n");
    disable_applies_to_a_parser_note_on_a_nbsp = script(b"#!/bin/sh\n# shellcheck disable=SC1018\necho\xc2\xa0hi\n");
    unterminated_heredoc = script(b"#!/bin/sh\ncat <<EOF\nbody\n");
    extended_analysis_flag_false = Case {
        args: &["--extended-analysis=false", "-f", "json1", "-"],
        ..script(b"#!/bin/sh\nf() { return; echo hi; }\nexit; foo;\n")
    };
    extended_analysis_flag_beats_the_directive = Case {
        args: &["--extended-analysis=true", "-f", "json1", "-"],
        ..script(b"#!/bin/sh\n# shellcheck extended-analysis=false\nf() { return; echo hi; }\n")
    };
    first_extended_analysis_directive_wins = script(b"#!/bin/sh\n# shellcheck extended-analysis=false\n# shellcheck extended-analysis=true\nexit; foo;\n");
    extended_analysis_directive_false = script(b"#!/bin/sh\n# shellcheck extended-analysis=false\nf() { return; echo hi; }\n");
    extended_analysis_bad_value = script(b"# shellcheck extended-analysis=tru\ntrue\n");
    linefeed_in_single_bracket_test = script(b"#!/bin/sh\n[ \n foo ]\n");
    linefeed_before_single_bracket_close = script(b"#!/bin/sh\n[ foo = bar\n]\n");
    external_sources_directive_in_a_script = script(b"#!/bin/sh\n# shellcheck external-sources=true\necho hi\n");
    no_analysis_after_an_unterminated_quote = script(b"#!/bin/sh\necho $foo; echo \"");
    no_analysis_after_a_stray_paren = script(b"#!/bin/sh\necho \"$x\"; )\n");
    no_analysis_after_a_paren_line = script(b"#!/bin/sh\necho $x\n)\n");
    no_analysis_after_an_unfinished_if = script(b"#!/bin/sh\necho $foo\nif true\n");
    associative_index_with_spaces = script(b"#!/bin/bash\ndeclare -A a; a[foo $bar]=x\n");
    index_parser_notes_are_kept = script(b"#!/bin/bash\na[1 -lt 2]=x\n");
    index_parser_problems_are_kept = script(b"#!/bin/bash\na[(1]=x\n");
    enable_flag_runs_the_optional_check = Case {
        args: &["--enable=quote-safe-variables", "-f", "json1", "-"],
        ..script(b"#!/bin/bash\nvar=hello; echo $var\n")
    };
    enable_directive_runs_the_optional_check = script(b"#!/bin/bash\n# shellcheck enable=quote-safe-variables\nvar=hello; echo $var\n");
    unterminated_quoted_directive_value = script(b"#!/bin/sh\n# shellcheck shell=\"bash\necho hi\n");
    arithmetic_for_with_a_brace_body = script(b"#!/bin/bash\nfor ((;;)) { true; }\n");
    for_in_with_a_brace_body = script(b"#!/bin/bash\nfor f in a; { echo \"$f\"; }\nfor i in 1 2; { echo $i; }\n");
    reserved_word_prefix_in_a_command_name = script(b"#!/bin/sh\ndo-release-upgrade\n");
    operators_right_after_a_closing_brace = script(b"#!/bin/sh\n{ echo hi; }>output\n{ false; }|true\n");
    directive_without_equals = script(b"#!/bin/sh\n# shellcheck disable SC2086\necho $1\n");
    shebang_bang_hash = script(b"!# /bin/sh\necho hi\n");
    shebang_bang_space = script(b"! /bin/sh\necho hi\n");
    shebang_hash_space = script(b"# /bin/sh\necho hi\n");
    escapes_in_double_quotes = script(b"#!/bin/sh\n[ \"\\$a\" = '$a' ]\nx=\"\\$HOME\"\ncase \"\\$x\" in '$x') :;; esac\necho \"$x\"\n");
    unicode_quotes = script("#!/bin/sh\necho \u{201c}$HOME\u{201d}\necho \u{2018}hi\u{2019}\n".as_bytes());
    sourced_file_with_check_sourced = files(
        &["-x", "-a", "-f", "json1", "main.sh"],
        &[
            ("main.sh", b"#!/bin/sh\n. ./lib.sh\necho \"$v\"\n"),
            ("lib.sh", b"v=$1\necho $v\n"),
        ],
    );
    sourced_file_named_by_a_directive = files(
        &["-x", "-f", "json1", "main.sh"],
        &[
            ("main.sh", b"#!/bin/sh\n# shellcheck source=lib.sh\n. \"$dir/lib.sh\"\necho \"$v\"\n"),
            ("lib.sh", b"v=1\n"),
        ],
    );
    sourced_file_without_external_sources = files(
        &["-f", "json1", "main.sh"],
        &[
            ("main.sh", b"#!/bin/sh\n. ./lib.sh\necho \"$v\"\n"),
            ("lib.sh", b"v=1\n"),
        ],
    );
    shellcheckrc_is_read_by_default = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"disable=SC2086\n"), ("x.sh", b"#!/bin/sh\necho $1\n")],
    );
    ansi_c_strings_are_decoded = script(b"#!/bin/bash\necho $'\\x65cho' *\nprintf $'\\x25s' value\n");
    quoted_brace_inside_a_parameter_expansion = script(b"#!/bin/bash\necho \"${x:-'}'}\"\necho \"${foo#\\}}\"\n");
    heredoc_delimiter_with_a_plus = script(b"#!/bin/sh\ncat <<END+TAG\nbody\nEND+TAG\necho $x\n");
    unterminated_quote_after_a_literal = script(b"#!/bin/sh\necho prefix'unterminated\n");
    bang_joined_to_its_command = script(b"#!/bin/sh\n!cat file\n");
    if_without_then = script(b"#!/bin/sh\nif true\n");
    brace_expansion_in_sh = script(b"#!/bin/sh\necho {a,b}\n");
    single_bracket_joined_to_its_operand = script(b"#!/bin/bash\n[foo ]\n");
    double_bracket_joined_to_its_operand = script(b"#!/bin/bash\n[[foo ]]\n");
    apostrophe_closes_a_single_quote = script(b"#!/bin/sh\necho 'it's'\n");
    extglob_with_spaces = script(b"#!/bin/bash\nshopt -s extglob\nls +(foo \\) bar)\n");
    cp_ln_and_sudo_arguments = script(b"#!/bin/sh\ncp source\nln source\nsudo cd /root\n");
    unsupported_interpreter = script(b"#!/usr/bin/python\ntrue $1\n");
    env_with_a_flag_in_the_shebang = script(b"#!/usr/bin/env -i bash\necho hi\n");
    double_bracket_closed_by_single = script(b"#!/bin/bash\n[[ x ]\n");
    single_bracket_closed_by_double = script(b"#!/bin/bash\n[ x ]]\n");
    comment_ending_in_a_backslash_after_a_continuation = script(b"#!/bin/sh\necho foo \\\n # this does not continue \\\necho bar\n");
    quoted_literal_with_spaces_in_a_for_loop = script(b"#!/bin/sh\nfor f in \"literal with spaces\"; do echo \"$f\"; done\n");
    an_unreadable_input_among_others = Case {
        unreadable: &["b.sh"],
        ..files(
            &["-f", "json1", "a.sh", "b.sh", "c.sh"],
            &[
                ("a.sh", b"#!/bin/sh\necho $1\n"),
                ("b.sh", b"#!/bin/sh\necho $3\n"),
                ("c.sh", b"#!/bin/sh\necho $2\n"),
            ],
        )
    };
    latin1_bytes_in_a_script = script(b"#!/bin/sh\n# caf\xe9\necho \"\xe9\" $1\n");
    shellcheckrc_key_without_equals = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"disable SC2086\n"), ("x.sh", b"#!/bin/sh\necho $1\n")],
    );
    shellcheckrc_quoted_values = files(
        &["-f", "json1", "x.sh"],
        &[
            (".shellcheckrc", b"disable='SC2086,SC2181'\nshell=\"bash\"\n"),
            ("x.sh", b"echo $1 $'x'\nfalse; [ $? = 0 ]\n"),
        ],
    );
    stdin_named_twice = Case {
        args: &["-f", "json1", "-", "-"],
        ..script(b"#!/bin/sh\necho $1\n")
    };
    shellcheckrc_first_shell_wins = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"shell=sh\nshell=bash\n"), ("x.sh", b"echo $'x'\n")],
    );
    shellcheckrc_unreadable_stops_the_search = Case {
        unreadable: &["sub/.shellcheckrc"],
        ..files(
            &["-f", "json1", "sub/x.sh"],
            &[
                (".shellcheckrc", b"disable=SC2086\n"),
                ("sub/.shellcheckrc", b"disable=SC2154\n"),
                ("sub/x.sh", b"#!/bin/sh\necho $x\n"),
            ],
        )
    };
    shell_ash = Case { args: &["--shell=ash", "-f", "json1", "-"], ..script(b"echo $'x' $1\n") };
    shell_bats = Case { args: &["--shell=bats", "-f", "json1", "-"], ..script(b"echo $'x' $1\n") };
    shell_ksh88 = Case { args: &["--shell=ksh88", "-f", "json1", "-"], ..script(b"echo $'x' $1\n") };
    shell_ksh93 = Case { args: &["--shell=ksh93", "-f", "json1", "-"], ..script(b"echo $'x' $1\n") };
    shell_oksh = Case { args: &["--shell=oksh", "-f", "json1", "-"], ..script(b"echo $'x' $1\n") };
    shellcheckrc_first_extended_analysis_wins = files(
        &["-f", "json1", "x.sh"],
        &[
            (".shellcheckrc", b"extended-analysis=false\nextended-analysis=true\n"),
            ("x.sh", b"#!/bin/sh\nf() { return; echo hi; }\n"),
        ],
    );
    shell_flag_skips_shebang_validation = Case {
        args: &["--shell=bash", "-f", "json1", "-"],
        ..script(b"#!/usr/bin/foo\necho $1\n")
    };
    output_write_failure = Case { full_stdout: true, ..script(b"#!/bin/sh\necho $1\n") };
    shellcheckrc_two_directives_on_a_line = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"disable=SC2086 shell=sh\n"), ("x.sh", b"echo $1 $'x'\n")],
    );
    shellcheckrc_broken = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"rofl\n"), ("x.sh", b"#!/bin/sh\necho $1\n")],
    );
    norc_skips_the_shellcheckrc = files(
        &["--norc", "-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"disable=2086\n"), ("x.sh", b"#!/bin/sh\necho $1\n")],
    );
    shellcheckrc_enables_an_optional_check = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"enable=avoid-nullary-conditions\n"), ("x.sh", b"#!/bin/sh\n[ \"$1\" ]\n")],
    );
    shellcheckrc_disables_an_unsupported_shell = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"disable=1071\n"), ("x.sh", b"#!/bin/zsh\necho $1\n")],
    );
    shellcheckrc_disables_a_malformed_shebang = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"disable=1104\n"), ("x.sh", b"!/bin/bash\necho 'hello world'\n")],
    );
    shellcheckrc_suppresses_dataflow = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"extended-analysis=false\n"), ("x.sh", b"#!/bin/sh\nexit; foo;\n")],
    );
    file_directive_beats_the_shellcheckrc_when_suppressing_dataflow = files(
        &["-f", "json1", "x.sh"],
        &[
            (".shellcheckrc", b"extended-analysis=true\n"),
            ("x.sh", b"#!/bin/sh\n# shellcheck extended-analysis=false\nexit; foo;\n"),
        ],
    );
    file_directive_beats_the_shellcheckrc_when_enabling_dataflow = files(
        &["-f", "json1", "x.sh"],
        &[
            (".shellcheckrc", b"extended-analysis=false\n"),
            ("x.sh", b"#!/bin/sh\n# shellcheck extended-analysis=true\nexit; foo;\n"),
        ],
    );
    flag_beats_the_file_directive_when_enabling_dataflow = files(
        &["--extended-analysis=true", "-f", "json1", "x.sh"],
        &[
            (".shellcheckrc", b"extended-analysis=false\n"),
            ("x.sh", b"#!/bin/sh\n# shellcheck extended-analysis=false\nexit; foo;\n"),
        ],
    );
    flag_beats_the_file_directive_when_suppressing_dataflow = files(
        &["--extended-analysis=false", "-f", "json1", "x.sh"],
        &[
            (".shellcheckrc", b"extended-analysis=true\n"),
            ("x.sh", b"#!/bin/sh\n# shellcheck extended-analysis=true\nexit; foo;\n"),
        ],
    );
    file_shell_directive_beats_the_shellcheckrc = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"shell=bash\n"), ("x.sh", b"# shellcheck shell=sh\necho $'x' $1\n")],
    );
    shellcheckrc_shell_beats_the_shebang = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"shell=bash\n"), ("x.sh", b"#!/bin/sh\necho $'x' $1\n")],
    );
    shellcheckrc_allows_external_sources = files(
        &["-f", "json1", "main.sh"],
        &[
            (".shellcheckrc", b"external-sources=true\n"),
            ("main.sh", b"#!/bin/bash\nsource ./lib.sh\necho \"$v\"\n"),
            ("lib.sh", b"v=$1\n"),
        ],
    );
    file_can_disable_external_sources = files(
        &["-f", "json1", "main.sh"],
        &[
            (".shellcheckrc", b"external-sources=true\n"),
            ("main.sh", b"#!/bin/bash\ntrue\nsource ./a.sh\n# shellcheck external-sources=false\nsource ./b.sh\n"),
            ("a.sh", b"echo $1\n"),
            ("b.sh", b"_=`foo`\n"),
        ],
    );
    file_cannot_enable_external_sources = files(
        &["-f", "json1", "main.sh"],
        &[
            (".shellcheckrc", b"external-sources=false\n"),
            ("main.sh", b"#!/bin/bash\n# shellcheck external-sources=true\nsource ./a.sh\n"),
            ("a.sh", b"true\n"),
        ],
    );
    fuzz_seed_168_backslash_in_a_parameter_expansion = Case {
        args: &["-s", "dash", "-f", "json1", "-"],
        ..script(b"${\\v}")
    };
    heredoc_delimiter_with_a_middle_dot = script("#!/bin/sh\ncat <<E\u{b7}F\nx\nE\u{b7}F\ncat <<\"E\u{b7}F\nx\n".as_bytes());
    directive_after_a_command = script(b"#!/bin/sh\necho hi # shellcheck disable=SC2086\n");
    directive_after_an_argument = script(b"#!/bin/sh\necho $1 # shellcheck disable=SC2086\n");
    source_directive_after_a_command = script(b"#!/bin/sh\necho $1 # shellcheck source=foo\n");
    directive_after_an_assignment = script(b"#!/bin/sh\nfoo=$1 # shellcheck disable=SC2034\necho $foo\n");
    directive_before_a_command = script(b"#!/bin/sh\n# shellcheck disable=SC2086\necho $1\n");
    directive_text_in_double_quotes = script(b"#!/bin/sh\necho \"# shellcheck disable=SC2086\" $1\n");
    directive_text_in_single_quotes = script(b"#!/bin/sh\necho '# shellcheck disable=SC2086' $1\n");
    directive_text_in_a_heredoc = script(b"#!/bin/sh\ncat <<EOF\n# shellcheck disable=SC2086\nEOF\necho $1\n");
    directive_text_inside_an_ordinary_comment = script(b"#!/bin/sh\n# not a directive # shellcheck disable=SC2086\necho $1\n");
    directive_after_then = script(b"#!/bin/sh\nif true; then # shellcheck disable=SC2086\n  echo $1\nfi\n");
    directive_after_a_function_brace = script(b"#!/bin/sh\nfoo() { # shellcheck disable=SC2086\n  echo $1\n}\n");
    directive_after_case_in = script(b"#!/bin/sh\ncase $1 in # shellcheck disable=SC2086\n  *) echo $1;;\nesac\n");
    directive_before_a_case_item = script(b"#!/bin/sh\ncase $1 in\n  # shellcheck disable=SC2086\n  *) echo $1;;\nesac\n");
    directive_after_a_semicolon = script(b"#!/bin/sh\necho $1; # shellcheck disable=SC2086\n");
    directive_after_and = script(b"#!/bin/sh\necho $1 &&  # shellcheck disable=SC2086\n  echo $2\n");
    directive_after_a_pipe = script(b"#!/bin/sh\necho $1 | # shellcheck disable=SC2086\n  cat\n");
    directive_after_a_line_continuation = script(b"#!/bin/sh\necho $1 \\\n # shellcheck disable=SC2086\n");
    directive_in_an_array = script(b"#!/bin/bash\nx=( # shellcheck disable=SC2086\n)\n");
    directive_without_a_space = script(b"#!/bin/sh\necho $1 #shellcheck disable=SC2086\n");
    directive_capitalized = script(b"#!/bin/sh\necho $1 # ShellCheck disable=SC2086\n");
    directive_with_no_body = script(b"#!/bin/sh\necho $1 # shellcheck\n");
    directive_prefix_of_a_longer_word = script(b"#!/bin/sh\necho $1 # shellcheckx disable=SC2086\n");
    two_trailing_directives = script(b"#!/bin/sh\ntrue # shellcheck disable=SC2086\ntrue # shellcheck disable=SC2034\n");
    directive_after_for_in_words = script(b"#!/bin/sh\nfor x in a b # shellcheck disable=SC2086\ndo echo $x; done\n");
    directive_after_for_in = script(b"#!/bin/sh\nfor x in # shellcheck disable=SC2086\ndo echo $x; done\n");
    directive_after_select_in = script(b"#!/bin/bash\nselect x in a # shellcheck disable=SC2086\ndo echo $x; done\n");
    directive_after_let = script(b"#!/bin/bash\nlet x=1 # shellcheck disable=SC2034\n");
    directive_after_a_redirection = script(b"#!/bin/sh\necho $1 >/dev/null # shellcheck disable=SC2086\n");
    directive_glued_to_a_redirection = script(b"#!/bin/sh\necho $1 2>&1# shellcheck disable=SC2086\n");
    directive_after_builtin = script(b"#!/bin/bash\nbuiltin # shellcheck disable=SC2086\n");
    directive_after_eval = script(b"#!/bin/sh\neval $1 # shellcheck disable=SC2086\n");
    directive_after_export = script(b"#!/bin/sh\nexport x=$1 # shellcheck disable=SC2086\n");
    directive_after_time = script(b"#!/bin/bash\ntime # shellcheck disable=SC2086\n");
    shellcheckrc_huge_disable_range = files(
        &["-f", "json1", "x.sh"],
        &[(".shellcheckrc", b"disable=SC1000-SC1000000000\n"), ("x.sh", b"#!/bin/sh\necho $1\n")],
    );
}
