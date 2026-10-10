//! ShellCheck CLI (Rust port). Reads scripts from files or stdin, runs the
//! analyzer core, and emits the requested format.
//!
//! Option parsing lives in `shellcheck_cli::options` and mirrors the Haskell
//! `shellcheck.hs` driver (option set, `getOpt Permute` semantics, exit codes).
//! Output formatting mirrors `ShellCheck.Formatter.*`: tty (default), gcc,
//! checkstyle, json, json1, quiet, and diff.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::io::{IsTerminal, Read, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::rc::Rc;

use shellcheck_cli::formatter::{self, checkstyle, diff, fixer, gcc, json, json1, tty};
use shellcheck_cli::options::{self, Outcome, RunConfig};
use shellcheck_cli::paths::{combine, drop_file_name, io_error_message, normalize_path};
use shellcheck_cli::rc::{self, ConfigLookup};
use shellcheck_rs::cfg::InternalError;
use shellcheck_rs::interface::{
    CheckSpec, ErrorMessage, PositionedComment, RSC_DATAFLOW_SKIPPED, System, decode_bytes,
};

fn main() -> ExitCode {
    // SHELLCHECK_OPTS is split on whitespace (Haskell `words`) and prepended to
    // argv before parsing, so env-configured defaults apply but explicit argv
    // can still override them (shellcheck.hs `getOptions`: env ++ args).
    let mut argv: Vec<std::ffi::OsString> = Vec::new();
    if let Ok(opts) = std::env::var("SHELLCHECK_OPTS") {
        argv.extend(opts.split_whitespace().map(std::ffi::OsString::from));
    }
    argv.extend(std::env::args_os().skip(1));
    let config = match options::parse_os(&argv, &Path::exists) {
        Outcome::Run(c) => *c,
        Outcome::PrintVersion => {
            println!("{}", options::version_banner());
            return ExitCode::SUCCESS;
        }
        Outcome::PrintHelp => {
            // `println!` adds the trailing blank line the oracle's --help emits
            // after the usage block (usage() itself ends with a single "\n").
            println!("{}", options::usage());
            return ExitCode::SUCCESS;
        }
        Outcome::ListOptional => {
            print!("{}", options::list_optional_text());
            return ExitCode::SUCCESS;
        }
        Outcome::Error { message, code } => {
            eprintln!("{message}");
            return ExitCode::from(code);
        }
    };

    run(config)
}

/// Port of `ioInterface` (shellcheck.hs): the real filesystem, as seen by the
/// parser when it follows a `source`.
///
/// A file may only be read if it was named as an input, unless `-x` (or an rc
/// `external-sources=true`, which arrives as the annotation argument) says
/// otherwise. `-P` and `source-path=` directives say where to look for it, with
/// `SCRIPTDIR` standing for the checked script's own directory.
#[derive(Clone)]
struct IoSystem {
    /// The input filenames, normalized (`inputs <- mapM normalize files`).
    inputs: Rc<HashSet<PathBuf>>,
    /// `externalSources options` (`-x`).
    external_sources: bool,
    /// `sourcePaths options` (`-P`), in flag order.
    source_paths: Vec<String>,
    /// `inputFile`'s cache for inputs that cannot be reopened -- stdin. A
    /// seekable file is re-read instead, exactly as upstream does.
    cache: Rc<RefCell<HashMap<String, String>>>,
    /// Native root input for this analysis. Display names may collide, so
    /// each input and its formatter use their own filesystem view.
    input: Option<PathBuf>,
}

impl IoSystem {
    fn new(config: &RunConfig) -> Self {
        Self {
            inputs: Rc::new(config.inputs.iter().map(|f| normalize_path(f)).collect()),
            external_sources: config.external_sources,
            source_paths: config.source_paths.clone(),
            cache: Rc::new(RefCell::new(HashMap::new())),
            input: None,
        }
    }

    fn for_input(&self, input: &Path) -> Self {
        Self {
            input: Some(input.to_path_buf()),
            ..self.clone()
        }
    }

    fn os_path(&self, file: &str) -> PathBuf {
        if let Some(input) = &self.input {
            if file == input.to_string_lossy() {
                return input.clone();
            }
            // SCRIPTDIR expands in the analyzer's textual interface. Restore
            // the native directory before following or formatting that source.
            if let Some(dir) = input.parent().filter(|dir| dir.to_str().is_none()) {
                let prefix = format!("{}/", dir.to_string_lossy());
                if let Some(relative) = file.strip_prefix(&prefix) {
                    return dir.join(relative);
                }
            }
        }
        PathBuf::from(file)
    }

    /// `allowable`: an external file is readable only when a flag or directive
    /// says so; otherwise it must be one of the inputs.
    fn allowable(&self, external_sources: Option<bool>, file: &str) -> bool {
        if external_sources.unwrap_or(self.external_sources) {
            return true;
        }
        self.inputs.contains(&normalize_path(&self.os_path(file)))
    }
}

impl System for IoSystem {
    fn read_file(
        &self,
        external_sources: Option<bool>,
        file: &str,
    ) -> Result<String, ErrorMessage> {
        if let Some(hit) = self.cache.borrow().get(file) {
            return Ok(hit.clone());
        }
        if !self.allowable(external_sources, file) {
            return Err(shellcheck_rs::interface::not_an_input(
                external_sources,
                file,
            ));
        }
        let (contents, should_cache) = input_file(file, self.os_path(file).as_os_str())?;
        if should_cache {
            self.cache
                .borrow_mut()
                .insert(file.to_string(), contents.clone());
        }
        Ok(contents)
    }

    fn find_source(
        &self,
        current_script: &str,
        external_sources: Option<bool>,
        source_paths: &[String],
        name: &str,
    ) -> String {
        // `findSourceFile`: an absolute name is also looked for relative to the
        // search paths, with its drive (on POSIX, the leading slashes) removed;
        // if nothing is found the original name stands.
        let (_, relative) = split_drive(name);
        let filename = if name.starts_with('/') {
            relative
        } else {
            name
        };
        let scriptdir = drop_file_name(current_script);
        let mut candidates = vec![adjust_path(filename, &scriptdir)];
        for dir in self.source_paths.iter().chain(source_paths.iter()) {
            candidates.push(combine(&adjust_path(dir, &scriptdir), filename));
        }
        for candidate in candidates {
            if self.allowable(external_sources, &candidate) && self.os_path(&candidate).is_file() {
                return candidate;
            }
        }
        name.to_string()
    }
}

/// `inputFile`: the contents, plus whether they must be cached because the
/// input cannot be reopened (stdin).
fn input_file(file: &str, path: &std::ffi::OsStr) -> Result<(String, bool), ErrorMessage> {
    // Upstream reads bytes (`openBinaryFile`/`hGetContents`) and decodes them
    // with `decodeString`, which falls back to ISO-8859-1 for anything that is
    // not valid UTF-8. Reading into a `String` directly would instead reject the
    // file, so read bytes and decode them the same way.
    if file == "-" {
        let mut bytes = Vec::new();
        std::io::stdin()
            .read_to_end(&mut bytes)
            .map_err(|e| io_error_message(file, &e))?;
        return Ok((decode_bytes(&bytes), true));
    }
    match std::fs::read(path) {
        Ok(bytes) => Ok((decode_bytes(&bytes), false)),
        Err(e) => Err(io_error_message(file, &e)),
    }
}

/// `System.FilePath.Posix.splitDrive`: the leading run of slashes, then the rest.
fn split_drive(path: &str) -> (&str, &str) {
    let n = path.len() - path.trim_start_matches('/').len();
    path.split_at(n)
}

/// `adjustPath`: a leading `SCRIPTDIR` component becomes the script's directory.
fn adjust_path(path: &str, scriptdir: &str) -> String {
    match path.strip_prefix("SCRIPTDIR") {
        Some("") => scriptdir.to_string(),
        Some(rest) if rest.starts_with('/') => combine(scriptdir, rest.trim_start_matches('/')),
        _ => path.to_string(),
    }
}

/// One loaded input: either its parsed comments (already sorted/filtered), or a
/// read error. The contents are not kept: a formatter re-reads whichever file
/// each comment belongs to, which for a followed `source` is not this input.
struct Loaded {
    name: String,
    sys: Rc<IoSystem>,
    comments: Vec<PositionedComment>,
    /// Why the analysis is incomplete, reported as a read failure is.
    failure: Option<String>,
}

enum Input {
    Ok(Loaded),
    Err { name: String, message: String },
}

impl Input {
    /// The input and the message its format's `onFailure` reports.
    fn failure(&self) -> Option<(&str, &str)> {
        match self {
            Self::Ok(l) => l.failure.as_deref().map(|m| (l.name.as_str(), m)),
            Self::Err { name, message } => Some((name, message)),
        }
    }

    fn comments(&self) -> &[PositionedComment] {
        match self {
            Self::Ok(l) => &l.comments,
            Self::Err { .. } => &[],
        }
    }
    /// What makes quiet mode exit 1.
    fn is_problem(&self) -> bool {
        self.failure().is_some() || !self.comments().is_empty()
    }
}

/// `statusToCode` of the inputs' combined status: a failure is a
/// `RuntimeException` (2), an `.editorconfig` SC1134 a `SupportFailure` (4),
/// and any other comment `SomeProblems` (1).
fn exit_status(loaded: &[Input]) -> u8 {
    if loaded.iter().any(|i| i.failure().is_some()) {
        2
    } else if loaded
        .iter()
        .any(|i| i.comments().iter().any(is_editor_config_error))
    {
        4
    } else {
        u8::from(loaded.iter().any(|i| !i.comments().is_empty()))
    }
}

/// `RSC1001`: the message for a check whose dataflow analysis stopped.
fn dataflow_failure(InternalError(what): InternalError) -> String {
    format!(
        "{RSC_DATAFLOW_SKIPPED}: ShellCheck internal error, please report: {what}. \
         The checks that need dataflow analysis were skipped."
    )
}

/// Load one input, reading it through the system interface exactly as `process`
/// does (`siReadFile sys Nothing filename`), so that the stdin cache and the
/// error wording are the same ones a sourced file gets. Reading is lazy: stdin
/// is only touched when a `-` input is actually reached, preserving quiet-mode's
/// short-circuit (it must not block on stdin after an earlier file failed).
/// The configuration is only looked up for an input that was read.
fn load(
    path: &Path,
    spec_template: &CheckSpec,
    config: Option<&ConfigLookup>,
    sys: &Rc<IoSystem>,
) -> Input {
    let sys = Rc::new(sys.for_input(path));
    let name = path.to_string_lossy();
    let name = name.as_ref();
    let contents = match sys.read_file(None, name) {
        Ok(s) => s,
        Err(message) => {
            return Input::Err {
                name: name.to_string(),
                message,
            };
        }
    };
    let mut spec = CheckSpec {
        filename: name.to_string(),
        script: contents,
        ..spec_template.clone()
    };
    // Merge rc directives into the per-input `CheckSpec`; see `rc::merge_into`,
    // which holds the rules (CLI flags win over rc where they conflict).
    if let Some(rc) = config.and_then(|c| c.get(name)) {
        rc::merge_into(&mut spec, &rc);
    }
    let sys_dyn = Rc::clone(&sys) as Rc<dyn System>;
    let result = shellcheck_rs::checker::check_script_with(sys_dyn, &spec);
    Input::Ok(Loaded {
        name: name.to_string(),
        sys,
        comments: result.comments,
        failure: result.dataflow_error.map(dataflow_failure),
    })
}

/// `NE.groupWith sourceFile`: split the comments into runs that share a start
/// file. They are already sorted by file, so adjacent grouping is enough -- and
/// a sourced file's comments come out under its own name, not the input's.
fn file_groups(comments: &[PositionedComment]) -> Vec<(String, Vec<PositionedComment>)> {
    let mut out: Vec<(String, Vec<PositionedComment>)> = Vec::new();
    for c in comments {
        match out.last_mut() {
            Some((file, group)) if *file == c.start.file => group.push(c.clone()),
            _ => out.push((c.start.file.clone(), vec![c.clone()])),
        }
    }
    out
}

/// The contents a formatter realigns tabs against: `siReadFile sys (Just True)`,
/// i.e. read regardless of `-x`, and an unreadable file counts as empty.
fn group_contents(sys: &Rc<IoSystem>, file: &str) -> String {
    sys.read_file(Some(true), file).unwrap_or_default()
}

/// `editorConfigError`: an SC1134 for an `.editorconfig`, which makes the run a
/// `SupportFailure`. A malformed EditorConfig (invalid `root` or
/// `shellcheck.*` directive) means shellcheck cannot apply the requested
/// configuration, so it fails rather than silently proceeding.
fn is_editor_config_error(comment: &PositionedComment) -> bool {
    comment.comment.code == 1134 && comment.start.file.ends_with(".editorconfig")
}

fn run(config: RunConfig) -> ExitCode {
    let sys = Rc::new(IoSystem::new(&config));
    let RunConfig {
        format,
        inputs,
        spec_template,
        color,
        wiki_link_count,
        rcfile,
        source_paths: _,
        external_sources: _,
    } = config;

    // Resolve the configuration policy up front (mirrors `getConfig`):
    //   * `--norc` (ignore_rc): never use any rc or EditorConfig file
    //     (`readConfigFile`'s `ignoreRC`).
    //   * `--rcfile <path>`: read exactly that file once, applied to every
    //     input; if unreadable, warn once and proceed with no rc config.
    //   * otherwise: discover `.shellcheckrc` per input by walking up from the
    //     input's directory (CWD for stdin) and then the user config dirs.
    //   * either way, merge in the input's EditorConfig directives.
    // The lookup runs per input, only once that input has been read.
    let config = (!spec_template.ignore_rc).then(|| ConfigLookup::new(rcfile));

    // Quiet mode is a streaming short-circuit: process inputs in order and exit
    // 1 on the FIRST input that has any comment or fails to read, without
    // loading later inputs (so `-f quiet bad.sh -` never blocks on stdin once
    // bad.sh has a problem). Exit 0 only if every input is clean. This mirrors
    // the Haskell Quiet formatter, which folds inputs lazily and reports the
    // first failing result. A read failure counts as a problem (exit 1), not a
    // runtime error (2), matching the oracle.
    if format == "quiet" {
        for i in &inputs {
            if load(i, &spec_template, config.as_ref(), &sys).is_problem() {
                return ExitCode::from(1);
            }
        }
        return ExitCode::SUCCESS;
    }

    let loaded: Vec<Input> = inputs
        .iter()
        .map(|i| load(i, &spec_template, config.as_ref(), &sys))
        .collect();

    let any_comments = loaded.iter().any(|i| !i.comments().is_empty());

    let is_tty = std::io::stdout().is_terminal();
    let use_color = formatter::should_output_color(color, is_tty);

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let stderr = std::io::stderr();
    let mut err = stderr.lock();

    let written = match format.as_str() {
        "json1" => print_json(json1::render(&json1_comments(&loaded, &mut err)), &mut out),
        "json" => print_json(json::render(&json_comments(&loaded, &mut err)), &mut out),
        "gcc" => {
            write_gcc(&loaded, &mut out, &mut err);
            Ok(())
        }
        "checkstyle" => {
            write_checkstyle(&loaded, &mut out);
            Ok(())
        }
        "diff" => {
            write_diff(&loaded, use_color, any_comments, &mut out, &mut err);
            Ok(())
        }
        _ => {
            write_tty(&loaded, use_color, wiki_link_count, &mut out, &mut err);
            Ok(())
        }
    };
    if let Err(e) = written {
        let _ = writeln!(err, "{e}");
        return ExitCode::from(2);
    }

    ExitCode::from(exit_status(&loaded))
}

/// A json document on its own line.
fn print_json(doc: serde_json::Result<String>, out: &mut impl Write) -> serde_json::Result<()> {
    let _ = writeln!(out, "{}", doc?);
    Ok(())
}

/// The json1 comments: each file group untabbed and prepended, so the output
/// lists the groups in reverse, as the Haskell `IORef` accumulation does.
fn json1_comments(loaded: &[Input], err: &mut impl Write) -> Vec<PositionedComment> {
    let mut all: Vec<PositionedComment> = Vec::new();
    for i in loaded {
        match i {
            Input::Ok(l) => {
                for (file, comments) in file_groups(&l.comments) {
                    let contents = group_contents(&l.sys, &file);
                    let mut new = fixer::make_non_virtual(&comments, &contents);
                    new.extend(std::mem::take(&mut all));
                    all = new;
                }
            }
            Input::Err { .. } => {}
        }
        if let Some((name, message)) = i.failure() {
            let _ = writeln!(err, "{name}: {message}");
        }
    }
    all
}

/// The legacy json comments (matches upstream `collectResult`): the full
/// comment list is prepended once per file group, causing duplicates across
/// multiple files.
fn json_comments(loaded: &[Input], err: &mut impl Write) -> Vec<PositionedComment> {
    let mut all: Vec<PositionedComment> = Vec::new();
    for i in loaded {
        match i {
            Input::Ok(l) => {
                for _ in file_groups(&l.comments) {
                    let mut new = l.comments.clone();
                    new.extend(std::mem::take(&mut all));
                    all = new;
                }
            }
            Input::Err { .. } => {}
        }
        if let Some((name, message)) = i.failure() {
            let _ = writeln!(err, "{name}: {message}");
        }
    }
    all
}

fn write_gcc(loaded: &[Input], out: &mut impl Write, err: &mut impl Write) {
    for i in loaded {
        match i {
            Input::Ok(l) => {
                for (file, comments) in file_groups(&l.comments) {
                    let contents = group_contents(&l.sys, &file);
                    let mut buf = String::new();
                    gcc::render_file(&file, &contents, &comments, &mut buf);
                    let _ = out.write_all(buf.as_bytes());
                }
            }
            Input::Err { .. } => {}
        }
        if let Some((name, message)) = i.failure() {
            let _ = writeln!(err, "{}", gcc::render_failure(name, message));
        }
    }
}

fn write_checkstyle(loaded: &[Input], out: &mut impl Write) {
    let _ = out.write_all(checkstyle::HEADER.as_bytes());
    for i in loaded {
        match i {
            Input::Ok(l) => {
                for (file, comments) in file_groups(&l.comments) {
                    let contents = group_contents(&l.sys, &file);
                    let mut buf = String::new();
                    checkstyle::render_file(&file, &contents, &comments, &mut buf);
                    let _ = out.write_all(buf.as_bytes());
                }
            }
            Input::Err { .. } => {}
        }
        if let Some((name, message)) = i.failure() {
            // CheckStyle onFailure writes to stdout.
            let _ = out.write_all(checkstyle::render_failure(name, message).as_bytes());
        }
    }
    let _ = out.write_all(checkstyle::FOOTER.as_bytes());
}

fn write_diff(
    loaded: &[Input],
    use_color: bool,
    any_comments: bool,
    out: &mut impl Write,
    err: &mut impl Write,
) {
    let color_fn = |s: &str| diff::color_bold_red(use_color, s);
    let mut reported = false;
    // Rendered per file in input order (matches the Haskell driver fold over inputs).
    for i in loaded {
        match i {
            Input::Ok(l) => {
                for (file, comments) in file_groups(&l.comments) {
                    let contents = group_contents(&l.sys, &file);
                    let d = diff::render_file(use_color, &file, &contents, &comments);
                    if d.reported {
                        let _ = out.write_all(d.text.as_bytes());
                        reported = true;
                    }
                }
            }
            Input::Err { .. } => {}
        }
        if let Some((name, message)) = i.failure() {
            let _ = writeln!(err, "{}", color_fn(&format!("{name}: {message}")));
        }
    }
    if any_comments && !reported {
        let _ = writeln!(err, "{}", color_fn(diff::NONE_FIXABLE_MSG));
    }
}

fn write_tty(
    loaded: &[Input],
    use_color: bool,
    wiki_link_count: usize,
    out: &mut impl Write,
    err: &mut impl Write,
) {
    let color_func = formatter::tty_color_func(use_color);
    let mut wiki: Vec<tty::WikiEntry> = Vec::new();
    for i in loaded {
        match i {
            Input::Ok(l) => {
                // Processes the full result (see `appendComments`) before rendering file groups to keep the wiki summary in result order.
                for (file, comments) in file_groups(&l.comments) {
                    let contents = group_contents(&l.sys, &file);
                    let mut buf = String::new();
                    tty::render_file(
                        &color_func,
                        &file,
                        &contents,
                        &comments,
                        &mut wiki,
                        &mut buf,
                    );
                    let _ = out.write_all(buf.as_bytes());
                }
            }
            Input::Err { .. } => {}
        }
        if let Some((name, message)) = i.failure() {
            let _ = writeln!(
                err,
                "{}",
                color_func("error", &format!("{name}: {message}"))
            );
        }
    }
    let mut wbuf = String::new();
    tty::render_wiki(&wiki, wiki_link_count, &mut wbuf);
    let _ = out.write_all(wbuf.as_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;
    use shellcheck_rs::interface::{Comment, Position, Severity};

    fn comment_in(file: &str, line: i64) -> PositionedComment {
        let pos = Position {
            file: file.to_string(),
            line,
            column: 1,
        };
        PositionedComment {
            start: pos.clone(),
            end: pos,
            comment: Comment {
                severity: Severity::InfoC,
                code: 2086,
                message: String::new(),
            },
            fix: None,
        }
    }

    #[test]
    fn file_groups_splits_adjacent_runs() {
        // Groups pre-sorted comments by source file, matching `NE.groupWith sourceFile`.
        let comments = vec![
            comment_in("./lib.sh", 1),
            comment_in("./lib.sh", 2),
            comment_in("main.sh", 3),
        ];
        let groups = file_groups(&comments);
        assert_eq!(groups.len(), 2);
        assert_eq!(groups[0].0, "./lib.sh");
        assert_eq!(groups[0].1.len(), 2);
        assert_eq!(groups[1].0, "main.sh");
        assert_eq!(
            file_groups(&[]),
            [] as [(
                std::string::String,
                std::vec::Vec<shellcheck_rs::PositionedComment>
            ); 0]
        );
    }

    #[test]
    fn adjust_path_expands_scriptdir() {
        assert_eq!(adjust_path("SCRIPTDIR/inc", "./"), "./inc");
        assert_eq!(adjust_path("SCRIPTDIR", "dir/"), "dir/");
        assert_eq!(adjust_path("SCRIPTDIR/a/b", "dir/"), "dir/a/b");
        // Only a leading component counts, and only the whole word.
        assert_eq!(adjust_path("x/SCRIPTDIR", "dir/"), "x/SCRIPTDIR");
        assert_eq!(adjust_path("SCRIPTDIRish", "dir/"), "SCRIPTDIRish");
        assert_eq!(adjust_path("inc", "dir/"), "inc");
    }

    #[test]
    fn split_drive_takes_the_leading_slashes() {
        assert_eq!(split_drive("/a/b"), ("/", "a/b"));
        assert_eq!(split_drive("//a"), ("//", "a"));
        assert_eq!(split_drive("a/b"), ("", "a/b"));
    }

    #[test]
    fn an_input_is_readable_but_an_unnamed_sibling_is_not() {
        // `allowable`: the inputs are readable whatever the flags say; anything
        // else needs -x or an `external-sources` directive.
        let sys = IoSystem {
            inputs: Rc::new(HashSet::from([normalize_path(Path::new("Cargo.toml"))])),
            external_sources: false,
            source_paths: Vec::new(),
            cache: Rc::new(RefCell::new(HashMap::new())),
            input: None,
        };
        assert!(sys.allowable(None, "Cargo.toml"));
        assert!(sys.allowable(None, "./Cargo.toml"));
        assert!(!sys.allowable(None, "Cargo.lock"));
        assert!(sys.allowable(Some(true), "Cargo.lock"));
        assert_eq!(
            sys.read_file(None, "Cargo.lock").unwrap_err(),
            "Cargo.lock was not specified as input (see shellcheck -x)."
        );
        assert_eq!(
            sys.read_file(Some(false), "Cargo.lock").unwrap_err(),
            "Cargo.lock was not specified as input, and external files were disabled via directive."
        );
        // An input that is not there at all still reports the read failure.
        let sys = IoSystem {
            inputs: Rc::new(HashSet::from([normalize_path(Path::new("nope.sh"))])),
            external_sources: false,
            source_paths: Vec::new(),
            cache: Rc::new(RefCell::new(HashMap::new())),
            input: None,
        };
        assert_eq!(
            sys.read_file(None, "nope.sh").unwrap_err(),
            "nope.sh: openBinaryFile: does not exist (No such file or directory)"
        );
    }

    #[test]
    fn a_file_that_is_not_valid_utf8_is_read_and_not_rejected() {
        // `inputFile` opens in binary mode and runs the bytes through
        // `decodeString`, so a stray byte is analysable text, not a fatal
        // "invalid byte sequence". The bytes after it keep their columns.
        let path = std::env::temp_dir().join("rshellcheck-decode-test.sh");
        std::fs::write(&path, b"#!/bin/sh\necho \xff\xfe $u\n").unwrap();
        let name = path.to_str().unwrap().to_string();
        let sys = IoSystem {
            inputs: Rc::new(HashSet::from([normalize_path(Path::new(&name))])),
            external_sources: false,
            source_paths: Vec::new(),
            cache: Rc::new(RefCell::new(HashMap::new())),
            input: None,
        };
        let contents = sys.read_file(None, &name).unwrap();
        assert_eq!(contents, "#!/bin/sh\necho \u{ff}\u{fe} $u\n");
        // Column of `$u` on line 2: 1-based, counting characters.
        let line = contents.lines().nth(1).unwrap();
        assert_eq!(line.chars().position(|c| c == '$').unwrap() + 1, 9);
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn find_source_searches_the_paths_and_falls_back_to_the_name() {
        // This crate's own directory, so the lookups do not depend on the
        // working directory the test happens to run in.
        let dir = env!("CARGO_MANIFEST_DIR");
        let sys = IoSystem {
            inputs: Rc::new(HashSet::new()),
            external_sources: true,
            source_paths: vec!["SCRIPTDIR/src".to_string()],
            cache: Rc::new(RefCell::new(HashMap::new())),
            input: None,
        };
        // SCRIPTDIR is the checked script's directory, not the sourcing file's.
        assert_eq!(
            sys.find_source(&format!("{dir}/x.sh"), None, &[], "options.rs"),
            format!("{dir}/src/options.rs")
        );
        // An annotation path is searched too, after the flag paths.
        let no_flags = IoSystem {
            inputs: Rc::new(HashSet::new()),
            external_sources: true,
            source_paths: Vec::new(),
            cache: Rc::new(RefCell::new(HashMap::new())),
            input: None,
        };
        assert_eq!(
            no_flags.find_source("x.sh", None, &[format!("{dir}/src")], "rc.rs"),
            format!("{dir}/src/rc.rs")
        );
        // An absolute name has its leading slash dropped before the search, and
        // if that finds nothing the original name stands.
        assert_eq!(
            sys.find_source(&format!("{dir}/x.sh"), None, &[], "/options.rs"),
            format!("{dir}/src/options.rs")
        );
        // Nothing found: the name stands, so the read error names it.
        assert_eq!(
            sys.find_source("x.sh", None, &[], "no/such/file"),
            "no/such/file"
        );
    }

    fn injected() -> Vec<Input> {
        let failure = Some(dataflow_failure(InternalError("Missing root")));
        vec![
            Input::Ok(Loaded {
                name: "a.sh".to_string(),
                sys: no_sources(),
                comments: vec![comment_in("a.sh", 2)],
                failure: failure.clone(),
            }),
            Input::Ok(Loaded {
                name: "b.sh".to_string(),
                sys: no_sources(),
                comments: Vec::new(),
                failure: None,
            }),
            Input::Ok(Loaded {
                name: "c.sh".to_string(),
                sys: no_sources(),
                comments: Vec::new(),
                failure,
            }),
        ]
    }

    fn no_sources() -> Rc<IoSystem> {
        Rc::new(IoSystem {
            inputs: Rc::new(HashSet::new()),
            external_sources: false,
            source_paths: Vec::new(),
            cache: Rc::new(RefCell::new(HashMap::new())),
            input: None,
        })
    }

    const MESSAGE: &str = "RSC1001: ShellCheck internal error, please report: Missing root. \
                           The checks that need dataflow analysis were skipped.";

    fn text(bytes: Vec<u8>) -> String {
        String::from_utf8(bytes).unwrap_or_else(|e| panic!("{e}"))
    }

    #[test]
    fn an_incomplete_analysis_exits_2_even_with_no_comments_left() {
        let loaded = injected();
        assert_eq!(exit_status(&loaded), 2);
        assert_eq!(exit_status(&loaded[1..]), 2);
        assert_eq!(exit_status(&loaded[1..2]), 0);
        assert!(loaded[2].is_problem());
        assert!(!loaded[1].is_problem());
    }

    #[test]
    fn json1_keeps_numeric_codes_and_reports_the_failure_on_stderr() {
        let mut err = Vec::new();
        let doc =
            json1::render(&json1_comments(&injected(), &mut err)).unwrap_or_else(|e| panic!("{e}"));
        let value: serde_json::Value = serde_json::from_str(&doc).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(value["comments"][0]["code"], serde_json::json!(2086));
        assert!(!doc.contains("RSC"), "{doc}");
        assert_eq!(text(err), format!("a.sh: {MESSAGE}\nc.sh: {MESSAGE}\n"));

        let mut err = Vec::new();
        let doc =
            json::render(&json_comments(&injected(), &mut err)).unwrap_or_else(|e| panic!("{e}"));
        assert!(!doc.contains("RSC"), "{doc}");
        assert_eq!(text(err), format!("a.sh: {MESSAGE}\nc.sh: {MESSAGE}\n"));
    }

    #[test]
    fn every_other_format_reports_the_failure_as_it_reports_a_read_failure() {
        let (mut out, mut err) = (Vec::new(), Vec::new());
        write_gcc(&injected(), &mut out, &mut err);
        assert_eq!(
            text(err),
            format!(
                "{}\n{}\n",
                gcc::render_failure("a.sh", MESSAGE),
                gcc::render_failure("c.sh", MESSAGE)
            )
        );
        assert!(text(out).contains("[SC2086]"));

        let mut out = Vec::new();
        write_checkstyle(&injected(), &mut out);
        let out = text(out);
        assert!(
            out.contains(&checkstyle::render_failure("a.sh", MESSAGE)),
            "{out}"
        );
        assert!(
            out.contains(&checkstyle::render_failure("c.sh", MESSAGE)),
            "{out}"
        );

        let (mut out, mut err) = (Vec::new(), Vec::new());
        write_tty(&injected(), false, 3, &mut out, &mut err);
        assert_eq!(text(err), format!("a.sh: {MESSAGE}\nc.sh: {MESSAGE}\n"));
        assert!(text(out).contains("SC2086"));

        let (mut out, mut err) = (Vec::new(), Vec::new());
        write_diff(&injected(), false, true, &mut out, &mut err);
        assert!(text(err).starts_with(&format!("a.sh: {MESSAGE}\nc.sh: {MESSAGE}\n")));
    }
}
