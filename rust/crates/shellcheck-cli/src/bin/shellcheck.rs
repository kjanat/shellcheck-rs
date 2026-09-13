//! ShellCheck CLI (Rust port). Reads scripts from files or stdin, runs the
//! analyzer core, and emits the requested format.
//!
//! Option parsing lives in `shellcheck_cli::options` and mirrors the Haskell
//! `shellcheck.hs` driver (option set, `getOpt Permute` semantics, exit codes).
//! Output formatting mirrors `ShellCheck.Formatter.*`: tty (default), gcc,
//! checkstyle, json, json1, quiet, and diff.

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{IsTerminal, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;
use std::rc::Rc;

use shellcheck_cli::formatter::{self, checkstyle, diff, fixer, gcc, json, json1, tty};
use shellcheck_cli::options::{self, Outcome, RunConfig};
use shellcheck_cli::rc::{self, RcConfig};
use shellcheck_rs::interface::{
    CheckSpec, ErrorMessage, PositionedComment, SystemInterface, decode_bytes,
};

fn main() -> ExitCode {
    // SHELLCHECK_OPTS is split on whitespace (Haskell `words`) and prepended to
    // argv before parsing, so env-configured defaults apply but explicit argv
    // can still override them (shellcheck.hs `getOptions`: env ++ args).
    let mut argv: Vec<String> = Vec::new();
    if let Ok(opts) = std::env::var("SHELLCHECK_OPTS") {
        argv.extend(opts.split_whitespace().map(|s| s.to_string()));
    }
    // `getArgs` hands Haskell every argument, whatever its bytes; a filename
    // that is not valid UTF-8 is a filename like any other. `std::env::args`
    // panics on one, so take the `OsString`s and keep the originals to open
    // with -- the lossy text is only ever what gets parsed and printed.
    let mut original_args: HashMap<String, std::ffi::OsString> = HashMap::new();
    for arg in std::env::args_os().skip(1) {
        let text = arg.to_string_lossy().into_owned();
        if std::ffi::OsStr::new(&text) != arg {
            original_args.insert(text.clone(), arg);
        }
        argv.push(text);
    }

    let config = match options::parse(&argv) {
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

    run(config, original_args)
}

/// Port of `ioInterface` (shellcheck.hs): the real filesystem, as seen by the
/// parser when it follows a `source`.
///
/// A file may only be read if it was named as an input, unless `-x` (or an rc
/// `external-sources=true`, which arrives as the annotation argument) says
/// otherwise. `-P` and `source-path=` directives say where to look for it, with
/// `SCRIPTDIR` standing for the checked script's own directory.
struct IoSystemInterface {
    /// The input filenames, normalized (`inputs <- mapM normalize files`).
    inputs: Vec<String>,
    /// `externalSources options` (`-x`).
    external_sources: bool,
    /// `sourcePaths options` (`-P`), in flag order.
    source_paths: Vec<String>,
    /// `inputFile`'s cache for inputs that cannot be reopened -- stdin. A
    /// seekable file is re-read instead, exactly as upstream does.
    cache: RefCell<HashMap<String, String>>,
    /// Command line arguments whose bytes are not valid UTF-8, keyed by the
    /// lossy text they are known by everywhere else. Upstream never loses those
    /// bytes (GHC round-trips them through the locale encoding), so opening the
    /// file must use the original and not the lossy name.
    original_args: HashMap<String, std::ffi::OsString>,
}

impl IoSystemInterface {
    fn new(
        config: &RunConfig,
        original_args: HashMap<String, std::ffi::OsString>,
    ) -> IoSystemInterface {
        IoSystemInterface {
            inputs: config.inputs.iter().map(|f| normalize(f)).collect(),
            external_sources: config.external_sources,
            source_paths: config.source_paths.clone(),
            cache: RefCell::new(HashMap::new()),
            original_args,
        }
    }

    /// The bytes to actually open `file` with: the original argument when the
    /// name came from a command line that was not valid UTF-8, else the name.
    fn os_path(&self, file: &str) -> std::ffi::OsString {
        self.original_args
            .get(file)
            .cloned()
            .unwrap_or_else(|| std::ffi::OsString::from(file))
    }

    /// `allowable`: an external file is readable only when a flag or directive
    /// says so; otherwise it must be one of the inputs.
    fn allowable(&self, external_sources: Option<bool>, file: &str) -> bool {
        if external_sources.unwrap_or(self.external_sources) {
            return true;
        }
        self.inputs.contains(&normalize(file))
    }
}

impl SystemInterface for IoSystemInterface {
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
        let (contents, should_cache) = input_file(file, &self.os_path(file))?;
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
            candidates.push(haskell_join(&adjust_path(dir, &scriptdir), filename));
        }
        for candidate in candidates {
            if self.allowable(external_sources, &candidate) && Path::new(&candidate).is_file() {
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

/// `show (ex :: IOException)` for what `openBinaryFile` throws, which is the
/// text that reaches the user after "Not following: " and after a failing
/// input's name.
fn io_error_message(file: &str, e: &std::io::Error) -> ErrorMessage {
    use std::io::ErrorKind;
    let detail = match e.kind() {
        ErrorKind::NotFound => "does not exist (No such file or directory)".to_string(),
        ErrorKind::PermissionDenied => "permission denied (Permission denied)".to_string(),
        ErrorKind::IsADirectory => "inappropriate type (is a directory)".to_string(),
        // `read_to_string` on a directory reports this on some platforms.
        _ if Path::new(file).is_dir() => "inappropriate type (is a directory)".to_string(),
        ErrorKind::InvalidData => "invalid byte sequence".to_string(),
        _ => e.to_string(),
    };
    format!("{file}: openBinaryFile: {detail}")
}

/// `normalize`: `canonicalizePath`, falling back to making the path absolute
/// and removing `.` / `..` lexically when it cannot be resolved.
fn normalize(path: &str) -> String {
    if let Ok(p) = std::fs::canonicalize(path) {
        return p.to_string_lossy().into_owned();
    }
    let mut out = PathBuf::new();
    let joined = if Path::new(path).is_absolute() {
        PathBuf::from(path)
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    };
    for c in joined.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out.to_string_lossy().into_owned()
}

/// `System.FilePath.Posix.splitDrive`: the leading run of slashes, then the rest.
fn split_drive(path: &str) -> (&str, &str) {
    let n = path.len() - path.trim_start_matches('/').len();
    path.split_at(n)
}

/// `dropFileName`: everything up to and including the last separator, or `./`
/// when there is none.
fn drop_file_name(path: &str) -> String {
    match path.rfind('/') {
        Some(i) => path[..=i].to_string(),
        None => "./".to_string(),
    }
}

/// `System.FilePath.combine`.
fn haskell_join(dir: &str, file: &str) -> String {
    if file.starts_with('/') {
        return file.to_string();
    }
    if dir.is_empty() {
        return file.to_string();
    }
    if dir.ends_with('/') {
        format!("{dir}{file}")
    } else {
        format!("{dir}/{file}")
    }
}

/// `adjustPath`: a leading `SCRIPTDIR` component becomes the script's directory.
fn adjust_path(path: &str, scriptdir: &str) -> String {
    match path.strip_prefix("SCRIPTDIR") {
        Some("") => scriptdir.to_string(),
        Some(rest) if rest.starts_with('/') => {
            haskell_join(scriptdir, rest.trim_start_matches('/'))
        }
        _ => path.to_string(),
    }
}

/// One loaded input: either its parsed comments (already sorted/filtered), or a
/// read error. The contents are not kept: a formatter re-reads whichever file
/// each comment belongs to, which for a followed `source` is not this input.
struct Loaded {
    comments: Vec<PositionedComment>,
}

enum Input {
    Ok(Loaded),
    Err { name: String, message: String },
}

/// Load one input, reading it through the system interface exactly as `process`
/// does (`siReadFile sys Nothing filename`), so that the stdin cache and the
/// error wording are the same ones a sourced file gets. Reading is lazy: stdin
/// is only touched when a `-` input is actually reached, preserving quiet-mode's
/// short-circuit (it must not block on stdin after an earlier file failed).
fn load(
    name: &str,
    spec_template: &CheckSpec,
    rc: Option<&RcConfig>,
    sys: &Rc<IoSystemInterface>,
) -> Input {
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
    merge_rc(&mut spec, rc);
    let sys_dyn = Rc::clone(sys) as Rc<dyn SystemInterface>;
    let result = shellcheck_rs::checker::check_script_with(sys_dyn, &spec);
    Input::Ok(Loaded {
        comments: result.comments,
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
fn group_contents(sys: &Rc<IoSystemInterface>, file: &str) -> String {
    sys.read_file(Some(true), file).unwrap_or_default()
}

/// Merge rc directives into the per-input `CheckSpec`; see `rc::merge_into`,
/// which holds the rules (CLI flags win over rc where they conflict).
fn merge_rc(spec: &mut CheckSpec, rc: Option<&RcConfig>) {
    if let Some(rc) = rc {
        rc::merge_into(spec, rc);
    }
}

fn run(config: RunConfig, original_args: HashMap<String, std::ffi::OsString>) -> ExitCode {
    let sys = Rc::new(IoSystemInterface::new(&config, original_args));
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

    // Resolve the rc configuration policy up front (mirrors `getConfig`):
    //   * `--norc` (ignore_rc): never use any rc file.
    //   * `--rcfile <path>`: read exactly that file once, applied to every
    //     input; if unreadable, warn once and proceed with no config.
    //   * otherwise: discover `.shellcheckrc` per input by walking up from the
    //     input's directory (CWD for stdin) and then the user config dirs.
    let ignore_rc = spec_template.ignore_rc;
    let rcfile_config: Option<RcConfig> = if !ignore_rc {
        if let Some(path) = &rcfile {
            match rc::read_config_file(std::path::Path::new(path)) {
                Some(cfg) => Some(cfg),
                None => {
                    eprintln!("Warning: unable to read --rcfile {path}");
                    None
                }
            }
        } else {
            None
        }
    } else {
        None
    };
    // Per-input rc config: fixed rcfile config, directory discovery, or none.
    let resolve_rc = |name: &str| -> Option<RcConfig> {
        if ignore_rc {
            None
        } else if rcfile.is_some() {
            rcfile_config.clone()
        } else {
            rc::discover(name)
        }
    };

    // Quiet mode is a streaming short-circuit: process inputs in order and exit
    // 1 on the FIRST input that has any comment or fails to read, without
    // loading later inputs (so `-f quiet bad.sh -` never blocks on stdin once
    // bad.sh has a problem). Exit 0 only if every input is clean. This mirrors
    // the Haskell Quiet formatter, which folds inputs lazily and reports the
    // first failing result. A read failure counts as a problem (exit 1), not a
    // runtime error (2), matching the oracle.
    if format == "quiet" {
        for i in &inputs {
            let rc = resolve_rc(i);
            match load(i, &spec_template, rc.as_ref(), &sys) {
                Input::Ok(l) if !l.comments.is_empty() => return ExitCode::from(1),
                Input::Ok(_) => {}
                Input::Err { .. } => return ExitCode::from(1),
            }
        }
        return ExitCode::SUCCESS;
    }

    let loaded: Vec<Input> = inputs
        .iter()
        .map(|i| load(i, &spec_template, resolve_rc(i).as_ref(), &sys))
        .collect();

    let any_failure = loaded.iter().any(|i| matches!(i, Input::Err { .. }));
    let any_comments = loaded
        .iter()
        .any(|i| matches!(i, Input::Ok(l) if !l.comments.is_empty()));

    let is_tty = std::io::stdout().is_terminal();
    let use_color = formatter::should_output_color(color, is_tty);

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let stderr = std::io::stderr();
    let mut err = stderr.lock();

    match format.as_str() {
        // "quiet" is handled by the streaming short-circuit above and never
        // reaches this match.
        "json1" => {
            // Untab per file group (makeNonVirtual); each group prepended, so
            // files and groups come out in reverse order of processing, matching
            // the Haskell IORef accumulation.
            let mut all: Vec<PositionedComment> = Vec::new();
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        for (file, comments) in file_groups(&l.comments) {
                            let contents = group_contents(&sys, &file);
                            let mut new = fixer::make_non_virtual(&comments, &contents);
                            new.extend(std::mem::take(&mut all));
                            all = new;
                        }
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(err, "{name}: {message}");
                    }
                }
            }
            let _ = writeln!(out, "{}", json1::render(&all));
        }

        "json" => {
            // Legacy array; no untab, and no grouping either: `collectResult`
            // prepends the *whole* comment list once per file group, so a result
            // spanning two files lists everything twice. Faithful to upstream.
            let mut all: Vec<PositionedComment> = Vec::new();
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        for _ in file_groups(&l.comments) {
                            let mut new = l.comments.clone();
                            new.extend(std::mem::take(&mut all));
                            all = new;
                        }
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(err, "{name}: {message}");
                    }
                }
            }
            let _ = writeln!(out, "{}", json::render(&all));
        }

        "gcc" => {
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        for (file, comments) in file_groups(&l.comments) {
                            let contents = group_contents(&sys, &file);
                            let mut buf = String::new();
                            gcc::render_file(&file, &contents, &comments, &mut buf);
                            let _ = out.write_all(buf.as_bytes());
                        }
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(err, "{}", gcc::render_failure(name, message));
                    }
                }
            }
        }

        "checkstyle" => {
            let _ = out.write_all(checkstyle::HEADER.as_bytes());
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        for (file, comments) in file_groups(&l.comments) {
                            let contents = group_contents(&sys, &file);
                            let mut buf = String::new();
                            checkstyle::render_file(&file, &contents, &comments, &mut buf);
                            let _ = out.write_all(buf.as_bytes());
                        }
                    }
                    Input::Err { name, message } => {
                        // CheckStyle onFailure writes to stdout.
                        let _ = out.write_all(checkstyle::render_failure(name, message).as_bytes());
                    }
                }
            }
            let _ = out.write_all(checkstyle::FOOTER.as_bytes());
        }

        "diff" => {
            let color_fn = |s: &str| diff::color_bold_red(use_color, s);
            let mut reported = false;
            // Rendered per file in input order (the Haskell formatter runs
            // once per file of the fix map as the driver folds over inputs).
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        for (file, comments) in file_groups(&l.comments) {
                            let contents = group_contents(&sys, &file);
                            let d = diff::render_file(use_color, &file, &contents, &comments);
                            if d.reported {
                                let _ = out.write_all(d.text.as_bytes());
                                reported = true;
                            }
                        }
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(err, "{}", color_fn(&format!("{name}: {message}")));
                    }
                }
            }
            if any_comments && !reported {
                let _ = writeln!(err, "{}", color_fn(diff::NONE_FIXABLE_MSG));
            }
        }

        _ => {
            // tty (default).
            let color_func = formatter::tty_color_func(use_color);
            let mut wiki: Vec<tty::WikiEntry> = Vec::new();
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        // `appendComments` runs over the whole result before the
                        // file groups are rendered, so the wiki summary is in
                        // result order rather than group order.
                        for (file, comments) in file_groups(&l.comments) {
                            let contents = group_contents(&sys, &file);
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
                    Input::Err { name, message } => {
                        let _ = writeln!(
                            err,
                            "{}",
                            color_func("error", &format!("{name}: {message}"))
                        );
                    }
                }
            }
            let mut wbuf = String::new();
            tty::render_wiki(&wiki, wiki_link_count, &mut wbuf);
            let _ = out.write_all(wbuf.as_bytes());
        }
    }

    // statusToCode: RuntimeException (2) > SomeProblems (1) > NoProblems (0).
    if any_failure {
        ExitCode::from(2)
    } else if any_comments {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
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
        // `NE.groupWith sourceFile` over comments already sorted by file: a
        // followed source contributes its own group under its own name.
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
        assert!(file_groups(&[]).is_empty());
    }

    #[test]
    fn drop_file_name_matches_haskell() {
        assert_eq!(drop_file_name("psrc.sh"), "./");
        assert_eq!(drop_file_name("dir/myscript"), "dir/");
        assert_eq!(drop_file_name("/abs/script.sh"), "/abs/");
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
    fn haskell_join_follows_combine() {
        assert_eq!(haskell_join("dir", "file"), "dir/file");
        assert_eq!(haskell_join("dir/", "file"), "dir/file");
        assert_eq!(haskell_join("", "file"), "file");
        // An absolute second half wins outright.
        assert_eq!(haskell_join("dir", "/file"), "/file");
    }

    #[test]
    fn split_drive_takes_the_leading_slashes() {
        assert_eq!(split_drive("/a/b"), ("/", "a/b"));
        assert_eq!(split_drive("//a"), ("//", "a"));
        assert_eq!(split_drive("a/b"), ("", "a/b"));
    }

    #[test]
    fn io_error_message_reads_like_the_haskell_exception() {
        let e = std::io::Error::from(std::io::ErrorKind::NotFound);
        assert_eq!(
            io_error_message("./missing.sh", &e),
            "./missing.sh: openBinaryFile: does not exist (No such file or directory)"
        );
        let e = std::io::Error::from(std::io::ErrorKind::PermissionDenied);
        assert_eq!(
            io_error_message("x", &e),
            "x: openBinaryFile: permission denied (Permission denied)"
        );
    }

    #[test]
    fn an_input_is_readable_but_an_unnamed_sibling_is_not() {
        // `allowable`: the inputs are readable whatever the flags say; anything
        // else needs -x or an `external-sources` directive.
        let sys = IoSystemInterface {
            inputs: vec![normalize("Cargo.toml")],
            external_sources: false,
            source_paths: Vec::new(),
            cache: RefCell::new(HashMap::new()),
            original_args: HashMap::new(),
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
        let sys = IoSystemInterface {
            inputs: vec![normalize("nope.sh")],
            external_sources: false,
            source_paths: Vec::new(),
            cache: RefCell::new(HashMap::new()),
            original_args: HashMap::new(),
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
        let sys = IoSystemInterface {
            inputs: vec![normalize(&name)],
            external_sources: false,
            source_paths: Vec::new(),
            cache: RefCell::new(HashMap::new()),
            original_args: HashMap::new(),
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
        let sys = IoSystemInterface {
            inputs: Vec::new(),
            external_sources: true,
            source_paths: vec!["SCRIPTDIR/src".to_string()],
            cache: RefCell::new(HashMap::new()),
            original_args: HashMap::new(),
        };
        // SCRIPTDIR is the checked script's directory, not the sourcing file's.
        assert_eq!(
            sys.find_source(&format!("{dir}/x.sh"), None, &[], "options.rs"),
            format!("{dir}/src/options.rs")
        );
        // An annotation path is searched too, after the flag paths.
        let no_flags = IoSystemInterface {
            inputs: Vec::new(),
            external_sources: true,
            source_paths: Vec::new(),
            cache: RefCell::new(HashMap::new()),
            original_args: HashMap::new(),
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
}
