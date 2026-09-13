//! Port of `ShellCheck.Parser` (recursive descent).
//!
//! The Haskell parser is Parsec-based over a monad-transformer stack carrying an
//! id counter, a `Id -> (start,end)` position map, buffered parse notes, and a
//! pending-here-doc queue. This is a hand-written recursive-descent equivalent:
//!
//! - [`Parser`] holds the input as a `Vec<char>` with an index and running
//!   1-based line/column (tabs advance to the next multiple of 8, matching
//!   Parsec's default `updatePosString`).
//! - Backtracking uses explicit checkpoint/restore of the cursor. Alternatives
//!   backtrack freely (PEG-like); ShellCheck's grammar uses `try` pervasively so
//!   this matches its accepted-input behaviour. Divergences in *error* handling
//!   are refined against the conformance harness.
//! - Node ids are allocated in creation order; each records its `(start,end)`
//!   span into the position map, exactly as `getNextIdBetween`.
//! - Parse *notes* are buffered and dropped if the whole parse fails; parse
//!   *problems* are always emitted. (`ShellCheck.Parser.parseNote` vs
//!   `parseProblem`.)

use crate::ast::*;
use crate::ast_lib;
use crate::interface::{NoExternalSources, Position, Severity, Shell, SystemInterface};
use std::collections::BTreeMap;
use std::rc::Rc;

mod arithmetic;
mod commands;
mod compound;
mod conditions;
mod directives;
#[cfg(test)]
mod tests;
mod words;

/// `ShellCheck.Data.commonCommands` — used by the SC1014 parser note to detect
/// a command mistakenly used as a `[ .. ]`/`[[ .. ]]` test operand.
const COMMON_COMMANDS: &[&str] = &[
    "admin",
    "alias",
    "ar",
    "asa",
    "at",
    "awk",
    "basename",
    "batch",
    "bc",
    "bg",
    "break",
    "c99",
    "cal",
    "cat",
    "cd",
    "cflow",
    "chgrp",
    "chmod",
    "chown",
    "cksum",
    "cmp",
    "colon",
    "comm",
    "command",
    "compress",
    "continue",
    "cp",
    "crontab",
    "csplit",
    "ctags",
    "cut",
    "cxref",
    "date",
    "dd",
    "delta",
    "df",
    "diff",
    "dirname",
    "dot",
    "du",
    "echo",
    "ed",
    "env",
    "eval",
    "ex",
    "exec",
    "exit",
    "expand",
    "export",
    "expr",
    "fc",
    "fg",
    "file",
    "find",
    "fold",
    "fuser",
    "gencat",
    "get",
    "getconf",
    "getopts",
    "gettext",
    "grep",
    "hash",
    "head",
    "iconv",
    "ipcrm",
    "ipcs",
    "jobs",
    "join",
    "kill",
    "lex",
    "link",
    "ln",
    "locale",
    "localedef",
    "logger",
    "logname",
    "lp",
    "ls",
    "m4",
    "mailx",
    "make",
    "man",
    "mesg",
    "mkdir",
    "mkfifo",
    "more",
    "msgfmt",
    "mv",
    "newgrp",
    "ngettext",
    "nice",
    "nl",
    "nm",
    "nohup",
    "od",
    "paste",
    "patch",
    "pathchk",
    "pax",
    "pr",
    "printf",
    "prs",
    "ps",
    "pwd",
    "read",
    "readlink",
    "readonly",
    "realpath",
    "renice",
    "return",
    "rm",
    "rmdel",
    "rmdir",
    "sact",
    "sccs",
    "sed",
    "set",
    "sh",
    "shift",
    "sleep",
    "sort",
    "split",
    "strings",
    "strip",
    "stty",
    "tabs",
    "tail",
    "talk",
    "tee",
    "test",
    "time",
    "timeout",
    "times",
    "touch",
    "tput",
    "tr",
    "trap",
    "tsort",
    "tty",
    "type",
    "ulimit",
    "umask",
    "unalias",
    "uname",
    "uncompress",
    "unexpand",
    "unget",
    "uniq",
    "unlink",
    "unset",
    "uucp",
    "uudecode",
    "uuencode",
    "uustat",
    "uux",
    "val",
    "vi",
    "wait",
    "wc",
    "what",
    "who",
    "write",
    "xargs",
    "xgettext",
    "yacc",
    "zcat",
];

/// A pending parse note/problem (SC1xxx), before id/position resolution.
#[derive(Debug, Clone)]
pub struct ParseNote {
    pub start: Position,
    pub end: Position,
    pub severity: Severity,
    pub code: i64,
    pub message: String,
}

/// Result of parsing a script.
pub struct ParseOutput {
    pub root: Option<Token>,
    pub notes: Vec<ParseNote>,
    pub positions: BTreeMap<Id, (Position, Position)>,
}

/// Cursor snapshot for backtracking.
#[derive(Clone, Copy)]
struct Mark {
    idx: usize,
    line: i64,
    col: i64,
    /// Whether the parse had already committed when the mark was taken, so a
    /// `reset` can tell "we backtracked over a point of no return" from an
    /// ordinary rewind. See [`Parser::backtracked_over_commitment`].
    #[cfg(debug_assertions)]
    committed: bool,
}

type PResult<T> = Result<T, ()>;

struct PendingHereDoc {
    dashed: Dashed,
    quoted: Quoted,
    delim: String,
    // id of the T_HereDoc token to fill in once the body is read
    id: Id,
    /// The context stack as it stood at the `<<`. `readPendingHereDocs` runs
    /// under `swapContext`, so a body that never terminates is reported
    /// against the redirection rather than whatever line it ran into.
    contexts: Vec<Context>,
    /// The annotation/source frames in scope at the `<<`, which in Haskell are
    /// `ContextAnnotation` frames on that same stack -- so a directive in
    /// front of the command covers what its here document reports, even
    /// though the body is read after the command is done.
    ann_contexts: Vec<AnnContext>,
}

/// The frames of Haskell's `contextStack` that carry meaning rather than a
/// production name: `ContextAnnotation [Annotation]` and `ContextSource file`.
///
/// The stack is kept outermost-first (Haskell's is innermost-first, since it
/// pushes to the front), so anything that reads it innermost-first iterates in
/// reverse.
#[derive(Debug, Clone)]
pub(super) enum AnnContext {
    /// `ContextAnnotation`: the directives in front of a command, in the order
    /// they were written.
    Annotations(Vec<Annotation>),
    /// `ContextSource`: a file being read through `source`, by the name
    /// `siFindSource` resolved it to.
    Source(String),
}

pub struct Parser {
    input: Vec<char>,
    idx: usize,
    line: i64,
    col: i64,
    filename: String,
    next_id: i32,
    positions: BTreeMap<Id, (Position, Position)>,
    notes: Vec<ParseNote>,
    problems: Vec<ParseNote>,
    pending_heredocs: Vec<PendingHereDoc>,
    // body text collected for each pending heredoc, keyed by id
    heredoc_bodies: BTreeMap<Id, Vec<Token>>,
    /// The productions currently being parsed, innermost last. Haskell keeps
    /// the same stack as `ContextName pos str` and reports the innermost two
    /// when a parse fails (`notesForContext`).
    contexts: Vec<Context>,
    /// Input index where each *currently* open production began, which
    /// [`Parser::contexts`] no longer tracks now that it keeps failed frames.
    /// A failure past the innermost of these has consumed input, which in
    /// Parsec means `<|>` can no longer recover.
    open_starts: Vec<usize>,
    /// The furthest input index the parser has ever reached. Parsec reports
    /// the error from the furthest failing alternative, not the last one
    /// tried, so failures are ranked by this rather than by the live cursor.
    reach: usize,
    /// The source position of [`Parser::reach`].
    reach_pos: Position,
    /// The deepest failure seen, which is the one a fatal parse reports.
    failure: Option<Failure>,
    /// The `ContextAnnotation` / `ContextSource` frames in scope, outermost
    /// first. Haskell keeps these on the same `contextStack` as the production
    /// names and filters the parse-failure notes with `isIgnored`; on a failed
    /// parse the frames in scope are the ones read before the failure, which is
    /// what this collects.
    ann_contexts: Vec<AnnContext>,
    /// Counter behind `Context::serial`.
    next_serial: u64,
    /// Set when a production gave up after consuming input and no enclosing
    /// alternative could take over. Parsec propagates such a failure straight
    /// out of `readScript`, so the parse is over and no tree survives.
    committed: bool,
    /// Audit for the `try` emulation: `reset` call sites that rewound over a
    /// commitment. See [`Parser::backtracked_over_commitment`].
    #[cfg(debug_assertions)]
    commitment_backtracks: std::collections::BTreeSet<String>,
    /// The context stack as it stood when the parse committed. Parsec stops
    /// dead there, so that is the stack `notesForContext` reads at the end --
    /// whatever this parser goes on to push while it unwinds.
    frozen_contexts: Option<Vec<Context>>,
    /// The dialect the script is being checked as, as far as it is known while
    /// parsing: `--shell` or a file-wide `shell=` directive, else the shebang,
    /// else `None` — which means the same as bash, the dialect ShellCheck
    /// assumes when nothing says otherwise.
    ///
    /// Upstream's parser never asks, because every construct it accepts is
    /// accepted by every shell it supports — with one exception, a `!` with
    /// nothing to negate. See `empty_negation_ok` and `PARITY-NOTES.md`.
    shell_hint: Option<Shell>,
    /// Whether the caller passed `--shell`, which like a `shell=` directive
    /// means the shebang no longer decides anything and is not checked.
    shell_flag_specified: bool,
    /// `Environment.systemInterface`: how a sourced file is resolved and read.
    sys: Rc<dyn SystemInterface>,
    /// `Environment.checkSourced`: whether diagnostics from inside a sourced
    /// file are kept (`-a`).
    check_sourced: bool,
    /// `Environment.currentFilename`: the script the check started from, which
    /// stays put while sourced files are read -- `SCRIPTDIR` is relative to it,
    /// not to whichever file the `source` was written in.
    root_filename: String,
}

/// One open production, mirroring Haskell's `ContextName pos str`.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Context {
    pos: Position,
    name: &'static str,
    /// Identifies this entry into the production, so a frame kept in a
    /// failure snapshot can be told apart from a later one at the same depth.
    serial: u64,
}

/// The deepest parse failure, with the context stack as it stood at the time.
#[derive(Debug, Clone)]
pub(super) struct Failure {
    reach: usize,
    pos: Position,
    message: String,
    /// Haskell reads `contextStack` once, after the parse has given up. This
    /// parser backtracks in places Parsec would not, and those recoveries pop
    /// frames off the top, so the stack is captured with the failure that will
    /// be reported instead of read at the end.
    contexts: Vec<Context>,
    /// True when the failing production had already consumed input. Parsec's
    /// `<|>` only tries the next alternative if the previous one failed
    /// *without* consuming, so such a failure both describes the error better
    /// and, when it came from an explicit `fail`, ends the parse outright.
    consumed: bool,
    /// True when the production failed deliberately (`fail_with`) rather than
    /// being backtracked out of by an enclosing alternative.
    explicit: bool,
}

const DOUBLE_QUOTABLE: &str = "\\\"$`";
const NBSP: char = '\u{A0}';

/// `quotableChars`: the characters a backslash meaningfully escapes outside of
/// quotes. Includes `doubleQuotableChars`.
const QUOTABLE_CHARS: &str = "|&;<>()\\ '\t\n\r\u{A0}\\\"$`";

/// `unicodeDoubleQuotes` / `unicodeSingleQuotes`: the curly quotes an editor
/// substitutes for the real ones, which the shell treats as ordinary text.
/// `bracedQuotable`: what a backslash escapes inside `${..}`.
const BRACED_QUOTABLE: &str = "}\"$`'";

const UNICODE_DOUBLE_QUOTES: &str = "\u{201C}\u{201D}\u{2033}\u{2036}";
const UNICODE_SINGLE_QUOTES: &str = "\u{2018}\u{2019}";

/// `almostSpace`'s character set: the unicode spaces that a shell does *not*
/// treat as whitespace, so a script containing one behaves unexpectedly.
const ALMOST_SPACE_CHARS: &str =
    "\u{A0}\u{2002}\u{2003}\u{2004}\u{2005}\u{2006}\u{2007}\u{2008}\u{2009}\u{200B}\u{202F}";

/// True if `c` terminates a glob character class body (`readClass`'s inner
/// literal run). This is `customEnd ("]") ++ standardEnd` from `readNormalLiteralPart`,
/// where `standardEnd = "[{}" ++ quotableChars ++ extglobStartChars ++ unicodeDoubleQuotes`.
/// `]` is handled by the caller (closes the class); `\` is an escape; `[` and the
/// extglob chars `?*@!+` are accepted as globchars by the caller. What remains here
/// are the pure terminators.
fn is_glob_class_terminator(c: char) -> bool {
    matches!(
        c,
        '{' | '}'
            | '|'
            | '&'
            | ';'
            | '<'
            | '>'
            | '('
            | ')'
            | ' '
            | '\''
            | '\t'
            | '\n'
            | '\r'
            | NBSP
            | '"'
            | '$'
            | '`'
            | '\u{201C}'
            | '\u{201D}'
            | '\u{2033}'
            | '\u{2036}'
    )
}

impl Parser {
    pub fn new(filename: &str, script: &str) -> Parser {
        Parser::with_shell_flag(filename, script, false, None)
    }

    /// `shell_flag_specified` mirrors Haskell's `shellTypeOverride`: `--shell`
    /// suppresses the shebang checks just as a `# shellcheck shell=` directive
    /// does, because the caller has already said what dialect this is.
    /// `shell_hint` is that dialect, when the caller or the filename named one.
    pub fn with_shell_flag(
        filename: &str,
        script: &str,
        shell_flag_specified: bool,
        shell_hint: Option<Shell>,
    ) -> Parser {
        Parser {
            shell_hint,
            shell_flag_specified,
            sys: Rc::new(NoExternalSources),
            check_sourced: false,
            root_filename: filename.to_string(),
            input: script.chars().collect(),
            idx: 0,
            line: 1,
            col: 1,
            filename: filename.to_string(),
            next_id: 0,
            positions: BTreeMap::new(),
            notes: Vec::new(),
            problems: Vec::new(),
            pending_heredocs: Vec::new(),
            heredoc_bodies: BTreeMap::new(),
            contexts: Vec::new(),
            open_starts: Vec::new(),
            ann_contexts: Vec::new(),
            next_serial: 0,
            committed: false,
            #[cfg(debug_assertions)]
            commitment_backtracks: std::collections::BTreeSet::new(),
            frozen_contexts: None,
            reach: 0,
            reach_pos: Position {
                file: filename.to_string(),
                line: 1,
                column: 1,
            },
            failure: None,
        }
    }

    // ---- cursor primitives -------------------------------------------------

    #[inline]
    fn mark(&self) -> Mark {
        Mark {
            idx: self.idx,
            line: self.line,
            col: self.col,
            #[cfg(debug_assertions)]
            committed: self.committed,
        }
    }

    #[inline]
    #[cfg_attr(debug_assertions, track_caller)]
    fn reset(&mut self, m: Mark) {
        // A rewind past a point of no return is `try`'s job, not a plain
        // `reset`'s: `try` puts the commitment back, a `reset` leaves the parse
        // committed and everything reported after it is silently dropped. That
        // asymmetry is what hid SC1019, so every site where it happens is
        // recorded for the audit rather than being left to the eye.
        #[cfg(debug_assertions)]
        if self.committed && !m.committed {
            self.commitment_backtracks
                .insert(std::panic::Location::caller().to_string());
        }
        self.idx = m.idx;
        self.line = m.line;
        self.col = m.col;
    }

    /// The `reset` call sites that rewound over a commitment during this parse.
    ///
    /// Each is a place where the Haskell either wraps the attempt in `try` (and
    /// the port must too) or never commits in the first place. Empty is the
    /// goal; debug builds only.
    #[cfg(debug_assertions)]
    pub fn backtracked_over_commitment(&self) -> Vec<String> {
        let mut v: Vec<String> = self.commitment_backtracks.iter().cloned().collect();
        v.sort();
        v
    }

    #[inline]
    fn pos(&self) -> Position {
        Position {
            file: self.filename.clone(),
            line: self.line,
            column: self.col,
        }
    }

    #[inline]
    fn peek(&self) -> Option<char> {
        self.input.get(self.idx).copied()
    }

    #[inline]
    fn peek_at(&self, n: usize) -> Option<char> {
        self.input.get(self.idx + n).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.input.get(self.idx).copied()?;
        // In Parsec an error travels with the reply, not in the state: when a
        // parser consumes input successfully, `parserBind` returns the consumed
        // reply as it is and whatever error had accumulated is dropped. So the
        // failure a parse finally reports is the furthest one since the last
        // input it managed to read, not the furthest one overall. Past a
        // commitment there is no more reading in Parsec at all, so the failure
        // that ended the parse stands.
        if !self.committed {
            self.failure = None;
        }
        self.idx += 1;
        if self.idx > self.reach {
            self.reach = self.idx;
        }
        match c {
            '\n' => {
                self.line += 1;
                self.col = 1;
            }
            '\t' => {
                // Parsec: advance to next multiple of 8.
                self.col += 8 - ((self.col - 1) % 8);
            }
            _ => self.col += 1,
        }
        if self.idx >= self.reach {
            self.reach_pos = Position {
                file: self.filename.clone(),
                line: self.line,
                column: self.col,
            };
        }
        Some(c)
    }

    fn eof(&self) -> bool {
        self.idx >= self.input.len()
    }

    /// Enter a named production, Haskell `called "name"`. Every `push_ctx`
    /// must be matched by a `pop_ctx` on both the success and failure path;
    /// [`Parser::called`] does that for a whole production body.
    fn push_ctx(&mut self, name: &'static str) {
        let pos = self.pos();
        self.next_serial += 1;
        let serial = self.next_serial;
        self.contexts.push(Context { pos, name, serial });
    }

    fn pop_ctx(&mut self) {
        let _ = self.contexts.pop();
    }

    /// Run `body` as the named production, so that a failure inside it can
    /// report "Couldn't parse this <name>".
    fn called<T>(
        &mut self,
        name: &'static str,
        body: impl FnOnce(&mut Self) -> PResult<T>,
    ) -> PResult<T> {
        let start_idx = self.idx;
        self.push_ctx(name);
        let serial = self.contexts.last().map_or(0, |c| c.serial);
        self.open_starts.push(start_idx);
        let r = body(self);
        self.open_starts.pop();
        if r.is_ok() || self.idx == start_idx {
            // `parsecBracket`: `after val` (popContext) runs when the body
            // succeeds, and on the `<|>` branch taken when it failed without
            // consuming. Note that it pops the *top* of the stack, which after
            // a recovered inner failure is not necessarily this frame.
            self.pop_ctx();
        }
        if r.is_err() && self.idx == start_idx {
            // This production bowed out cleanly, so Haskell would have
            // popped its frame before reading the stack at the end. Drop it
            // from the failure's snapshot too, but only when it is still on
            // top: a frame left behind by a consuming failure below stays.
            let popped = self.contexts.len() + 1;
            if let Some(f) = &mut self.failure {
                if f.contexts.len() == popped && f.contexts[popped - 1].serial == serial {
                    f.contexts.truncate(popped - 1);
                }
            }
            // `parsecBracket`'s `<|> (after val *> fail "")` is only reached
            // when the failure consumed nothing: `<|>` cannot take over from
            // one that did, so no error is raised here at all.
            self.record_failure_as("", false, false);
        }
        r
    }

    /// Fail the current production outright, Haskell `fail "msg"`. The message
    /// reaches the user as SC1072 when this turns out to be the deepest
    /// failure; an empty one is still a deliberate failure, as `fail ""` is in
    /// the Haskell, and is what ends the parse rather than backtracking out.
    /// `readAmbiguous`: a prefix that two productions both claim. Try the
    /// expected one; then the alternative, whose diagnostics are forgotten if
    /// it fails too (`forgetOnFailure`); and if both fail, run the expected one
    /// a second time, so the error reported is the one from the production the
    /// author most likely meant rather than from the fallback.
    fn read_ambiguous(
        &mut self,
        expected: impl Fn(&mut Self) -> PResult<Token>,
        alternative: impl Fn(&mut Self) -> PResult<Token>,
        warn: impl FnOnce(&mut Self, Position),
    ) -> PResult<Token> {
        let pos = self.pos();
        let m = self.mark();
        // `try` rewinds Parsec's own state, which holds the buffered notes.
        let notes = self.notes.len();
        let failure = self.failure.clone();
        // Both attempts sit behind `try`, so a consuming failure in either is
        // caught rather than propagated: the parse is not over.
        let committed = self.committed;
        let frozen = self.frozen_contexts.clone();
        if let Ok(t) = expected(self) {
            return Ok(t);
        }
        self.reset(m);
        self.notes.truncate(notes);
        self.committed = committed;
        self.frozen_contexts = frozen.clone();
        // Problems and contexts live outside Parsec, so the first attempt's
        // survive: `forgetOnFailure` only rewinds what the *alternative* adds.
        let problems = self.problems.len();
        let contexts = self.contexts.clone();
        if let Ok(t) = alternative(self) {
            warn(self, pos);
            return Ok(t);
        }
        self.notes.truncate(notes);
        self.problems.truncate(problems);
        self.contexts = contexts;
        // Both attempts sat behind `try`, so neither error escapes; the last
        // run consumes input and its error alone is what Parsec propagates.
        self.failure = failure;
        self.committed = committed;
        self.frozen_contexts = frozen;
        self.reset(m);
        expected(self)
    }

    fn fail_with<T>(&mut self, message: &str) -> PResult<T> {
        self.record_failure(message, true);
        Err(())
    }

    /// Fail deliberately from inside a `try`, as `unexpecting` does: the
    /// message is still the one reported if nothing gets further, but the
    /// failure reads as non-consuming so an enclosing alternative may recover.
    pub(super) fn fail_recoverable<T>(&mut self, message: &str) -> PResult<T> {
        self.record_failure_as(message, true, false);
        Err(())
    }

    /// Whether a failure here has consumed input since the innermost
    /// production began, and so cannot be backtracked out of.
    fn has_consumed(&self) -> bool {
        self.open_starts.last().is_some_and(|&s| self.idx > s)
    }

    /// Whether a production has failed outright past the point of commitment,
    /// which is what ends the parse.
    pub(super) fn has_committed_failure(&self) -> bool {
        self.committed
    }

    /// The parse is over: no enclosing alternative can recover, so Parsec
    /// propagates the failure straight out of `readScript`. Freeze the context
    /// stack as it stands, since that is the one `notesForContext` reads --
    /// whatever this parser goes on to push while it unwinds.
    pub(super) fn commit(&mut self) {
        if !self.committed {
            self.committed = true;
            self.frozen_contexts = Some(self.contexts.clone());
        }
    }

    /// `try p`: on failure the cursor goes back, and so does Parsec's own state
    /// -- the buffered parse notes, and with them the commitment, since a
    /// consuming failure inside a `try` is caught rather than propagated. The
    /// context stack and the problems live in the `StateT` underneath and stay.
    pub(super) fn try_parse<T>(&mut self, f: impl FnOnce(&mut Self) -> PResult<T>) -> PResult<T> {
        let m = self.mark();
        let notes = self.notes.len();
        let committed = self.committed;
        let frozen = self.frozen_contexts.clone();
        match f(self) {
            Ok(v) => Ok(v),
            Err(()) => {
                self.reset(m);
                self.notes.truncate(notes);
                self.committed = committed;
                self.frozen_contexts = frozen;
                Err(())
            }
        }
    }

    /// `shouldIgnoreCode`: any frame in scope that disables this code, where a
    /// `ContextSource` frame disables *everything* unless `--check-sourced`
    /// (`contextItemDisablesCode`).
    fn code_is_disabled(&self, code: i64) -> bool {
        self.ann_contexts.iter().any(|c| match c {
            AnnContext::Annotations(list) => list.iter().any(|a| match a {
                Annotation::DisableComment(from, to) => code >= *from && code < *to,
                _ => false,
            }),
            AnnContext::Source(_) => !self.check_sourced,
        })
    }

    /// `withAnnotations`: a `disable=` directive applies to the command it
    /// precedes, including the parse problems raised while reading it. Like any
    /// `parsecBracket` the scope closes on success or on a failure that
    /// consumed nothing; one that consumed leaves it open, which is what lets
    /// `# shellcheck disable=..` silence the failure notes too.
    pub(super) fn with_annotations<T>(
        &mut self,
        anns: &[Annotation],
        f: impl FnOnce(&mut Self) -> PResult<T>,
    ) -> PResult<T> {
        let from = self.ann_contexts.len();
        let start_idx = self.idx;
        self.push_disables(anns);
        let r = f(self);
        if r.is_ok() || self.idx == start_idx {
            self.ann_contexts.truncate(from);
        }
        r
    }

    /// `withAnnotations`: these annotations, pushed as one `ContextAnnotation`
    /// frame. An empty list pushes nothing (`if null anns then p else ..`).
    pub(super) fn push_disables(&mut self, anns: &[Annotation]) {
        if !anns.is_empty() {
            self.ann_contexts
                .push(AnnContext::Annotations(anns.to_vec()));
        }
    }

    /// The diagnostics a fatal parse failure reports: the innermost two open
    /// productions as SC1073 / SC1009, and the failure itself as SC1072.
    /// Mirrors `notesForContext ++ [makeErrorFor err]`.
    fn failure_notes(&self) -> Vec<ParseNote> {
        let Some(f) = &self.failure else {
            return Vec::new();
        };
        let mut out = Vec::new();
        // `contextStack` lives in the state *outside* Parsec, so nothing
        // backtracks it: a production that failed after consuming input leaves
        // its frame behind, and that residue is what the report names.
        // `notesForContext (contextStack state)`: the stack as it stands when
        // the parse gives up, which is the one frozen at the commitment (or the
        // live one, when nothing committed). Haskell has the innermost context
        // first; ours has it last.
        let stack = self.frozen_contexts.as_ref().unwrap_or(&self.contexts);
        let mut inner = stack.iter().rev();
        if let Some(c) = inner.next() {
            out.push(ParseNote {
                start: c.pos.clone(),
                end: c.pos.clone(),
                severity: Severity::ErrorC,
                code: 1073,
                message: format!("Couldn't parse this {}. Fix to allow more checks.", c.name),
            });
        }
        if let Some(c) = inner.next() {
            out.push(ParseNote {
                start: c.pos.clone(),
                end: c.pos.clone(),
                severity: Severity::InfoC,
                code: 1009,
                message: format!("The mentioned syntax error was in this {}.", c.name),
            });
        }
        // `getStringFromParsec`: the explicit message, then the fixed tail.
        let detail = if f.message.is_empty() {
            String::new()
        } else {
            format!("{}.", f.message)
        };
        out.push(ParseNote {
            start: f.pos.clone(),
            end: f.pos.clone(),
            severity: Severity::ErrorC,
            code: 1072,
            message: format!("{detail} Fix any mentioned problems and try again."),
        });
        // `isIgnored`: a `disable=` directive in scope silences these too.
        out.retain(|n| !self.code_is_disabled(n.code));
        out
    }

    /// `readStringForParser p`: the raw text `p` would consume, with everything
    /// it read and everything it reported forgotten -- `inSeparateContext
    /// $ lookAhead (p >> getPosition)`, then `anyChar` up to that position.
    pub(super) fn read_string_for_parser(
        &mut self,
        f: impl FnOnce(&mut Self) -> PResult<()>,
    ) -> PResult<String> {
        let m = self.mark();
        let notes = self.notes.len();
        let problems = self.problems.len();
        let contexts = self.contexts.clone();
        let failure = self.failure.clone();
        let committed = self.committed;
        let frozen = self.frozen_contexts.clone();
        let r = f(self);
        let end = self.idx;
        self.reset(m);
        self.notes.truncate(notes);
        self.problems.truncate(problems);
        self.contexts = contexts;
        self.failure = failure;
        self.committed = committed;
        self.frozen_contexts = frozen;
        r?;
        let str: String = self.input[m.idx..end].iter().collect();
        while self.idx < end {
            self.bump();
        }
        Ok(str)
    }

    /// `subParse`: a parser over a different input, continuing this one's id
    /// space, context stack and annotation scope. Parsec's state is swapped,
    /// but everything in the `StateT` underneath it -- contexts, problems --
    /// carries straight through, so the sub-parse's diagnostics name the
    /// productions that contain it.
    pub(super) fn sub_parser(&self, input: &str, start: &Position) -> Parser {
        let mut sub = Parser::new(&self.filename, input);
        sub.line = start.line;
        sub.col = start.column;
        sub.next_id = self.next_id;
        sub.contexts = self.contexts.clone();
        sub.next_serial = self.next_serial;
        sub.ann_contexts = self.ann_contexts.clone();
        sub.sys = Rc::clone(&self.sys);
        sub.check_sourced = self.check_sourced;
        sub.root_filename = self.root_filename.clone();
        sub
    }

    /// Take back what a sub-parser produced: ids, spans and diagnostics.
    pub(super) fn merge_sub(&mut self, sub: Parser) {
        self.next_id = sub.next_id;
        self.next_serial = sub.next_serial;
        for (k, v) in sub.positions {
            self.positions.entry(k).or_insert(v);
        }
        self.notes.extend(sub.notes);
        self.problems.extend(sub.problems);
    }

    /// `tryWithErrors`: a sub-parse whose failure is reported rather than
    /// propagated -- the error itself plus the contexts it was left in -- after
    /// which the caller carries on with nothing (`<|> return []`).
    pub(super) fn report_sub_failure(&mut self, contexts: Vec<Context>, failure: Option<Failure>) {
        // The sub-parse reports against its own stack, which is the one it
        // froze when it committed.
        let outer = self.frozen_contexts.replace(contexts);
        let saved = std::mem::replace(&mut self.failure, failure);
        let notes = self.failure_notes();
        self.frozen_contexts = outer;
        self.failure = saved;
        // `addParseProblem (makeErrorFor err)` then `notesForContext`, so the
        // error comes first.
        if let Some(err) = notes.iter().find(|n| n.code == 1072) {
            self.problems.push(err.clone());
        }
        for n in notes.into_iter().filter(|n| n.code != 1072) {
            self.problems.push(n);
        }
    }

    /// Remember this failure if it is deeper than any seen so far, along with
    /// the productions open around it. Mirrors Parsec keeping the error from
    /// the furthest position reached.
    fn record_failure(&mut self, message: &str, explicit: bool) {
        let consumed = self.has_consumed();
        self.record_failure_as(message, explicit, consumed);
    }

    fn record_failure_as(&mut self, message: &str, explicit: bool, consumed: bool) {
        if self.committed {
            // The parse is over: Parsec would never have reached any of this,
            // so a later failure must not outrank the one that ended it.
            return;
        }
        // Rank failures the way Parsec picks one: by the position the parser
        // had actually reached when it gave up — furthest wins —
        // then — since `getStringFromParsec` keeps only explicit, non-empty
        // `Message`s and discards everything Parsec itself produced — one with
        // something to say, then a deliberate failure over one that was merely
        // backtracked out of, then a production that had committed to what it
        // was reading over an alternative that bailed immediately.
        let rank = (self.idx, !message.is_empty(), explicit, consumed);
        // On a tie the later failure wins: Parsec merges errors at the same
        // position, and what it reports the contexts from is the stack as it
        // stands then -- so the freshest snapshot is the right one.
        let better = match &self.failure {
            None => true,
            Some(f) => rank >= (f.reach, !f.message.is_empty(), f.explicit, f.consumed),
        };
        if better {
            self.failure = Some(Failure {
                reach: self.idx,
                pos: self.pos(),
                message: message.to_string(),
                contexts: self.contexts.clone(),
                consumed,
                explicit,
            });
        }
    }

    // ---- char-class combinators -------------------------------------------

    /// Parsec records an error for every failure, implicit ones included, and
    /// reports the one that got furthest. `getStringFromParsec` keeps only
    /// explicit `Message`s, so an implicit failure contributes its position and
    /// nothing else -- which is why `case '' i` reports no message at all.
    pub(super) fn fail_implicitly(&mut self) {
        self.record_failure_as("", false, false);
    }

    fn char(&mut self, c: char) -> PResult<char> {
        if self.peek() == Some(c) {
            self.bump();
            Ok(c)
        } else {
            self.fail_implicitly();
            Err(())
        }
    }

    fn one_of(&mut self, set: &str) -> PResult<char> {
        match self.peek() {
            Some(c) if set.contains(c) => {
                self.bump();
                Ok(c)
            }
            _ => {
                self.fail_implicitly();
                Err(())
            }
        }
    }

    fn string(&mut self, s: &str) -> PResult<()> {
        let m = self.mark();
        // `tokens` is one primitive: matching the string char by char is an
        // implementation detail that records no errors of its own.
        let saved = self.failure.clone();
        for c in s.chars() {
            if self.char(c).is_err() {
                // Parsec's `tokens` reports a mismatch at the position the
                // string started at, however far into it the mismatch was --
                // so `optional (string "SC")` on `S]` fails at the `S`.
                self.reset(m);
                self.failure = saved;
                self.fail_implicitly();
                return Err(());
            }
        }
        Ok(())
    }

    fn satisfy<F: Fn(char) -> bool>(&mut self, f: F) -> PResult<char> {
        match self.peek() {
            Some(c) if f(c) => {
                self.bump();
                Ok(c)
            }
            _ => Err(()),
        }
    }

    // ---- id / span / notes -------------------------------------------------

    fn next_id_between(&mut self, start: Position, end: Position) -> Id {
        let id = Id(self.next_id);
        self.next_id += 1;
        self.positions.insert(id, (start, end));
        id
    }

    fn span_for(&self, id: Id) -> (Position, Position) {
        self.positions.get(&id).cloned().unwrap_or_default()
    }

    fn note_at(&mut self, start: Position, end: Position, sev: Severity, code: i64, msg: &str) {
        // `addParseNote` checks `shouldIgnoreCode` too.
        if self.code_is_disabled(code) {
            return;
        }
        self.notes.push(ParseNote {
            start,
            end,
            severity: sev,
            code,
            message: msg.to_string(),
        });
    }

    fn problem_at(&mut self, start: Position, end: Position, sev: Severity, code: i64, msg: &str) {
        // `parseProblemAt` checks `shouldIgnoreCode` against the annotation
        // frames in scope.
        if self.code_is_disabled(code) {
            return;
        }
        if self.committed {
            // Parsing is over as far as Haskell is concerned: everything this
            // parser reads past the point of no return is phantom, and its
            // diagnostics would be ones the oracle never had a chance to emit.
            return;
        }
        self.problems.push(ParseNote {
            start,
            end,
            severity: sev,
            code,
            message: msg.to_string(),
        });
    }

    // ---- whitespace / comments --------------------------------------------

    fn line_whitespace(&mut self) -> PResult<char> {
        // " \t" <|> almostSpace <|> carriageReturn-not-before-newline handled elsewhere
        match self.peek() {
            Some(c) if c == ' ' || c == '\t' => {
                self.bump();
                Ok(c)
            }
            _ => self.almost_space(),
        }
    }

    /// `suspectCharAfterQuotes`: a character that, coming straight after a
    /// closing quote, suggests the quote was meant to stay open.
    pub(super) fn suspect_char_after_quotes(&self) -> Option<char> {
        match self.peek() {
            Some(c) if c.is_ascii_alphanumeric() || c == '_' || c == '%' => Some(c),
            _ => None,
        }
    }

    /// `suggestForgotClosingQuote`: a quoted string spanning a line feed and
    /// followed by a suspect character is usually a quote left open earlier.
    pub(super) fn suggest_forgot_closing_quote(
        &mut self,
        start: &Position,
        end: &Position,
        name: &str,
    ) {
        self.problem_at(
            start.clone(),
            start.clone(),
            Severity::WarningC,
            1078,
            &format!("Did you forget to close this {name}?"),
        );
        self.problem_at(
            end.clone(),
            end.clone(),
            Severity::InfoC,
            1079,
            "This is actually an end quote, but due to next char it looks suspect.",
        );
    }

    /// `almostSpace`: a unicode space that the shell does not treat as one.
    /// Reports SC1018 and yields a plain `' '` so the caller can carry on as
    /// though the author had typed a space.
    pub(super) fn almost_space(&mut self) -> PResult<char> {
        match self.peek() {
            Some(c) if ALMOST_SPACE_CHARS.contains(c) => {
                let p = self.pos();
                self.bump();
                self.note_at(
                    p.clone(),
                    p,
                    Severity::ErrorC,
                    1018,
                    "This is a unicode space. Delete and retype it.",
                );
                Ok(' ')
            }
            _ => {
                // `oneOf`: a failure here is an error at this position, like
                // any other primitive's.
                self.fail_implicitly();
                Err(())
            }
        }
    }

    /// `spacing`: linewhitespace / line-continuations, then optional comment.
    fn spacing(&mut self) -> String {
        let mut out = String::new();
        loop {
            let mut progressed = false;
            // many1 linewhitespace
            while let Ok(c) = self.line_whitespace() {
                out.push(c);
                progressed = true;
            }
            // continuation: "\\\n"
            let m = self.mark();
            if self.string("\\\n").is_ok() {
                progressed = true;
                // whitespace after continuation
                while self.line_whitespace().is_ok() {}
                // The line was continued. A comment on the next line ending in a
                // backslash does not continue it any further.
                let cm = self.mark();
                match self.read_comment() {
                    Ok(c) if c.ends_with('\\') => {
                        let pos = self.pos();
                        self.problem_at(
                            pos.clone(),
                            pos,
                            Severity::ErrorC,
                            1143,
                            "This backslash is part of a comment and does not continue the line.",
                        );
                    }
                    Ok(_) => {}
                    Err(()) => self.reset(cm),
                }
            } else {
                self.reset(m);
            }
            if !progressed {
                break;
            }
        }
        let _ = self.read_comment();
        out
    }

    fn spacing1(&mut self) -> PResult<String> {
        let s = self.spacing();
        if s.is_empty() {
            // `when (null spacing) $ fail "Expected whitespace"`
            self.fail_with("Expected whitespace")
        } else {
            Ok(s)
        }
    }

    fn read_comment(&mut self) -> PResult<String> {
        if self.peek() != Some('#') {
            return Err(());
        }
        // Do not consume shellcheck directive lines; leave them for
        // `read_annotation` (mirrors `readComment`'s `unexpecting` guard).
        if self.at_annotation_prefix() {
            return Err(());
        }
        // `readComment = unexpecting "shellcheck annotation" .. >> readAnyComment`:
        // the body is the same `many $ noneOf "\r\n"`, so a CR is left for
        // `carriageReturn` to report as SC1017 rather than swallowed here.
        self.read_any_comment()
    }

    /// `readAnyComment`: a `#` comment, directive or not, to the end of the
    /// line. Unlike `readComment` it does not spare annotations.
    fn read_any_comment(&mut self) -> PResult<String> {
        self.char('#')?;
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '\n' || c == '\r' {
                break;
            }
            self.bump();
            s.push(c);
        }
        Ok(s)
    }

    /// Non-consuming lookahead for `#` (spaces) `shellcheck` `<ws>`.
    fn at_annotation_prefix(&self) -> bool {
        let mut i = self.idx;
        if self.input.get(i) != Some(&'#') {
            return false;
        }
        i += 1;
        while matches!(self.input.get(i), Some(' ') | Some('\t')) {
            i += 1;
        }
        for ch in "shellcheck".chars() {
            if self.input.get(i) != Some(&ch) {
                return false;
            }
            i += 1;
        }
        // `readAnnotationPrefix` stops at "shellcheck": whatever follows,
        // `readComment`'s `unexpecting` refuses the line, so `# shellcheckfoo`
        // is a broken directive rather than a comment.
        true
    }

    /// `carriageReturn`: a literal CR, which the shell keeps as part of the
    /// word and which is therefore always worth reporting.
    fn carriage_return(&mut self) -> PResult<char> {
        if self.peek() != Some('\r') {
            return Err(());
        }
        let pos = self.pos();
        self.bump();
        self.problem_at(
            pos.clone(),
            pos,
            Severity::ErrorC,
            1017,
            "Literal carriage return. Run script through tr -d '\\r' .",
        );
        Ok('\r')
    }

    fn linefeed(&mut self) -> PResult<char> {
        // optional carriage return, then '\n', then read pending heredocs
        let _ = self.carriage_return();
        self.char('\n')?;
        self.read_pending_heredocs()?;
        Ok('\n')
    }

    /// `linefeed <|> carriageReturn`, the unit `readNewlineList` repeats. A
    /// `linefeed` that consumed a CR and then found no `\n` takes the whole
    /// alternation down with it, as a bare `<|>` does.
    fn linefeed_or_carriage_return(&mut self) -> PResult<char> {
        let m = self.mark();
        match self.linefeed() {
            Ok(c) => Ok(c),
            Err(()) => {
                if self.idx != m.idx {
                    return Err(());
                }
                self.carriage_return()
            }
        }
    }

    fn whitespace(&mut self) -> PResult<char> {
        if let Ok(c) = self.line_whitespace() {
            return Ok(c);
        }
        // `whitespace = oneOf " \t" <|> carriageReturn <|> almostSpace <|> linefeed`:
        // a CR is whitespace on its own, CRLF or not.
        if let Ok(c) = self.carriage_return() {
            return Ok(c);
        }
        self.linefeed()
    }

    /// `allspacing`: whitespace including linefeeds and comments.
    fn allspacing(&mut self) {
        // `allspacing = spacing; option False (linefeed >> allspacing)`, so it
        // is `spacing` -- line continuations and a comment included -- with
        // linefeeds between.
        loop {
            self.spacing();
            let m = self.mark();
            if self.linefeed().is_err() {
                self.reset(m);
                break;
            }
        }
    }

    fn line_break(&mut self) {
        // `readLineBreak = optional readNewlineList`: newlines and spacing,
        // then the same bad-break check the newline list makes.
        let mut any = false;
        loop {
            self.spacing();
            let m = self.mark();
            match self.whitespace() {
                Ok('\n' | '\r') => any = true,
                Ok(_) => {}
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        if any {
            self.check_bad_break();
        }
    }

    /// `checkBadBreak`: after a line break, a line that *starts* with `|`, `||`
    /// or `&&` is almost always a continuation the author meant to hang off the
    /// previous line. `&>`/`&>>` is a redirection, not an operator, so it is
    /// excluded (`notFollowedBy2 (string "&>")`).
    pub(super) fn check_bad_break(&mut self) {
        match self.peek() {
            Some('|') => {}
            Some('&') if self.peek_at(1) != Some('>') => {}
            _ => return,
        }
        let pos = self.pos();
        self.problem_at(
            pos.clone(),
            pos,
            Severity::ErrorC,
            1133,
            "Unexpected start of line. If breaking lines, |/||/&& should be at the end of the previous one.",
        );
    }
}

/// Public entry point mirroring `ShellCheck.Parser.parseScript`.
pub fn parse_script(filename: &str, script: &str) -> ParseOutput {
    parse_script_with(filename, script, false, None)
}

/// Parse a script, telling the parser whether the caller supplied `--shell`,
/// and which dialect the caller or the filename named if either did.
/// Parse `script` and report the `reset` sites that rewound over a commitment
/// (see [`Parser::backtracked_over_commitment`]). For the `try`-emulation
/// audit; debug builds only, and the parse result itself is discarded.
#[cfg(debug_assertions)]
pub fn audit_commitment_backtracks(filename: &str, script: &str) -> Vec<String> {
    let mut p = Parser::new(filename, script);
    let _ = p.read_script_file();
    p.backtracked_over_commitment()
}

/// `ShellCheck.Interface.ParseSpec`: everything `parseScript` is given.
///
/// `shell_flag_specified` / `shell_hint` stand for `psShellTypeOverride` plus
/// the filename-derived fallback the checker resolves before parsing.
pub struct ParseSpec {
    pub filename: String,
    pub script: String,
    /// `psCheckSourced`.
    pub check_sourced: bool,
    /// Whether `--shell` (or an equivalent) settled the dialect.
    pub shell_flag_specified: bool,
    /// The dialect as far as the caller knows it.
    pub shell_hint: Option<Shell>,
    /// How `source` statements are resolved and read.
    pub sys: Rc<dyn SystemInterface>,
}

impl Default for ParseSpec {
    /// `newParseSpec`, with the interface that refuses every source as
    /// not-an-input (see [`NoExternalSources`]).
    fn default() -> Self {
        ParseSpec {
            filename: String::new(),
            script: String::new(),
            check_sourced: false,
            shell_flag_specified: false,
            shell_hint: None,
            sys: Rc::new(NoExternalSources),
        }
    }
}

/// `parseScript`: the full entry point, including source following.
pub fn parse_script_spec(spec: &ParseSpec) -> ParseOutput {
    let mut p = Parser::with_shell_flag(
        &spec.filename,
        &spec.script,
        spec.shell_flag_specified,
        spec.shell_hint,
    );
    p.sys = Rc::clone(&spec.sys);
    p.check_sourced = spec.check_sourced;
    p.root_filename = spec.filename.clone();
    finish_parse(p)
}

pub fn parse_script_with(
    filename: &str,
    script: &str,
    shell_flag_specified: bool,
    shell_hint: Option<Shell>,
) -> ParseOutput {
    let p = Parser::with_shell_flag(filename, script, shell_flag_specified, shell_hint);
    finish_parse(p)
}

fn finish_parse(mut p: Parser) -> ParseOutput {
    let root = p.read_script_file();
    // A production that failed after consuming input means the script does not
    // parse, even if backtracking found some other way to read the rest of it:
    // Parsec's `<|>` offers no alternative once input has been consumed. Input
    // simply left over at the end is not this — `verifyEof` reports it and the
    // tree survives.
    let committed_failure = p.has_committed_failure();
    if root.is_none() || committed_failure {
        // Haskell `parseShell`'s `Left err` branch: prRoot = Nothing, so no
        // analysis runs at all, the buffered parse *notes* are discarded, and
        // only the fatal *problems* survive alongside the failure itself.
        let mut notes = p.problems.clone();
        notes.extend(p.failure_notes());
        return ParseOutput {
            root: None,
            notes,
            positions: BTreeMap::new(),
        };
    }
    // Reattach here-doc bodies collected during parsing.
    let root = root.map(|r| reattach_heredocs(r, &p.heredoc_bodies));
    // Reparse array indices as arithmetic / index words (reparseIndices).
    let root = root.map(|r| {
        let assoc = get_associative_arrays(&r);
        p.reparse_indices_root(r, &assoc)
    });
    // Parse succeeded (we always return a tree in the slice); emit notes+problems.
    let mut notes = p.problems.clone();
    notes.extend(p.notes.clone());
    ParseOutput {
        root,
        notes,
        positions: p.positions,
    }
}

/// `getAssociativeArrays`: names declared with `declare/local/typeset -A`.
fn get_associative_arrays(root: &Token) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
            if words.is_empty() {
                return;
            }
            let name = match &*words[0].inner {
                InnerToken::T_NormalWord(parts) if parts.len() == 1 => match &*parts[0].inner {
                    InnerToken::T_Literal(s) => Some(s.clone()),
                    _ => None,
                },
                _ => None,
            };
            if !matches!(
                name.as_deref(),
                Some("declare") | Some("local") | Some("typeset")
            ) {
                return;
            }
            let args = &words[1..];
            // Collect flag chars (getAllFlags).
            let mut has_a = false;
            for a in args {
                if let Some(s) = crate::ast_lib::get_literal_string(a) {
                    if let Some(rest) = s.strip_prefix("--") {
                        let _ = rest;
                    } else if let Some(chars) = s.strip_prefix('-') {
                        if chars.contains('A') {
                            has_a = true;
                        }
                    }
                }
            }
            if !has_a {
                return;
            }
            for a in args {
                // non-flag args only
                let lit = crate::ast_lib::get_literal_string(a);
                if let Some(ref s) = lit {
                    if s.starts_with('-') {
                        continue;
                    }
                }
                match &*a.inner {
                    InnerToken::T_Assignment { var, .. } => {
                        out.insert(var.clone());
                    }
                    _ => {
                        if let Some(s) = lit {
                            out.insert(s);
                        }
                    }
                }
            }
        }
    });
    out
}

/// `unEscape` from `readBackTicked`: process backslash escapes in backtick
/// command-substitution content before sub-parsing.
fn unescape_backtick(raw: &str, quoted: bool) -> String {
    let chars: Vec<char> = raw.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c == '\\' && i + 1 < chars.len() {
            let x = chars[i + 1];
            if quoted && x == '"' {
                out.push('"');
                i += 2;
                continue;
            }
            if x == '$' || x == '`' || x == '\\' {
                out.push(x);
                i += 2;
                continue;
            }
            if x == '\n' {
                i += 2;
                continue;
            }
            // Other escapes keep the backslash (process the next char normally).
            out.push('\\');
            i += 1;
            continue;
        }
        out.push(c);
        i += 1;
    }
    out
}

fn reattach_heredocs(t: Token, bodies: &BTreeMap<Id, Vec<Token>>) -> Token {
    // Rebuild the tree, filling T_HereDoc bodies by id.
    let Token { id, inner } = t;
    let inner = std::rc::Rc::try_unwrap(inner).unwrap_or_else(|shared| (*shared).clone());
    let new_inner = map_children_inner(inner, bodies, id);
    Token {
        id,
        inner: std::rc::Rc::new(new_inner),
    }
}

fn map_children_inner(inner: InnerToken, bodies: &BTreeMap<Id, Vec<Token>>, id: Id) -> InnerToken {
    use InnerToken::*;
    // Special-case heredoc body fill.
    if let T_HereDoc {
        dashed,
        quoted,
        delim,
        ..
    } = &inner
    {
        if let Some(body) = bodies.get(&id) {
            return T_HereDoc {
                dashed: *dashed,
                quoted: *quoted,
                delim: delim.clone(),
                body: body
                    .iter()
                    .cloned()
                    .map(|b| reattach_heredocs(b, bodies))
                    .collect(),
            };
        }
    }
    // Generic recursive rebuild.
    macro_rules! r {
        ($t:expr) => {
            reattach_heredocs($t, bodies)
        };
    }
    macro_rules! rv {
        ($v:expr) => {
            $v.into_iter()
                .map(|x| reattach_heredocs(x, bodies))
                .collect()
        };
    }
    match inner {
        T_NormalWord(l) => T_NormalWord(rv!(l)),
        T_DoubleQuoted(l) => T_DoubleQuoted(rv!(l)),
        T_DollarDoubleQuoted(l) => T_DollarDoubleQuoted(rv!(l)),
        T_DollarExpansion(l) => T_DollarExpansion(rv!(l)),
        T_Backticked(l) => T_Backticked(rv!(l)),
        T_Subshell(l) => T_Subshell(rv!(l)),
        T_BraceGroup(l) => T_BraceGroup(rv!(l)),
        T_Array(l) => T_Array(rv!(l)),
        T_Extglob { op, list } => T_Extglob {
            op,
            list: rv!(list),
        },
        T_ProcSub { op, list } => T_ProcSub {
            op,
            list: rv!(list),
        },
        T_Condition { typ, token } => T_Condition {
            typ,
            token: r!(token),
        },
        TC_And { typ, op, lhs, rhs } => TC_And {
            typ,
            op,
            lhs: r!(lhs),
            rhs: r!(rhs),
        },
        TC_Or { typ, op, lhs, rhs } => TC_Or {
            typ,
            op,
            lhs: r!(lhs),
            rhs: r!(rhs),
        },
        TC_Binary { typ, op, lhs, rhs } => TC_Binary {
            typ,
            op,
            lhs: r!(lhs),
            rhs: r!(rhs),
        },
        TC_Group { typ, token } => TC_Group {
            typ,
            token: r!(token),
        },
        TC_Nullary { typ, token } => TC_Nullary {
            typ,
            token: r!(token),
        },
        TC_Unary { typ, op, token } => TC_Unary {
            typ,
            op,
            token: r!(token),
        },
        T_DollarArithmetic(t) => T_DollarArithmetic(r!(t)),
        T_DollarBracket(t) => T_DollarBracket(r!(t)),
        T_Arithmetic(t) => T_Arithmetic(r!(t)),
        TA_Binary { op, lhs, rhs } => TA_Binary {
            op,
            lhs: r!(lhs),
            rhs: r!(rhs),
        },
        TA_Assignment { op, lhs, rhs } => TA_Assignment {
            op,
            lhs: r!(lhs),
            rhs: r!(rhs),
        },
        TA_Variable { name, indices } => TA_Variable {
            name,
            indices: rv!(indices),
        },
        TA_Expansion(l) => TA_Expansion(rv!(l)),
        TA_Sequence(l) => TA_Sequence(rv!(l)),
        TA_Parenthesis(t) => TA_Parenthesis(r!(t)),
        TA_Trinary { cond, then, els } => TA_Trinary {
            cond: r!(cond),
            then: r!(then),
            els: r!(els),
        },
        TA_Unary { op, operand } => TA_Unary {
            op,
            operand: r!(operand),
        },
        T_Backgrounded(t) => T_Backgrounded(r!(t)),
        T_Banged(t) => T_Banged(r!(t)),
        T_HereString(t) => T_HereString(r!(t)),
        T_DollarBraced { braced, op } => T_DollarBraced { braced, op: r!(op) },
        T_AndIf { lhs, rhs } => T_AndIf {
            lhs: r!(lhs),
            rhs: r!(rhs),
        },
        T_OrIf { lhs, rhs } => T_OrIf {
            lhs: r!(lhs),
            rhs: r!(rhs),
        },
        T_Pipeline {
            separators,
            commands,
        } => T_Pipeline {
            separators: rv!(separators),
            commands: rv!(commands),
        },
        T_Redirecting { redirs, cmd } => T_Redirecting {
            redirs: rv!(redirs),
            cmd: r!(cmd),
        },
        T_SimpleCommand { assignments, words } => T_SimpleCommand {
            assignments: rv!(assignments),
            words: rv!(words),
        },
        T_Assignment {
            mode,
            var,
            indices,
            value,
        } => T_Assignment {
            mode,
            var,
            indices: rv!(indices),
            value: r!(value),
        },
        T_IfExpression { clauses, elses } => T_IfExpression {
            clauses: clauses.into_iter().map(|(c, b)| (rv!(c), rv!(b))).collect(),
            elses: rv!(elses),
        },
        T_WhileExpression { condition, body } => T_WhileExpression {
            condition: rv!(condition),
            body: rv!(body),
        },
        T_UntilExpression { condition, body } => T_UntilExpression {
            condition: rv!(condition),
            body: rv!(body),
        },
        T_ForIn { var, items, body } => T_ForIn {
            var,
            items: rv!(items),
            body: rv!(body),
        },
        T_SelectIn { var, items, body } => T_SelectIn {
            var,
            items: rv!(items),
            body: rv!(body),
        },
        T_ForArithmetic {
            init,
            cond,
            step,
            body,
        } => T_ForArithmetic {
            init: r!(init),
            cond: r!(cond),
            step: r!(step),
            body: rv!(body),
        },
        T_CaseExpression { word, cases } => T_CaseExpression {
            word: r!(word),
            cases: cases
                .into_iter()
                .map(|(t, p, b)| (t, rv!(p), rv!(b)))
                .collect(),
        },
        T_Function {
            keyword,
            parens,
            name,
            body,
        } => T_Function {
            keyword,
            parens,
            name,
            body: r!(body),
        },
        T_BatsTest { name, body } => T_BatsTest {
            name,
            body: r!(body),
        },
        T_Script { shebang, commands } => T_Script {
            shebang: r!(shebang),
            commands: rv!(commands),
        },
        T_Annotation { annotations, token } => T_Annotation {
            annotations,
            token: r!(token),
        },
        T_IoFile { op, file } => T_IoFile {
            op: r!(op),
            file: r!(file),
        },
        T_IoDuplicate { op, num } => T_IoDuplicate { op: r!(op), num },
        T_FdRedirect { fd, target } => T_FdRedirect {
            fd,
            target: r!(target),
        },
        // A sourced file has already had its own here documents reattached by
        // the sub-parse that read it (`readScriptFile` does that per file), but
        // the `source` command itself is an ordinary command that may carry
        // one, so both halves are still walked.
        T_SourceCommand { includer, included } => T_SourceCommand {
            includer: r!(includer),
            included: r!(included),
        },
        T_Include(t) => T_Include(r!(t)),
        other => other,
    }
}
