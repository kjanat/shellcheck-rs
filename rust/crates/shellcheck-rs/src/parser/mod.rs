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
use crate::interface::{Position, Severity};
use std::collections::BTreeMap;

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
}

type PResult<T> = Result<T, ()>;

struct PendingHereDoc {
    dashed: Dashed,
    quoted: Quoted,
    delim: String,
    // id of the T_HereDoc token to fill in once the body is read
    id: Id,
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
    /// The furthest input index the parser has ever reached. Parsec reports
    /// the error from the furthest failing alternative, not the last one
    /// tried, so failures are ranked by this rather than by the live cursor.
    reach: usize,
    /// The source position of [`Parser::reach`].
    reach_pos: Position,
    /// The deepest failure seen, which is the one a fatal parse reports.
    failure: Option<Failure>,
    /// Whether the caller passed `--shell`, which like a `shell=` directive
    /// means the shebang no longer decides anything and is not checked.
    shell_flag_specified: bool,
}

/// One open production, mirroring Haskell's `ContextName pos str`.
#[derive(Debug, Clone)]
struct Context {
    pos: Position,
    name: &'static str,
    /// Input index where this production started. A failure past it has
    /// consumed input, which in Parsec means `<|>` can no longer recover.
    start_idx: usize,
}

/// The deepest parse failure, with the contexts that were open at the time.
#[derive(Debug, Clone)]
struct Failure {
    reach: usize,
    pos: Position,
    message: String,
    contexts: Vec<Context>,
    /// True when the failing production had already consumed input. Parsec's
    /// `<|>` only tries the next alternative if the previous one failed
    /// *without* consuming, so such a failure both describes the error better
    /// and, when it came from an explicit `fail`, ends the parse outright.
    consumed: bool,
}

const DOUBLE_QUOTABLE: &str = "\\\"$`";
const NBSP: char = '\u{A0}';

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
        Parser::with_shell_flag(filename, script, false)
    }

    /// `shell_flag_specified` mirrors Haskell's `shellTypeOverride`: `--shell`
    /// suppresses the shebang checks just as a `# shellcheck shell=` directive
    /// does, because the caller has already said what dialect this is.
    pub fn with_shell_flag(filename: &str, script: &str, shell_flag_specified: bool) -> Parser {
        Parser {
            shell_flag_specified,
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
        }
    }

    #[inline]
    fn reset(&mut self, m: Mark) {
        self.idx = m.idx;
        self.line = m.line;
        self.col = m.col;
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
        let start_idx = self.idx;
        self.contexts.push(Context {
            pos,
            name,
            start_idx,
        });
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
        self.push_ctx(name);
        let r = body(self);
        if r.is_err() {
            self.record_failure("");
        }
        self.pop_ctx();
        r
    }

    /// Fail the current production with an explicit message, Haskell
    /// `fail "msg"`. The message reaches the user as SC1072 when this turns
    /// out to be the deepest failure.
    fn fail_with<T>(&mut self, message: &str) -> PResult<T> {
        self.record_failure(message);
        Err(())
    }

    /// Whether a failure here has consumed input since the innermost
    /// production began, and so cannot be backtracked out of.
    fn has_consumed(&self) -> bool {
        self.contexts.last().is_some_and(|c| self.idx > c.start_idx)
    }

    /// The diagnostics a fatal parse failure reports: the innermost two open
    /// productions as SC1073 / SC1009, and the failure itself as SC1072.
    /// Mirrors `notesForContext ++ [makeErrorFor err]`.
    fn failure_notes(&self) -> Vec<ParseNote> {
        let Some(f) = &self.failure else {
            return Vec::new();
        };
        let mut out = Vec::new();
        // Haskell's stack has the innermost context first; ours has it last.
        let mut inner = f.contexts.iter().rev();
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
        out
    }

    /// Remember this failure if it is deeper than any seen so far, along with
    /// the productions open around it. Mirrors Parsec keeping the error from
    /// the furthest position reached.
    fn record_failure(&mut self, message: &str) {
        let consumed = self.has_consumed();
        // Rank failures the way Parsec picks one: furthest position first,
        // then a production that had committed to what it was reading over an
        // alternative that bailed immediately, then one that had something to
        // say over one that merely ran out of input.
        let rank = (self.reach, consumed, !message.is_empty());
        let better = match &self.failure {
            None => true,
            Some(f) => rank > (f.reach, f.consumed, !f.message.is_empty()),
        };
        if better {
            self.failure = Some(Failure {
                reach: self.reach,
                pos: self.reach_pos.clone(),
                message: message.to_string(),
                contexts: self.contexts.clone(),
                consumed,
            });
        }
    }

    // ---- char-class combinators -------------------------------------------

    fn char(&mut self, c: char) -> PResult<char> {
        if self.peek() == Some(c) {
            self.bump();
            Ok(c)
        } else {
            Err(())
        }
    }

    fn one_of(&mut self, set: &str) -> PResult<char> {
        match self.peek() {
            Some(c) if set.contains(c) => {
                self.bump();
                Ok(c)
            }
            _ => Err(()),
        }
    }

    fn string(&mut self, s: &str) -> PResult<()> {
        let m = self.mark();
        for c in s.chars() {
            if self.char(c).is_err() {
                self.reset(m);
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
        self.notes.push(ParseNote {
            start,
            end,
            severity: sev,
            code,
            message: msg.to_string(),
        });
    }

    fn problem_at(&mut self, start: Position, end: Position, sev: Severity, code: i64, msg: &str) {
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
        // " \t" <|> almostSpace(NBSP) <|> carriageReturn-not-before-newline handled elsewhere
        match self.peek() {
            Some(c) if c == ' ' || c == '\t' => {
                self.bump();
                Ok(c)
            }
            Some(c) if c == NBSP => {
                let p = self.pos();
                self.bump();
                self.note_at(
                    p.clone(),
                    p,
                    Severity::ErrorC,
                    1018,
                    "This is a unicode non-breaking space. Delete and retype it.",
                );
                Ok(' ')
            }
            _ => Err(()),
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
        if s.is_empty() { Err(()) } else { Ok(s) }
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
        self.bump();
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '\n' {
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
        // must be followed by whitespace or end (so "shellcheckfoo" is not a directive)
        matches!(
            self.input.get(i),
            None | Some(' ') | Some('\t') | Some('\n') | Some('\r')
        )
    }

    fn linefeed(&mut self) -> PResult<char> {
        // optional carriage return, then '\n', then read pending heredocs
        let _ = self.char('\r');
        self.char('\n')?;
        self.read_pending_heredocs();
        Ok('\n')
    }

    fn whitespace(&mut self) -> PResult<char> {
        if let Ok(c) = self.line_whitespace() {
            return Ok(c);
        }
        // carriage return
        let m = self.mark();
        if self.char('\r').is_ok() {
            // lone CR (not part of CRLF handled by linefeed) -> treat as space-ish
            if self.peek() == Some('\n') {
                self.reset(m);
            } else {
                return Ok('\r');
            }
        }
        self.linefeed()
    }

    /// `allspacing`: whitespace including linefeeds and comments.
    fn allspacing(&mut self) {
        loop {
            let mut progressed = false;
            while self.whitespace().is_ok() {
                progressed = true;
            }
            let m = self.mark();
            if self.read_comment().is_ok() {
                progressed = true;
            } else {
                self.reset(m);
            }
            if !progressed {
                break;
            }
        }
    }

    fn line_break(&mut self) {
        // readLineBreak = optional (many linefeed-ish). Consume newlines + spacing.
        loop {
            self.spacing();
            let m = self.mark();
            if self.whitespace().is_ok() {
                // keep going only if it was a newline-type space
                continue;
            } else {
                self.reset(m);
                break;
            }
        }
    }
}

/// Public entry point mirroring `ShellCheck.Parser.parseScript`.
pub fn parse_script(filename: &str, script: &str) -> ParseOutput {
    parse_script_with(filename, script, false)
}

/// Parse a script, telling the parser whether the caller supplied `--shell`.
pub fn parse_script_with(filename: &str, script: &str, shell_flag_specified: bool) -> ParseOutput {
    let mut p = Parser::with_shell_flag(filename, script, shell_flag_specified);
    let root = p.read_script_file();
    // A production that failed after committing to what it was reading means
    // the script does not parse, even if backtracking found some other way to
    // read the rest of it.
    // Only an explicit `fail` past the point of commitment ends the parse:
    // that is where ShellCheck's grammar has decided what it is reading, and
    // where Parsec's `<|>` can no longer offer an alternative.
    let committed_failure = p
        .failure
        .as_ref()
        .is_some_and(|f| f.consumed && !f.message.is_empty());
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
    let new_inner = map_children_inner(*inner, bodies, id);
    Token {
        id,
        inner: Box::new(new_inner),
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
        other => other,
    }
}
