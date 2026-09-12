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
use crate::astlib;
use crate::interface::{Position, Severity};
use std::collections::BTreeMap;

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
        Parser {
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
        Some(c)
    }

    fn eof(&self) -> bool {
        self.idx >= self.input.len()
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

// ============================================================================
// Productions
// ============================================================================

impl Parser {
    // ---- words -------------------------------------------------------------

    /// `readNormalWord` = many1 word parts -> T_NormalWord
    fn read_normal_word(&mut self) -> PResult<Token> {
        self.read_normalish_word(&["do", "done", "then", "fi", "esac"])
    }

    fn read_normalish_word(&mut self, _terms: &[&str]) -> PResult<Token> {
        let start = self.pos();
        let mut parts = Vec::new();
        while let Ok(p) = self.read_normal_word_part() {
            parts.push(p);
        }
        if parts.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_NormalWord(parts)))
    }

    fn read_normal_word_part(&mut self) -> PResult<Token> {
        match self.peek() {
            None => Err(()),
            Some(c) => match c {
                '\'' => self.read_single_quoted(),
                '"' => self.read_double_quoted(),
                '$' => self.read_normal_dollar(),
                '`' => self.read_backticked(false),
                // extglob start: ?*@!+ followed by '('
                _ if "?*@!+".contains(c) && self.peek_at(1) == Some('(') => self.read_extglob(),
                '*' | '?' | '[' => self.read_glob(),
                // Lone extglob-start chars (@ ! +) become globby literals,
                // matching `readGlobbyLiteral`.
                '@' | '!' | '+' => {
                    let start = self.pos();
                    self.bump();
                    let id = self.next_id_between(start, self.pos());
                    Ok(Token::new(id, InnerToken::T_Literal(c.to_string())))
                }
                '<' | '>' if self.peek_at(1) == Some('(') => self.read_proc_sub(),
                '{' | '}' => self.read_brace_or_literal(),
                _ => self.read_normal_literal(""),
            },
        }
    }

    fn read_single_quoted(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('\'')?;
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '\'' {
                break;
            }
            self.bump();
            s.push(c);
        }
        self.char('\'').map_err(|_| ())?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_SingleQuoted(s)))
    }

    fn read_double_quoted(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('"')?;
        let mut parts = Vec::new();
        loop {
            match self.peek() {
                Some('"') | None => break,
                Some('$') => {
                    if let Ok(t) = self.read_double_quoted_dollar() {
                        parts.push(t);
                        continue;
                    }
                    // literal '$'
                    parts.push(self.read_double_literal_run()?);
                }
                Some('`') => parts.push(self.read_backticked(true)?),
                _ => parts.push(self.read_double_literal_run()?),
            }
        }
        self.char('"').map_err(|_| ())?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DoubleQuoted(parts)))
    }

    fn read_double_literal_run(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '\\' {
                // double-escaped: backslash + one of \"$`, else literal backslash
                let nxt = self.peek_at(1);
                if let Some(n) = nxt {
                    if DOUBLE_QUOTABLE.contains(n) {
                        self.bump();
                        self.bump();
                        s.push('\\');
                        s.push(n);
                        continue;
                    }
                }
                self.bump();
                s.push('\\');
                continue;
            }
            if DOUBLE_QUOTABLE.contains(c) {
                break;
            }
            self.bump();
            s.push(c);
        }
        if s.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }

    fn read_normal_literal(&mut self, custom_end: &str) -> PResult<Token> {
        let start = self.pos();
        let mut s = String::new();
        // standard end: "[{}" ++ quotableChars ++ extglobStartChars ++ unicode quotes.
        // Must include `'` so a mid-word single quote starts a T_SingleQuoted part
        // rather than being swallowed into the literal.
        let standard_end = "[{}|&;<>()\\ \t\n\r\u{A0}\"'$`?*@!+";
        loop {
            match self.peek() {
                Some('\\') => {
                    // escaped char
                    self.bump();
                    match self.bump() {
                        Some('\n') => { /* line continuation: produces nothing */ }
                        Some(c) => s.push(c),
                        None => s.push('\\'),
                    }
                }
                Some(c) if !custom_end.contains(c) && !standard_end.contains(c) => {
                    self.bump();
                    s.push(c);
                }
                _ => break,
            }
        }
        if s.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }

    fn read_glob(&mut self) -> PResult<Token> {
        let start = self.pos();
        match self.peek() {
            Some(c @ ('*' | '?')) => {
                self.bump();
                let id = self.next_id_between(start, self.pos());
                Ok(Token::new(id, InnerToken::T_Glob(c.to_string())))
            }
            Some('[') => {
                let m = self.mark();
                if let Ok(g) = self.read_glob_class(start.clone()) {
                    Ok(g)
                } else {
                    self.reset(m);
                    // globby literal '['
                    self.bump();
                    let id = self.next_id_between(start, self.pos());
                    Ok(Token::new(id, InnerToken::T_Literal("[".to_string())))
                }
            }
            _ => Err(()),
        }
    }

    fn read_glob_class(&mut self, start: Position) -> PResult<Token> {
        self.char('[')?;
        let mut body = String::from("[");
        if let Ok(c) = self.one_of("!^") {
            body.push(c);
        }
        if let Ok(c) = self.one_of("]") {
            body.push(c);
        }
        let mut had = false;
        loop {
            // predefined [:class:]
            let m = self.mark();
            if self.string("[:").is_ok() {
                let mut cls = String::new();
                while let Ok(c) = self.satisfy(|c| c.is_ascii_alphabetic()) {
                    cls.push(c);
                }
                if !cls.is_empty() && self.string(":]").is_ok() {
                    body.push_str("[:");
                    body.push_str(&cls);
                    body.push_str(":]");
                    had = true;
                    continue;
                }
                self.reset(m);
            } else {
                self.reset(m);
            }
            // Faithful port of `readClass`'s inner
            // `many (predefined <|> readNormalLiteralPart "]" <|> globchars)`.
            // `predefined` ([:class:]) is handled above. Here we handle escapes,
            // globchars (`![` + extglobStartChars), and normal literal parts,
            // stopping on `]`/EOF or any char in `customEnd ++ standardEnd`.
            match self.peek() {
                Some(']') | None => break,
                // readNormalEscaped: backslash + the escaped char.
                Some('\\') => {
                    self.bump();
                    body.push('\\');
                    if let Some(n) = self.peek() {
                        self.bump();
                        body.push(n);
                    }
                    had = true;
                }
                // globchars = oneOf ("![" ++ extglobStartChars): accepted as a
                // single char even though they otherwise terminate a literal run.
                Some(c) if "![?*@+".contains(c) => {
                    self.bump();
                    body.push(c);
                    had = true;
                }
                // standardEnd = "[{}" ++ quotableChars ++ extglobStartChars ++
                // unicodeDoubleQuotes (minus `\` handled above, and `[`/extglob
                // handled as globchars). These terminate the class body.
                Some(c) if is_glob_class_terminator(c) => break,
                Some(c) => {
                    self.bump();
                    body.push(c);
                    had = true;
                }
            }
        }
        if !had {
            return Err(());
        }
        self.char(']')?;
        body.push(']');
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Glob(body)))
    }

    fn read_brace_or_literal(&mut self) -> PResult<Token> {
        // Faithful port of `readBraced <|> readLiteralCurlyBraces` from
        // `readNormalWordPart`: try a real brace expansion (`{a,b}`, `{1..3}`,
        // nested, with recursive element words); if it is not a valid brace
        // expansion, fall back to a bare `{` (or `}`) literal so non-expansions
        // still parse.
        let start = self.pos();
        if self.peek() == Some('{') {
            let m = self.mark();
            if let Ok(t) = self.read_braced() {
                return Ok(t);
            }
            self.reset(m);
            self.bump();
            let id = self.next_id_between(start, self.pos());
            return Ok(Token::new(id, InnerToken::T_Literal("{".to_string())));
        }
        // bare '}'
        self.char('}')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal("}".to_string())))
    }

    /// `readBraced = try braceExpansion` (Parser.hs). A brace expansion is
    /// `'{' (bracedElement `sepBy1` ',') '}'` guarded so it needs either >=2
    /// elements, or a single element whose literal string contains "..".
    /// Returns `Err` (leaving the input untouched) when it is not one.
    fn read_braced(&mut self) -> PResult<Token> {
        let start = self.pos();
        let m = self.mark();
        if self.char('{').is_err() {
            self.reset(m);
            return Err(());
        }
        // bracedElement `sepBy1` ','  — bracedElement always succeeds (`many`),
        // so there is at least one element.
        let mut elements = vec![self.read_braced_element()];
        while self.peek() == Some(',') {
            self.bump();
            elements.push(self.read_braced_element());
        }
        let guard_ok = match elements.len() {
            0 => false,
            1 => astlib::only_literal_string(&elements[0]).contains(".."),
            _ => true,
        };
        if !guard_ok {
            self.reset(m);
            return Err(());
        }
        if self.char('}').is_err() {
            self.reset(m);
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_BraceExpansion(elements)))
    }

    /// `bracedElement = T_NormalWord `withParser` many [ braceExpansion,
    /// readDollarExpression, readSingleQuoted, readDoubleQuoted, braceLiteral ]`.
    /// `many` never fails, so this always yields a (possibly empty) NormalWord.
    fn read_braced_element(&mut self) -> Token {
        let start = self.pos();
        let mut parts = Vec::new();
        loop {
            // nested brace expansion
            let m = self.mark();
            if let Ok(t) = self.read_braced() {
                parts.push(t);
                continue;
            }
            self.reset(m);
            // readDollarExpression = ensureDollar >> readDollarExp (no lonely $,
            // no $'..'/$"..")
            if self.peek() == Some('$') {
                let m2 = self.mark();
                if let Ok(t) = self.read_dollar_exp() {
                    parts.push(t);
                    continue;
                }
                self.reset(m2);
            }
            if self.peek() == Some('\'') {
                if let Ok(t) = self.read_single_quoted() {
                    parts.push(t);
                    continue;
                }
            }
            if self.peek() == Some('"') {
                if let Ok(t) = self.read_double_quoted() {
                    parts.push(t);
                    continue;
                }
            }
            if let Ok(t) = self.read_brace_literal() {
                parts.push(t);
                continue;
            }
            break;
        }
        let id = self.next_id_between(start, self.pos());
        Token::new(id, InnerToken::T_NormalWord(parts))
    }

    /// `braceLiteral = T_Literal `withParser` readGenericLiteral1 (oneOf
    /// "{}\"$'," <|> whitespace)`. Reads at least one char, keeping escape
    /// backslashes verbatim (except `\<newline>`, which produces nothing).
    fn read_brace_literal(&mut self) -> PResult<Token> {
        fn is_brace_ws(c: char) -> bool {
            matches!(
                c,
                ' ' | '\t'
                    | '\n'
                    | '\r'
                    | '\u{A0}'
                    | '\u{2002}'
                    | '\u{2003}'
                    | '\u{2004}'
                    | '\u{2005}'
                    | '\u{2006}'
                    | '\u{2007}'
                    | '\u{2008}'
                    | '\u{2009}'
                    | '\u{200B}'
                    | '\u{202F}'
            )
        }
        let start = self.pos();
        let mut s = String::new();
        loop {
            match self.peek() {
                Some('\\') => {
                    self.bump();
                    match self.bump() {
                        Some('\n') => { /* line continuation: produces nothing */ }
                        Some(c) => {
                            s.push('\\');
                            s.push(c);
                        }
                        None => s.push('\\'),
                    }
                }
                Some(c) if !"{}\"$',".contains(c) && !is_brace_ws(c) => {
                    self.bump();
                    s.push(c);
                }
                _ => break,
            }
        }
        if s.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }

    fn read_proc_sub(&mut self) -> PResult<Token> {
        let start = self.pos();
        let dir = self.one_of("<>")?;
        self.char('(')?;
        let sub_start = self.pos();
        let raw = self.read_balanced_parens_until_close()?;
        let list = self.subparse_commands(&raw, sub_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_ProcSub {
                op: dir.to_string(),
                list,
            },
        ))
    }

    fn read_extglob(&mut self) -> PResult<Token> {
        let start = self.pos();
        let op = self.one_of("?*@!+")?;
        self.char('(')?;
        // read inner as list of words separated by |
        let mut parts = Vec::new();
        loop {
            match self.peek() {
                Some(')') | None => break,
                Some('|') => {
                    self.bump();
                }
                _ => {
                    if let Ok(w) = self.read_normal_word_part() {
                        parts.push(w);
                    } else {
                        break;
                    }
                }
            }
        }
        self.char(')')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_Extglob {
                op: op.to_string(),
                list: parts,
            },
        ))
    }

    fn read_backticked(&mut self, quoted: bool) -> PResult<Token> {
        let start = self.pos();
        self.char('`')?;
        // collect raw until closing backtick, then unescape + subparse
        let sub_start = self.pos();
        let mut raw = String::new();
        while let Some(c) = self.peek() {
            if c == '`' {
                break;
            }
            if c == '\\' {
                self.bump();
                raw.push('\\');
                if let Some(n) = self.bump() {
                    raw.push(n);
                }
                continue;
            }
            self.bump();
            raw.push(c);
        }
        self.char('`').map_err(|_| ())?;
        // `unEscape`: process backtick escapes (`\$` `` \` `` `\\`, line splices,
        // and `\"`->`"` when inside double quotes) before sub-parsing.
        let unescaped = unescape_backtick(&raw, quoted);
        let cmds = self.subparse_commands(&unescaped, sub_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Backticked(cmds)))
    }

    // ---- dollar expansions -------------------------------------------------

    fn read_normal_dollar(&mut self) -> PResult<Token> {
        // ensureDollar
        if self.peek() != Some('$') {
            return Err(());
        }
        // Each alternative must be atomic: reset to the '$' before trying the
        // next, since a sub-parser may consume the '$' then fail.
        let m = self.mark();
        if let Ok(t) = self.read_dollar_exp() {
            return Ok(t);
        }
        self.reset(m);
        // $'...'
        if let Ok(t) = self.read_dollar_single_quote() {
            return Ok(t);
        }
        self.reset(m);
        // $"..."
        if let Ok(t) = self.read_dollar_double_quote() {
            return Ok(t);
        }
        self.reset(m);
        self.read_dollar_lonely()
    }

    fn read_double_quoted_dollar(&mut self) -> PResult<Token> {
        if self.peek() != Some('$') {
            return Err(());
        }
        let m = self.mark();
        if let Ok(t) = self.read_dollar_exp() {
            return Ok(t);
        }
        self.reset(m);
        self.read_dollar_lonely()
    }

    fn read_dollar_exp(&mut self) -> PResult<Token> {
        // arithmetic $((, expansion $(, bracket $[, braced ${, variable $x
        let m = self.mark();
        if self.peek() == Some('$') && self.peek_at(1) == Some('(') && self.peek_at(2) == Some('(')
        {
            if let Ok(t) = self.read_dollar_arithmetic() {
                return Ok(t);
            }
            self.reset(m);
        }
        if self.peek() == Some('$') && self.peek_at(1) == Some('(') {
            return self.read_dollar_expansion();
        }
        if self.peek() == Some('$') && self.peek_at(1) == Some('[') {
            return self.read_dollar_bracket();
        }
        // ksh/bash `${ cmd; }` / `${| cmd; }` command expansion: `${` then a
        // pipe or whitespace.
        if self.peek() == Some('$')
            && self.peek_at(1) == Some('{')
            && matches!(
                self.peek_at(2),
                Some('|') | Some(' ') | Some('\t') | Some('\n') | Some('\r')
            )
        {
            if let Ok(t) = self.read_dollar_brace_command_expansion() {
                return Ok(t);
            }
            self.reset(m);
        }
        if self.peek() == Some('$') && self.peek_at(1) == Some('{') {
            return self.read_dollar_braced();
        }
        self.read_dollar_variable()
    }

    fn read_dollar_arithmetic(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$((")?;
        let c = self.read_arithmetic_contents()?;
        self.char(')')?;
        if self.char(')').is_err() {
            // Haskell: char ')' <|> fail "Expected a double )) to end the $((..))"
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarArithmetic(c)))
    }

    fn read_dollar_brace_command_expansion(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("${")?;
        let piped = if self.char('|').is_ok() {
            Piped::Piped
        } else {
            // must be whitespace
            match self.peek() {
                Some(' ') | Some('\t') | Some('\n') | Some('\r') => {
                    self.bump();
                    Piped::Unpiped
                }
                _ => return Err(()),
            }
        };
        // Extract the content up to the matching `}` (brace-depth aware).
        let sub_start = self.pos();
        let mut raw = String::new();
        let mut depth = 1;
        while let Some(c) = self.peek() {
            if c == '{' {
                depth += 1;
            } else if c == '}' {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            self.bump();
            raw.push(c);
        }
        self.char('}').map_err(|_| ())?;
        let list = self.subparse_commands(&raw, sub_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_DollarBraceCommandExpansion { pipe: piped, list },
        ))
    }

    fn read_dollar_bracket(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$[")?;
        let c = self.read_arithmetic_contents()?;
        self.string("]")?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarBracket(c)))
    }

    fn read_dollar_expansion(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$(")?;
        let sub_start = self.pos();
        let raw = self.read_balanced_parens_until_close()?;
        let cmds = self.subparse_commands(&raw, sub_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarExpansion(cmds)))
    }

    fn read_dollar_braced(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("${")?;
        let word_start = self.pos();
        // read braced word: everything up to matching }. A bare `{` is an
        // ordinary literal char here (Parser.hs `readDollarBracedLiteral` stops
        // only at `bracedQuotable` = `}"$'` + backtick); so e.g. `${{var}`
        // parses the `${...}` as one expansion whose word is `{var`. Nesting is
        // introduced only by a `${` sub-expansion, so depth increments on `${`
        // (a `{` preceded by `$`), not on a bare `{`.
        let mut raw = String::new();
        let mut depth = 1;
        let mut prev = '\0';
        while let Some(c) = self.peek() {
            if c == '{' && prev == '$' {
                depth += 1;
            } else if c == '}' {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            self.bump();
            raw.push(c);
            prev = c;
        }
        self.char('}').map_err(|_| ())?;
        // Parse the braced content into parts so nested expansions (e.g.
        // `${x:+$y}`) become real child tokens and are seen by the analyses.
        let inner = self.make_braced_word(&raw, &word_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_DollarBraced {
                braced: true,
                op: inner,
            },
        ))
    }

    fn read_dollar_variable(&mut self) -> PResult<Token> {
        let start = self.pos();
        let pos = self.pos();
        self.char('$')?;
        // Position right after the `$`. Haskell's `wrapString` captures the
        // inner literal word's span starting after `char '$'`, so the inner
        // T_NormalWord/T_Literal begin here (the outer T_DollarBraced keeps the
        // `$`-anchored `start`).
        let word_pos = self.pos();
        // positional / special / regular
        if let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.bump();
                let word = self.make_literal_word(&c.to_string(), word_pos);
                let id = self.next_id_between(start, self.pos());
                if let Some(n) = self.peek() {
                    if n.is_ascii_digit() {
                        // `parseNoteAt pos` in Haskell is zero-width at the `$`.
                        self.note_at(
                            pos.clone(),
                            pos.clone(),
                            Severity::ErrorC,
                            1037,
                            "Braces are required for positionals over 9, e.g. ${10}.",
                        );
                    }
                }
                return Ok(Token::new(
                    id,
                    InnerToken::T_DollarBraced {
                        braced: false,
                        op: word,
                    },
                ));
            }
            if "$?!#-@*".contains(c) {
                self.bump();
                let word = self.make_literal_word(&c.to_string(), word_pos);
                let id = self.next_id_between(start, self.pos());
                return Ok(Token::new(
                    id,
                    InnerToken::T_DollarBraced {
                        braced: false,
                        op: word,
                    },
                ));
            }
            if c == '_' || c.is_ascii_alphabetic() {
                let name = self.read_variable_name()?;
                let word = self.make_literal_word(&name, word_pos);
                let id = self.next_id_between(start, self.pos());
                return Ok(Token::new(
                    id,
                    InnerToken::T_DollarBraced {
                        braced: false,
                        op: word,
                    },
                ));
            }
        }
        // lone '$'
        self.reset(self.mark_at_start(start.clone()));
        Err(())
    }

    fn read_variable_name(&mut self) -> PResult<String> {
        let mut s = String::new();
        match self.peek() {
            Some(c) if c == '_' || c.is_ascii_alphabetic() => {
                self.bump();
                s.push(c);
            }
            _ => return Err(()),
        }
        while let Some(c) = self.peek() {
            if c == '_' || c.is_ascii_alphanumeric() {
                self.bump();
                s.push(c);
            } else {
                break;
            }
        }
        Ok(s)
    }

    fn read_dollar_lonely(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('$')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal("$".to_string())))
    }

    fn read_dollar_single_quote(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$'")?;
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '\\' {
                self.bump();
                if let Some(n) = self.bump() {
                    s.push('\\');
                    s.push(n);
                }
                continue;
            }
            if c == '\'' {
                break;
            }
            self.bump();
            s.push(c);
        }
        self.char('\'')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarSingleQuoted(s)))
    }

    fn read_dollar_double_quote(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$\"")?;
        // reuse double-quote body
        let mut parts = Vec::new();
        loop {
            match self.peek() {
                Some('"') | None => break,
                Some('$') => {
                    if let Ok(t) = self.read_double_quoted_dollar() {
                        parts.push(t);
                        continue;
                    }
                    parts.push(self.read_double_literal_run()?);
                }
                Some('`') => parts.push(self.read_backticked(true)?),
                _ => parts.push(self.read_double_literal_run()?),
            }
        }
        self.char('"')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarDoubleQuoted(parts)))
    }

    // ---- helpers for subexpressions ---------------------------------------

    fn mark_at_start(&self, p: Position) -> Mark {
        // Reconstruct a Mark from a Position by scanning is expensive; instead we
        // never actually use this to move backward past consumed chars in a way
        // that matters. Return current mark (no-op safety).
        let _ = p;
        self.mark()
    }

    /// Parse the raw content of a `${...}` into a word whose parts include any
    /// nested expansions, single/double quotes and literal runs.
    fn make_braced_word(&mut self, raw: &str, start: &Position) -> Token {
        let mut sub = Parser::new(&self.filename, raw);
        sub.line = start.line;
        sub.col = start.column;
        sub.next_id = self.next_id;
        let parts = sub.read_braced_parts();
        for (k, v) in sub.positions.iter() {
            self.positions.insert(*k, v.clone());
        }
        self.notes.append(&mut sub.notes);
        self.problems.append(&mut sub.problems);
        self.next_id = sub.next_id;
        let wid = self.next_id_between(start.clone(), self.pos());
        Token::new(wid, InnerToken::T_NormalWord(parts))
    }

    fn read_braced_parts(&mut self) -> Vec<Token> {
        let mut parts = Vec::new();
        loop {
            match self.peek() {
                None => break,
                Some('\'') => match self.read_single_quoted() {
                    Ok(t) => parts.push(t),
                    Err(()) => parts.push(self.braced_literal_char()),
                },
                Some('"') => match self.read_double_quoted() {
                    Ok(t) => parts.push(t),
                    Err(()) => parts.push(self.braced_literal_char()),
                },
                Some('`') => match self.read_backticked(false) {
                    Ok(t) => parts.push(t),
                    Err(()) => parts.push(self.braced_literal_char()),
                },
                Some('$') => {
                    let m = self.mark();
                    match self.read_normal_dollar() {
                        Ok(t) => parts.push(t),
                        Err(()) => {
                            self.reset(m);
                            parts.push(self.braced_literal_char());
                        }
                    }
                }
                Some(_) => {
                    let start = self.pos();
                    let mut s = String::new();
                    while let Some(c) = self.peek() {
                        if "$`'\"".contains(c) {
                            break;
                        }
                        s.push(c);
                        self.bump();
                    }
                    if s.is_empty() {
                        break;
                    }
                    let id = self.next_id_between(start, self.pos());
                    parts.push(Token::new(id, InnerToken::T_Literal(s)));
                }
            }
        }
        parts
    }

    fn braced_literal_char(&mut self) -> Token {
        let start = self.pos();
        let c = self.bump().unwrap_or('\0');
        let id = self.next_id_between(start, self.pos());
        Token::new(id, InnerToken::T_Literal(c.to_string()))
    }

    fn make_literal_word(&mut self, s: &str, start: Position) -> Token {
        let lit_id = self.next_id_between(start.clone(), self.pos());
        let lit = Token::new(lit_id, InnerToken::T_Literal(s.to_string()));
        let wid = self.next_id_between(start, self.pos());
        Token::new(wid, InnerToken::T_NormalWord(vec![lit]))
    }

    // ---- arithmetic contents (faithful port of readArithmeticContents) -----
    //
    // Parses inline (like the Haskell parser) directly off the input stream,
    // producing the real `TA_*` tree. Binary/assignment/combo-op nodes carry the
    // *operator token's* span (matching `readComboOp`'s `id <- endSpan start`),
    // not the whole lhs..rhs range.

    /// `spacing` local to arithmetic: many (whitespace | "\\\n").
    fn arith_spacing(&mut self) {
        loop {
            let m = self.mark();
            if self.string("\\\n").is_ok() {
                continue;
            }
            self.reset(m);
            if self.whitespace().is_ok() {
                continue;
            }
            break;
        }
    }

    /// `readComboOp op token`: match one of `ops` (atomic), require it not be
    /// followed by another op char (`failIfIncompleteOp`), give it a span-only
    /// id, then eat trailing spacing. Returns `(id, matched-op)`.
    fn arith_read_combo_op(&mut self, ops: &[&str]) -> PResult<(Id, String)> {
        let start = self.pos();
        let outer = self.mark();
        let mut matched: Option<String> = None;
        for op in ops {
            let m = self.mark();
            if self.string(op).is_ok() {
                // failIfIncompleteOp = notFollowedBy2 (oneOf "&|<>=")
                if !matches!(self.peek(), Some(c) if "&|<>=".contains(c)) {
                    matched = Some((*op).to_string());
                    break;
                }
            }
            self.reset(m);
        }
        let op = match matched {
            Some(o) => o,
            None => {
                self.reset(outer);
                return Err(());
            }
        };
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok((id, op))
    }

    /// `readMinusOp`: binary `-`, but warn (SC1106) for `-lt`/`-gt`/&c.
    fn arith_read_minus_op(&mut self) -> PResult<(Id, String)> {
        let start = self.pos();
        let pos = self.pos();
        let outer = self.mark();
        // try (char '-' >> failIfIncompleteOp)
        if self.char('-').is_err() {
            self.reset(outer);
            return Err(());
        }
        if matches!(self.peek(), Some(c) if "&|<>=".contains(c)) {
            self.reset(outer);
            return Err(());
        }
        // optional lookAhead: -lt/-gt/... -> SC1106
        let look = self.mark();
        let alts = [
            ("lt", "<"),
            ("gt", ">"),
            ("le", "<="),
            ("ge", ">="),
            ("eq", "=="),
            ("ne", "!="),
        ];
        let mut found: Option<(&str, &str)> = None;
        for (s, alt) in alts {
            let m = self.mark();
            if self.string(s).is_ok() && self.spacing1().is_ok() {
                found = Some((s, alt));
                self.reset(m);
                break;
            }
            self.reset(m);
        }
        self.reset(look);
        if let Some((s, alt)) = found {
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1106,
                &format!("In arithmetic contexts, use {} instead of -{}", alt, s),
            );
        }
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok((id, "-".to_string()))
    }

    /// Generic `splitBy sub ops = chainl1 sub (readBinary ops)` producing
    /// left-associated `TA_Binary` nodes.
    fn arith_split_by(
        &mut self,
        sub: fn(&mut Self) -> PResult<Token>,
        ops: &[&str],
    ) -> PResult<Token> {
        let mut x = sub(self)?;
        loop {
            let m = self.mark();
            match self.arith_read_combo_op(ops) {
                Ok((id, op)) => {
                    // op consumed: term is now required (Parsec propagates failure)
                    let y = sub(self)?;
                    x = Token::new(id, InnerToken::TA_Binary { op, lhs: x, rhs: y });
                }
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        Ok(x)
    }

    /// Entry point: `readArithmeticContents = readSequence`.
    fn read_arithmetic_contents(&mut self) -> PResult<Token> {
        self.read_arith_sequence()
    }

    /// `readSequence`: comma-separated assignments -> `TA_Sequence`.
    fn read_arith_sequence(&mut self) -> PResult<Token> {
        self.arith_spacing();
        let start = self.pos();
        let mut list = Vec::new();
        let m = self.mark();
        match self.read_arith_assignment() {
            Ok(first) => {
                list.push(first);
                // many (char ',' >> spacing >> readAssignment)
                loop {
                    let mm = self.mark();
                    if self.char(',').is_ok() {
                        self.arith_spacing();
                        // sepBy1's inner is `sep >> p`; if sep consumed then p
                        // fails, Parsec propagates the failure.
                        let t = self.read_arith_assignment()?;
                        list.push(t);
                    } else {
                        self.reset(mm);
                        break;
                    }
                }
            }
            Err(()) => {
                self.reset(m);
            }
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::TA_Sequence(list)))
    }

    /// `readAssignment = chainr1 readTrinary readAssignmentOp` -> `TA_Assignment`.
    fn read_arith_assignment(&mut self) -> PResult<Token> {
        let x = self.read_arith_trinary()?;
        let m = self.mark();
        match self.arith_read_combo_op(&[
            "=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=", "&=", "^=", "|=",
        ]) {
            Ok((id, op)) => {
                // chainr1: right-recurse
                let y = self.read_arith_assignment()?;
                Ok(Token::new(
                    id,
                    InnerToken::TA_Assignment { op, lhs: x, rhs: y },
                ))
            }
            Err(()) => {
                self.reset(m);
                Ok(x)
            }
        }
    }

    /// `readTrinary` (?:) -> `TA_Trinary`.
    fn read_arith_trinary(&mut self) -> PResult<Token> {
        let x = self.read_arith_logical_or()?;
        let m = self.mark();
        let start = self.pos();
        if self.string("?").is_ok() {
            self.arith_spacing();
            let y = self.read_arith_trinary()?;
            // string ":" — required
            if self.string(":").is_err() {
                // consumed input; propagate failure faithfully
                return Err(());
            }
            self.arith_spacing();
            let z = self.read_arith_trinary()?;
            let id = self.next_id_between(start, self.pos());
            Ok(Token::new(
                id,
                InnerToken::TA_Trinary {
                    cond: x,
                    then: y,
                    els: z,
                },
            ))
        } else {
            self.reset(m);
            Ok(x)
        }
    }

    fn read_arith_logical_or(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_logical_and, &["||"])
    }
    fn read_arith_logical_and(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_bit_or, &["&&"])
    }
    fn read_arith_bit_or(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_bit_xor, &["|"])
    }
    fn read_arith_bit_xor(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_bit_and, &["^"])
    }
    fn read_arith_bit_and(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_equated, &["&"])
    }
    fn read_arith_equated(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_compared, &["==", "!="])
    }
    fn read_arith_compared(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_shift, &["<=", ">=", "<", ">"])
    }
    fn read_arith_shift(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_addition, &["<<", ">>"])
    }

    /// `readAddition = chainl1 readMultiplication (readBinary ["+"] <|> readMinusOp)`.
    fn read_arith_addition(&mut self) -> PResult<Token> {
        let mut x = self.read_arith_multiplication()?;
        loop {
            let m = self.mark();
            // try "+" combo op, else minus op
            let opres = match self.arith_read_combo_op(&["+"]) {
                Ok(r) => Some(r),
                Err(()) => {
                    self.reset(m);
                    match self.arith_read_minus_op() {
                        Ok(r) => Some(r),
                        Err(()) => {
                            self.reset(m);
                            None
                        }
                    }
                }
            };
            match opres {
                Some((id, op)) => {
                    let y = self.read_arith_multiplication()?;
                    x = Token::new(id, InnerToken::TA_Binary { op, lhs: x, rhs: y });
                }
                None => break,
            }
        }
        Ok(x)
    }

    fn read_arith_multiplication(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_exponential, &["*", "/", "%"])
    }
    fn read_arith_exponential(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_any_negated, &["**"])
    }

    /// `readAnyNegated = readNegated <|> readAnySigned`.
    fn read_arith_any_negated(&mut self) -> PResult<Token> {
        let m = self.mark();
        if let Ok(t) = self.read_arith_negated() {
            return Ok(t);
        }
        self.reset(m);
        self.read_arith_any_signed()
    }

    /// `readNegated`: `! | ~` prefix -> `TA_Unary`.
    fn read_arith_negated(&mut self) -> PResult<Token> {
        let start = self.pos();
        let op = self.one_of("!~")?;
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        let x = self.read_arith_any_negated()?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: op.to_string(),
                operand: x,
            },
        ))
    }

    /// `readAnySigned = readSigned <|> readAnycremented`.
    fn read_arith_any_signed(&mut self) -> PResult<Token> {
        let m = self.mark();
        if let Ok(t) = self.read_arith_signed() {
            return Ok(t);
        }
        self.reset(m);
        self.read_arith_anycremented()
    }

    /// `readSigned`: unary `+`/`-` (not `++`/`--`) -> `TA_Unary`.
    fn read_arith_signed(&mut self) -> PResult<Token> {
        let start = self.pos();
        let outer = self.mark();
        let mut got: Option<char> = None;
        for c in ['+', '-'] {
            let m = self.mark();
            if self.char(c).is_ok() {
                // notFollowedBy2 (char c)
                if self.peek() != Some(c) {
                    self.arith_spacing();
                    got = Some(c);
                    break;
                }
            }
            self.reset(m);
        }
        let op = match got {
            Some(c) => c,
            None => {
                self.reset(outer);
                return Err(());
            }
        };
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        let x = self.read_arith_anycremented()?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: op.to_string(),
                operand: x,
            },
        ))
    }

    /// `readAnycremented = readNormalOrPostfixIncremented <|> readPrefixIncremented`.
    fn read_arith_anycremented(&mut self) -> PResult<Token> {
        let m = self.mark();
        if let Ok(t) = self.read_arith_normal_or_postfix() {
            return Ok(t);
        }
        self.reset(m);
        self.read_arith_prefix_incremented()
    }

    /// `readPrefixIncremented`: `++x`/`--x` -> `TA_Unary` with op `"++|"`/`"--|"`.
    fn read_arith_prefix_incremented(&mut self) -> PResult<Token> {
        let start = self.pos();
        let m = self.mark();
        let op = if self.string("++").is_ok() {
            "++"
        } else {
            self.reset(m);
            if self.string("--").is_ok() {
                "--"
            } else {
                self.reset(m);
                return Err(());
            }
        };
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        let x = self.read_arith_term()?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: format!("{}|", op),
                operand: x,
            },
        ))
    }

    /// `readNormalOrPostfixIncremented`: term, optional trailing `++`/`--`
    /// -> `TA_Unary` with op `"|++"`/`"|--"`.
    fn read_arith_normal_or_postfix(&mut self) -> PResult<Token> {
        let x = self.read_arith_term()?;
        self.arith_spacing();
        let start = self.pos();
        let m = self.mark();
        let op = if self.string("++").is_ok() {
            Some("++")
        } else {
            self.reset(m);
            if self.string("--").is_ok() {
                Some("--")
            } else {
                self.reset(m);
                None
            }
        };
        match op {
            Some(op) => {
                let id = self.next_id_between(start, self.pos());
                self.arith_spacing();
                Ok(Token::new(
                    id,
                    InnerToken::TA_Unary {
                        op: format!("|{}", op),
                        operand: x,
                    },
                ))
            }
            None => Ok(x),
        }
    }

    /// `readArithTerm = readGroup <|> readVariable <|> readExpansion`.
    fn read_arith_term(&mut self) -> PResult<Token> {
        let m = self.mark();
        if let Ok(t) = self.read_arith_group() {
            return Ok(t);
        }
        self.reset(m);
        if let Ok(t) = self.read_arith_variable() {
            return Ok(t);
        }
        self.reset(m);
        self.read_arith_expansion()
    }

    /// `readGroup`: `( sequence )` -> `TA_Parenthesis`.
    fn read_arith_group(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('(')?;
        let s = self.read_arith_sequence()?;
        self.char(')')?;
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok(Token::new(id, InnerToken::TA_Parenthesis(s)))
    }

    /// `readVariable`: name + array indices -> `TA_Variable`.
    fn read_arith_variable(&mut self) -> PResult<Token> {
        let start = self.pos();
        let name = self.read_variable_name()?;
        let mut indices = Vec::new();
        loop {
            let m = self.mark();
            match self.read_arith_array_index() {
                Ok(t) => indices.push(t),
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok(Token::new(id, InnerToken::TA_Variable { name, indices }))
    }

    /// `readArrayIndex` (arithmetic-local): `[ arith ]` -> `T_UnparsedIndex`
    /// storing the source position and the raw consumed text. The inner
    /// arithmetic parse is used only to find the extent (like `readStringForParser`
    /// via `inSeparateContext`); its ids/notes are rolled back.
    fn read_arith_array_index(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('[')?;
        let pos = self.pos();
        let idx0 = self.idx;
        let save_next_id = self.next_id;
        let save_notes = self.notes.len();
        let save_problems = self.problems.len();
        // Consume what readArithmeticContents would, discarding its output.
        let _ = self.read_arithmetic_contents();
        let raw: String = self.input[idx0..self.idx].iter().collect();
        // Roll back the separate-context allocations/notes.
        self.next_id = save_next_id;
        self.notes.truncate(save_notes);
        self.problems.truncate(save_problems);
        self.positions.retain(|k, _| k.0 < save_next_id);
        self.char(']')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_UnparsedIndex { pos, str: raw },
        ))
    }

    /// `readExpansion`: `$`-expansions / quotes / literals -> `TA_Expansion`.
    fn read_arith_expansion(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut pieces = Vec::new();
        loop {
            let m = self.mark();
            let piece = match self.peek() {
                Some('\'') => self.read_single_quoted(),
                Some('"') => self.read_double_quoted(),
                Some('$') => self.read_normal_dollar(),
                Some('`') => self.read_backticked(false),
                Some('{') => self.read_braced(),
                Some('#') => {
                    let s = self.pos();
                    self.bump();
                    let lid = self.next_id_between(s, self.pos());
                    Ok(Token::new(lid, InnerToken::T_Literal("#".to_string())))
                }
                _ => self.read_normal_literal("+-*/=%^,]?:"),
            };
            match piece {
                Ok(t) => pieces.push(t),
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        if pieces.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok(Token::new(id, InnerToken::TA_Expansion(pieces)))
    }

    fn read_balanced_parens_until_close(&mut self) -> PResult<String> {
        // consumes up to and including the matching ')', returns inner raw text
        let mut raw = String::new();
        let mut depth = 1;
        while let Some(c) = self.peek() {
            if c == '(' {
                depth += 1;
            } else if c == ')' {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            self.bump();
            raw.push(c);
        }
        self.char(')')?;
        Ok(raw)
    }

    /// Subparse a fragment as a compound list, in a nested parser sharing the id
    /// space and position/note collections. The sub-parser starts at `start`'s
    /// absolute line/column so inner-token positions are correct in the original
    /// script (the raw text is a verbatim, offset-preserving substring for
    /// `$(...)`, `<(...)` and backticks).
    fn subparse_commands(&mut self, raw: &str, start: Position) -> Vec<Token> {
        let mut sub = Parser::new(&self.filename, raw);
        sub.line = start.line;
        sub.col = start.column;
        sub.next_id = self.next_id;
        let cmds = sub.read_compound_list_or_empty();
        // merge
        self.next_id = sub.next_id;
        for (k, v) in sub.positions {
            self.positions.entry(k).or_insert(v);
        }
        self.notes.extend(sub.notes);
        self.problems.extend(sub.problems);
        cmds
    }
}

// ============================================================================
// Commands, redirections, control flow, script entry
// ============================================================================

impl Parser {
    fn empty_literal(&mut self) -> Token {
        let p = self.pos();
        let id = self.next_id_between(p.clone(), p);
        Token::new(id, InnerToken::T_Literal(String::new()))
    }

    fn read_shebang(&mut self) -> Option<Token> {
        // #! (optionally with spaces / swapped), then rest of first line.
        let start = self.pos();
        let m = self.mark();
        let ok = if self.string("#!").is_ok() {
            true
        } else {
            self.reset(m);
            // "#! " with spaces already covered; try "# !"? keep simple.
            false
        };
        if !ok {
            self.reset(m);
            return None;
        }
        while self.line_whitespace().is_ok() {}
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '\r' || c == '\n' {
                break;
            }
            self.bump();
            s.push(c);
        }
        let id = self.next_id_between(start, self.pos());
        let _ = self.char('\r');
        let _ = self.char('\n');
        Some(Token::new(id, InnerToken::T_Literal(s)))
    }

    // ---- separators --------------------------------------------------------

    fn read_separator_op(&mut self) -> Option<char> {
        match self.peek() {
            Some('&') if self.peek_at(1) != Some('&') => {
                self.bump();
                Some('&')
            }
            Some(';') if self.peek_at(1) != Some(';') => {
                self.bump();
                Some(';')
            }
            _ => None,
        }
    }

    /// Returns (separator_char, (start,end)) or None.
    fn read_separator(&mut self) -> Option<(char, (Position, Position))> {
        let start = self.pos();
        if let Some(op) = self.read_separator_op() {
            let end = self.pos();
            self.line_break();
            Some((op, (start, end)))
        } else {
            // newline separator
            let m = self.mark();
            self.spacing();
            if self.peek() == Some('\n') || self.peek() == Some('\r') {
                let s2 = self.pos();
                self.newline_list();
                let e2 = self.pos();
                Some(('\n', (s2, e2)))
            } else {
                self.reset(m);
                None
            }
        }
    }

    fn newline_list(&mut self) {
        loop {
            let m = self.mark();
            self.spacing();
            if self.linefeed().is_ok() {
                continue;
            }
            // lone CR?
            if self.char('\r').is_ok() && self.peek() != Some('\n') {
                continue;
            }
            self.reset(m);
            break;
        }
    }

    // ---- terms / and-or / pipelines ---------------------------------------

    fn read_compound_list_or_empty(&mut self) -> Vec<Token> {
        self.allspacing();
        self.read_term().unwrap_or_default()
    }

    fn read_term(&mut self) -> Option<Vec<Token>> {
        self.allspacing();
        let first = self.read_and_or().ok()?;
        Some(self.read_term_more(first))
    }

    fn read_term_more(&mut self, current: Token) -> Vec<Token> {
        if let Some((sep, (start, end))) = self.read_separator() {
            let id = self.next_id_between(start, end);
            let node = if sep == '&' {
                Token::new(id, InnerToken::T_Backgrounded(current))
            } else {
                current
            };
            // try to read another and-or
            let m = self.mark();
            match self.read_and_or() {
                Ok(next) => {
                    let mut v = vec![node];
                    v.extend(self.read_term_more(next));
                    v
                }
                Err(()) => {
                    self.reset(m);
                    vec![node]
                }
            }
        } else {
            vec![current]
        }
    }

    fn read_and_or(&mut self) -> PResult<Token> {
        let ann_start = self.pos();
        let annotations = self.read_annotations();
        self.allspacing_no_newline();
        let mut left = self.read_pipeline()?;
        loop {
            let m = self.mark();
            self.spacing();
            let op_start = self.pos();
            let op = if self.peek() == Some('&') && self.peek_at(1) == Some('&') {
                self.bump();
                self.bump();
                Some(true)
            } else if self.peek() == Some('|') && self.peek_at(1) == Some('|') {
                self.bump();
                self.bump();
                Some(false)
            } else {
                None
            };
            match op {
                Some(is_and) => {
                    // T_AndIf/T_OrIf inherit the operator token's span (matching
                    // ShellCheck's g_AND_IF / g_OR_IF ids), so checks that emit on
                    // the node land on the `&&` / `||`.
                    let op_end = self.pos();
                    self.line_break();
                    let right = self.read_pipeline()?;
                    let id = self.next_id_between(op_start, op_end);
                    left = if is_and {
                        Token::new(
                            id,
                            InnerToken::T_AndIf {
                                lhs: left,
                                rhs: right,
                            },
                        )
                    } else {
                        Token::new(
                            id,
                            InnerToken::T_OrIf {
                                lhs: left,
                                rhs: right,
                            },
                        )
                    };
                }
                None => {
                    self.reset(m);
                    break;
                }
            }
        }
        if annotations.is_empty() {
            Ok(left)
        } else {
            let end = self.span_for(left.id()).1;
            let id = self.next_id_between(ann_start, end);
            Ok(Token::new(
                id,
                InnerToken::T_Annotation {
                    annotations,
                    token: left,
                },
            ))
        }
    }

    fn allspacing_no_newline(&mut self) {
        self.spacing();
    }

    fn read_pipeline(&mut self) -> PResult<Token> {
        self.read_banged()
    }

    fn read_banged(&mut self) -> PResult<Token> {
        let m = self.mark();
        // '!' as a word by itself
        if self.peek() == Some('!') {
            // ensure followed by space (bang keyword)
            let after = self.peek_at(1);
            if after == Some(' ') || after == Some('\t') {
                let start = self.pos();
                self.bump();
                let bang_id = self.next_id_between(start, self.pos());
                self.spacing();
                let inner = self.read_banged()?;
                return Ok(Token::new(bang_id, InnerToken::T_Banged(inner)));
            }
        }
        self.reset(m);
        self.read_pipe_sequence()
    }

    /// `readBanged readCommand`: a single pipeline stage, which may itself be
    /// prefixed by one or more `!` (e.g. `true | ! true`, `! ! true`). Unlike
    /// `read_banged`, the fallback reads a single command, not a whole pipe
    /// sequence, so it can be used per-stage inside `read_pipe_sequence`.
    fn read_banged_command(&mut self) -> PResult<Token> {
        let m = self.mark();
        if self.peek() == Some('!') {
            let after = self.peek_at(1);
            if after == Some(' ') || after == Some('\t') {
                let start = self.pos();
                self.bump();
                let bang_id = self.next_id_between(start, self.pos());
                self.spacing();
                let inner = self.read_banged_command()?;
                return Ok(Token::new(bang_id, InnerToken::T_Banged(inner)));
            }
        }
        self.reset(m);
        self.read_command()
    }

    fn read_pipe_sequence(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut cmds = Vec::new();
        let mut pipes = Vec::new();
        let first = self.read_banged_command()?;
        cmds.push(first);
        loop {
            let m = self.mark();
            self.spacing();
            if self.peek() == Some('|') && self.peek_at(1) != Some('|') {
                let pstart = self.pos();
                self.bump();
                let mut op = String::from("|");
                if self.char('&').is_ok() {
                    op.push('&');
                }
                let pid = self.next_id_between(pstart, self.pos());
                pipes.push(Token::new(pid, InnerToken::T_Pipe(op)));
                self.spacing();
                self.line_break();
                match self.read_banged_command() {
                    Ok(c) => cmds.push(c),
                    Err(()) => {
                        self.reset(m);
                        break;
                    }
                }
            } else {
                self.reset(m);
                break;
            }
        }
        self.spacing();
        if cmds.len() == 1 && pipes.is_empty() {
            // Still wrap in a pipeline for uniformity? ShellCheck wraps single
            // command in T_Pipeline [] [cmd]. Yes.
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_Pipeline {
                separators: pipes,
                commands: cmds,
            },
        ))
    }

    fn read_command(&mut self) -> PResult<Token> {
        // Reserved words that close a compound list must not be read as command
        // names (mirrors `readPipeline`'s `unexpecting readKeyword`). Without
        // this, e.g. `for..do..done`'s body swallows `done` and the loop fails.
        if self.at_command_terminator() {
            return Err(());
        }
        if let Ok(t) = self.read_compound_command() {
            return Ok(t);
        }
        if let Ok(t) = self.read_condition_command() {
            return Ok(t);
        }
        if let Ok(t) = self.read_coproc() {
            return Ok(t);
        }
        self.read_simple_command()
    }

    /// Faithful port of `readCoProc` (Parser.hs). `coproc` + spacing, then either
    /// a compound form (optional name word + compound command body) or a simple
    /// form (a simple-command body). The body is wrapped in `T_CoProcBody`.
    fn read_coproc(&mut self) -> PResult<Token> {
        let start = self.pos();
        let m = self.mark();
        // try { string "coproc"; spacing1 }
        if self.string("coproc").is_err() {
            self.reset(m);
            return Err(());
        }
        if self.spacing1().is_err() {
            self.reset(m);
            return Err(());
        }
        // choice [ try readCompoundCoProc, readSimpleCoProc ]
        let mc = self.mark();
        if let Ok(t) = self.read_compound_coproc(start.clone()) {
            return Ok(t);
        }
        self.reset(mc);
        self.read_simple_coproc(start)
    }

    fn read_compound_coproc(&mut self, start: Position) -> PResult<Token> {
        // notFollowedBy2 readAssignmentWord
        let ma = self.mark();
        let is_assign = self.read_assignment_word().is_ok();
        self.reset(ma);
        if is_assign {
            return Err(());
        }
        // choice [ try (body only, no name), (name word + body) ]
        let m1 = self.mark();
        if let Ok(body) = self.read_coproc_body(true) {
            let id = self.next_id_between(start.clone(), self.pos());
            return Ok(Token::new(id, InnerToken::T_CoProc { name: None, body }));
        }
        self.reset(m1);
        let var = self.read_normal_word()?;
        self.spacing();
        let body = self.read_coproc_body(true)?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_CoProc {
                name: Some(var),
                body,
            },
        ))
    }

    fn read_simple_coproc(&mut self, start: Position) -> PResult<Token> {
        let body = self.read_coproc_body(false)?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_CoProc { name: None, body }))
    }

    /// `readBody parser`: run `parser`, wrap its result in `T_CoProcBody`.
    fn read_coproc_body(&mut self, compound: bool) -> PResult<Token> {
        let start = self.pos();
        let body = if compound {
            self.read_compound_command()?
        } else {
            self.read_simple_command()?
        };
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_CoProcBody(body)))
    }

    /// True if the upcoming token is a reserved word/operator that terminates a
    /// command list (`then else elif fi do done esac`, `}`).
    fn at_command_terminator(&self) -> bool {
        for kw in ["then", "else", "elif", "fi", "do", "done", "esac"] {
            if self.keyword_ahead(kw) {
                return true;
            }
        }
        // A bare `}` closing a brace group (word-bounded).
        if self.peek() == Some('}') && self.is_word_boundary_after(1) {
            return true;
        }
        false
    }

    // ---- compound commands -------------------------------------------------

    fn read_compound_command(&mut self) -> PResult<Token> {
        let c = self.peek();
        let m = self.mark();
        let cmd = match c {
            Some('(') if self.peek_at(1) == Some('(') => {
                // readAmbiguous "((" readArithmeticExpression readSubshell
                let mm = self.mark();
                match self.read_arithmetic_command() {
                    Ok(t) => Ok(t),
                    Err(()) => {
                        self.reset(mm);
                        self.read_subshell()
                    }
                }
            }
            Some('(') => self.read_subshell(),
            Some('{') if self.is_word_boundary_after(1) => self.read_brace_group(),
            _ => {
                if self.keyword_ahead("if") {
                    self.read_if_clause()
                } else if self.keyword_ahead("while") {
                    self.read_while_clause()
                } else if self.keyword_ahead("until") {
                    self.read_until_clause()
                } else if self.keyword_ahead("for") {
                    self.read_for_clause()
                } else if self.keyword_ahead("case") {
                    self.read_case_clause()
                } else if self.keyword_ahead("select") {
                    self.read_select_clause()
                } else if self.keyword_ahead("function") {
                    self.read_function_def()
                } else if self.peek() == Some('(') && self.peek_at(1) == Some('(') {
                    let mm = self.mark();
                    match self.read_arithmetic_command() {
                        Ok(t) => Ok(t),
                        Err(()) => {
                            self.reset(mm);
                            self.read_subshell()
                        }
                    }
                } else if self.string_peek("@test ") {
                    self.read_bats_test()
                } else if self.looks_like_posix_function() {
                    self.read_posix_function()
                } else {
                    Err(())
                }
            }
        };
        match cmd {
            Ok(t) => {
                // Every compound command is wrapped in T_Redirecting (with a
                // possibly-empty redirect list), exactly as ShellCheck's
                // readCompoundCommand. This keeps parent-path depth (and thus
                // fix precedence) identical to the oracle.
                let redirs = self.read_redirect_list();
                let (s, _) = self.span_for(t.id());
                let e = self.pos();
                let id = self.next_id_between(s, e);
                Ok(Token::new(id, InnerToken::T_Redirecting { redirs, cmd: t }))
            }
            Err(()) => {
                self.reset(m);
                Err(())
            }
        }
    }

    fn is_word_boundary_after(&self, n: usize) -> bool {
        match self.peek_at(n) {
            None => true,
            Some(c) => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ';',
        }
    }

    /// True if the upcoming token is exactly `kw` followed by a word boundary.
    fn keyword_ahead(&self, kw: &str) -> bool {
        let chars: Vec<char> = kw.chars().collect();
        for (i, &ch) in chars.iter().enumerate() {
            if self.peek_at(i) != Some(ch) {
                return false;
            }
        }
        match self.peek_at(chars.len()) {
            None => true,
            Some(c) => !(c == '_' || c.is_ascii_alphanumeric()),
        }
    }

    fn consume_keyword(&mut self, kw: &str) -> PResult<()> {
        if self.keyword_ahead(kw) {
            for _ in 0..kw.chars().count() {
                self.bump();
            }
            Ok(())
        } else {
            Err(())
        }
    }

    fn read_subshell(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('(')?;
        let list = self.read_compound_list_or_empty();
        self.allspacing();
        self.char(')')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Subshell(list)))
    }

    fn read_brace_group(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('{')?;
        self.allspacing();
        let list = self.read_compound_list_or_empty();
        self.allspacing();
        self.consume_keyword("}")
            .or_else(|_| self.char('}').map(|_| ()))?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_BraceGroup(list)))
    }

    fn read_if_clause(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("if")?;
        let mut clauses: Vec<IfClause> = Vec::new();
        let cond = self.read_condition_list()?;
        self.allspacing();
        self.consume_keyword("then")?;
        let body = self.read_compound_list_or_empty();
        clauses.push((cond, body));
        loop {
            self.allspacing();
            if self.keyword_ahead("elif") {
                self.consume_keyword("elif")?;
                let c = self.read_condition_list()?;
                self.allspacing();
                self.consume_keyword("then")?;
                let b = self.read_compound_list_or_empty();
                clauses.push((c, b));
            } else {
                break;
            }
        }
        self.allspacing();
        let elses = if self.keyword_ahead("else") {
            self.consume_keyword("else")?;
            self.read_compound_list_or_empty()
        } else {
            Vec::new()
        };
        self.allspacing();
        self.consume_keyword("fi")?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_IfExpression { clauses, elses },
        ))
    }

    fn read_condition_list(&mut self) -> PResult<Vec<Token>> {
        self.allspacing();
        let first = self.read_and_or()?;
        Ok(self.read_term_more(first))
    }

    fn read_while_clause(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("while")?;
        let cond = self.read_condition_list()?;
        self.allspacing();
        self.consume_keyword("do")?;
        let body = self.read_compound_list_or_empty();
        self.allspacing();
        self.consume_keyword("done")?;
        // ShellCheck's `g_Done` is `tryWordToken "done" .. \`thenSkip\` spacing`, so
        // the loop's span extends over the line-whitespace following `done` (a
        // trailing redirect starts after it). Without this the node is one column
        // short of the oracle. `spacing` is line-whitespace only (no newlines).
        self.spacing();
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_WhileExpression {
                condition: cond,
                body,
            },
        ))
    }

    fn read_until_clause(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("until")?;
        let cond = self.read_condition_list()?;
        self.allspacing();
        self.consume_keyword("do")?;
        let body = self.read_compound_list_or_empty();
        self.allspacing();
        self.consume_keyword("done")?;
        // See `read_while_clause`: `g_Done` consumes trailing line-whitespace, so
        // the T_UntilExpression span reaches the start of any trailing redirect.
        self.spacing();
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_UntilExpression {
                condition: cond,
                body,
            },
        ))
    }

    fn read_for_clause(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("for")?;
        // ShellCheck reuses the `for` keyword id for the whole T_ForIn/T_ForArithmetic
        // node, so SC2034 (and others) point at `for`, not the entire loop.
        let for_end = self.pos();
        self.spacing();
        // arithmetic for: for ((init; cond; step))
        if self.peek() == Some('(') && self.peek_at(1) == Some('(') {
            // readArithmeticDelimiter '(': "(" spacing "(" (lenient about spaces)
            self.char('(')?;
            self.arith_spacing();
            self.char('(')?;
            let init = self.read_arithmetic_contents()?;
            self.char(';')?;
            self.arith_spacing();
            let cond = self.read_arithmetic_contents()?;
            self.char(';')?;
            self.arith_spacing();
            let step = self.read_arithmetic_contents()?;
            self.arith_spacing();
            // readArithmeticDelimiter ')': ")" spacing ")"
            self.char(')')?;
            self.arith_spacing();
            self.char(')')?;
            self.spacing();
            // optional sequential separator, then do..done (or brace group)
            self.allspacing();
            let _ = self.char(';');
            self.allspacing();
            self.consume_keyword("do")?;
            let body = self.read_compound_list_or_empty();
            self.allspacing();
            self.consume_keyword("done")?;
            let id = self.next_id_between(start, for_end.clone());
            return Ok(Token::new(
                id,
                InnerToken::T_ForArithmetic {
                    init,
                    cond,
                    step,
                    body,
                },
            ));
        }
        let var = self.read_variable_name()?;
        self.spacing();
        let mut items = Vec::new();
        let mut is_in = false;
        if self.keyword_ahead("in") {
            self.consume_keyword("in")?;
            is_in = true;
            self.spacing();
            loop {
                self.spacing();
                if self.peek() == Some(';')
                    || self.peek() == Some('\n')
                    || self.peek() == Some('\r')
                {
                    break;
                }
                match self.read_normal_word() {
                    Ok(w) => items.push(w),
                    Err(()) => break,
                }
            }
        }
        let _ = self.char(';');
        self.allspacing();
        self.consume_keyword("do")?;
        let body = self.read_compound_list_or_empty();
        self.allspacing();
        self.consume_keyword("done")?;
        let id = self.next_id_between(start, for_end);
        let _ = is_in;
        Ok(Token::new(id, InnerToken::T_ForIn { var, items, body }))
    }

    /// `readBatsTest`: `@test <name> { ... }`, where <name> is everything on the
    /// line up to the last ` {`.
    fn read_bats_test(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("@test ")?;
        self.spacing();
        // name = current line up to the last " {"
        let mut j = self.idx;
        while matches!(self.input.get(j), Some(&c) if c != '\n') {
            j += 1;
        }
        let line: String = self.input[self.idx..j].iter().collect();
        let brace_pos = line.rfind(" {").ok_or(())?;
        let name = line[..brace_pos].trim_end().to_string();
        // consume exactly name.chars().count() chars
        for _ in 0..name.chars().count() {
            self.bump();
        }
        self.spacing();
        let body = self.read_brace_group()?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_BatsTest { name, body }))
    }

    fn read_select_clause(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("select")?;
        // ShellCheck reuses the `select` keyword id for the whole T_SelectIn node.
        let sel_end = self.pos();
        self.spacing();
        let var = self.read_variable_name()?;
        self.spacing();
        let mut items = Vec::new();
        if self.keyword_ahead("in") {
            self.consume_keyword("in")?;
            self.spacing();
            loop {
                self.spacing();
                if matches!(self.peek(), Some(';') | Some('\n') | Some('\r') | None) {
                    break;
                }
                match self.read_normal_word() {
                    Ok(w) => items.push(w),
                    Err(()) => break,
                }
            }
        }
        let _ = self.char(';');
        self.allspacing();
        self.consume_keyword("do")?;
        let body = self.read_compound_list_or_empty();
        self.allspacing();
        self.consume_keyword("done")?;
        let id = self.next_id_between(start, sel_end);
        Ok(Token::new(id, InnerToken::T_SelectIn { var, items, body }))
    }

    fn read_case_clause(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("case")?;
        self.spacing();
        let word = self.read_normal_word()?;
        self.allspacing();
        self.consume_keyword("in")?;
        self.allspacing();
        let mut cases: Vec<CaseClause> = Vec::new();
        loop {
            self.allspacing();
            if self.keyword_ahead("esac") {
                break;
            }
            // optional leading (
            let _ = self.char('(');
            let mut pats = Vec::new();
            loop {
                self.spacing();
                match self.read_normal_word() {
                    Ok(w) => pats.push(w),
                    Err(()) => break,
                }
                self.spacing();
                if self.char('|').is_ok() {
                    continue;
                } else {
                    break;
                }
            }
            self.spacing();
            self.char(')')?;
            let body = self.read_case_body();
            // Mirrors Parser.hs readCaseSeparator: the `;;` arm and the
            // no-separator-before-esac arm both yield CaseBreak. The arms are
            // NOT interchangeable — the `;;` condition consumes the separator
            // while the fallback consumes nothing — so they must stay distinct.
            #[allow(clippy::if_same_then_else)]
            let ctype = if self.string(";;&").is_ok() {
                CaseType::CaseContinue
            } else if self.string(";&").is_ok() {
                CaseType::CaseFallThrough
            } else if self.string(";;").is_ok() {
                CaseType::CaseBreak
            } else {
                CaseType::CaseBreak
            };
            cases.push((ctype, pats, body));
        }
        self.allspacing();
        self.consume_keyword("esac")?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_CaseExpression { word, cases }))
    }

    /// True at a case-clause terminator: `;;`, `;&`, or `;;&`.
    fn at_case_terminator(&self) -> bool {
        self.peek() == Some(';') && matches!(self.peek_at(1), Some(';') | Some('&'))
    }

    fn read_case_body(&mut self) -> Vec<Token> {
        // A compound list, stopping at a clause terminator (;;/;&/;;&) or esac.
        // A plain `;` (not part of a terminator) is a statement separator.
        self.allspacing();
        if self.keyword_ahead("esac") || self.at_case_terminator() {
            return Vec::new();
        }
        let first = match self.read_and_or() {
            Ok(f) => f,
            Err(()) => return Vec::new(),
        };
        let mut out = vec![first];
        loop {
            let m = self.mark();
            self.spacing();
            if self.at_case_terminator() {
                self.reset(m);
                break;
            }
            if self.read_separator().is_some() {
                self.allspacing();
                if self.at_case_terminator() || self.keyword_ahead("esac") {
                    break;
                }
                match self.read_and_or() {
                    Ok(n) => out.push(n),
                    Err(()) => {
                        self.reset(m);
                        break;
                    }
                }
            } else {
                self.reset(m);
                break;
            }
        }
        out
    }

    /// Non-consuming lookahead for a POSIX function definition:
    /// `name` (spaces) `(` (spaces) `)`.
    fn looks_like_posix_function(&self) -> bool {
        let mut i = self.idx;
        let is_start = |c: char| c.is_ascii_alphanumeric() || "_:+?-./^@,".contains(c);
        let is_cont = |c: char| c.is_ascii_alphanumeric() || "_#:+?-./^@,".contains(c);
        match self.input.get(i) {
            Some(&c) if is_start(c) => i += 1,
            _ => return false,
        }
        let name_start = self.idx;
        while matches!(self.input.get(i), Some(&c) if is_cont(c)) {
            i += 1;
        }
        let name: String = self.input[name_start..i].iter().collect();
        if name == "time" {
            return false;
        }
        while matches!(self.input.get(i), Some(' ') | Some('\t')) {
            i += 1;
        }
        if self.input.get(i) != Some(&'(') {
            return false;
        }
        i += 1;
        while matches!(self.input.get(i), Some(' ') | Some('\t')) {
            i += 1;
        }
        self.input.get(i) == Some(&')')
    }

    /// `readWithoutFunction`: `name ( )` then a brace-group or subshell body.
    fn read_posix_function(&mut self) -> PResult<Token> {
        let start = self.pos();
        let name = self.read_function_name()?;
        if name == "time" {
            return Err(());
        }
        self.spacing();
        self.char('(')?;
        self.spacing();
        self.char(')')?;
        self.allspacing();
        let body = if self.peek() == Some('{') {
            self.read_brace_group()?
        } else if self.peek() == Some('(') {
            self.read_subshell()?
        } else {
            return Err(());
        };
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_Function {
                keyword: false,
                parens: true,
                name,
                body,
            },
        ))
    }

    fn read_function_def(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("function")?;
        self.spacing();
        let name = self.read_function_name()?;
        self.spacing();
        // optional ()
        let has_parens = if self.char('(').is_ok() {
            self.spacing();
            self.char(')')?;
            true
        } else {
            false
        };
        self.allspacing();
        let body = self.read_command()?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_Function {
                keyword: true,
                parens: has_parens,
                name,
                body,
            },
        ))
    }

    fn read_function_name(&mut self) -> PResult<String> {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || "_:+?-./^@,".contains(c) {
                self.bump();
                s.push(c);
            } else {
                break;
            }
        }
        if s.is_empty() { Err(()) } else { Ok(s) }
    }

    fn read_arithmetic_command(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("((")?;
        let c = self.read_arithmetic_contents()?;
        self.string("))")?;
        self.arith_spacing();
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Arithmetic(c)))
    }

    // ---- simple command ----------------------------------------------------

    fn read_simple_command(&mut self) -> PResult<Token> {
        let prefix = self.read_cmd_prefix();
        self.spacing();
        let cmd = self.read_cmd_name();
        if prefix.is_empty() && cmd.is_none() {
            return Err(());
        }
        let mut suffix = Vec::new();
        if let Some(ref c) = cmd {
            // `validateCommand` (Parser.hs): SC1127 when the command word looks
            // like a C-style comment (`//` or `/* ... `).
            self.validate_command_comment(c);
            // Determine whether this is a modifier command whose arguments are
            // parsed as assignments (readModifierSuffix). For `builtin`, use the
            // first argument's name.
            let name = Self::command_literal_name(c);
            let effective = if name.as_deref() == Some("builtin") {
                let m = self.mark();
                self.spacing();
                let peeked = self
                    .read_normal_word()
                    .ok()
                    .and_then(|w| Self::command_literal_name(&w));
                self.reset(m);
                peeked
            } else {
                name
            };
            let is_modifier = matches!(
                effective.as_deref(),
                Some("declare")
                    | Some("export")
                    | Some("local")
                    | Some("readonly")
                    | Some("typeset")
            );
            if effective.as_deref() == Some("let") {
                suffix = self.read_let_suffix();
            } else if effective.as_deref() == Some("time") {
                suffix = self.read_time_suffix();
            } else {
                suffix = self.read_cmd_suffix(is_modifier);
            }
        }
        // assemble
        let mut all_for_span: Vec<&Token> = prefix.iter().collect();
        if let Some(ref c) = cmd {
            all_for_span.push(c);
        }
        for s in &suffix {
            all_for_span.push(s);
        }
        let (sstart, send) = if let Some(first) = all_for_span.first() {
            let s = self.span_for(first.id()).0;
            let e = self.span_for(all_for_span.last().unwrap().id()).1;
            (s, e)
        } else {
            (self.pos(), self.pos())
        };
        let id1 = self.next_id_between(sstart.clone(), send.clone());
        let id2 = self.next_id_between(sstart, send);

        // partition prefix into assignments / redirects / rest
        let (mut assigns, mut redirs, mut args): (Vec<Token>, Vec<Token>, Vec<Token>) =
            (Vec::new(), Vec::new(), Vec::new());
        for t in prefix {
            match &*t.inner {
                InnerToken::T_Assignment { .. } => assigns.push(t),
                InnerToken::T_FdRedirect { .. } => redirs.push(t),
                _ => args.push(t),
            }
        }
        let mut cmd_args = Vec::new();
        if let Some(c) = cmd {
            cmd_args.push(c);
        }
        cmd_args.append(&mut args);
        for t in suffix {
            match &*t.inner {
                InnerToken::T_FdRedirect { .. } => redirs.push(t),
                _ => cmd_args.push(t),
            }
        }
        let simple = Token::new(
            id2,
            InnerToken::T_SimpleCommand {
                assignments: assigns,
                words: cmd_args,
            },
        );
        Ok(Token::new(
            id1,
            InnerToken::T_Redirecting {
                redirs,
                cmd: simple,
            },
        ))
    }

    /// `readTimeSuffix`: `time [-p ...] <pipeline>`. Reads optional flag words
    /// (each a `-`-prefixed cmd word), then a full pipeline, appended as the
    /// suffix of the `time` simple command (Parser.hs `readTimeSuffix`). If no
    /// pipeline follows, nothing is consumed and the suffix is empty (mirroring
    /// `option []` over a non-consuming failure).
    fn read_time_suffix(&mut self) -> Vec<Token> {
        let m = self.mark();
        let mut out = Vec::new();
        // many readFlag ; readFlag = lookAhead '-' >> readCmdWord
        loop {
            let fm = self.mark();
            self.spacing();
            if self.peek() == Some('-') {
                if let Ok(w) = self.read_normal_word() {
                    out.push(w);
                    continue;
                }
            }
            self.reset(fm);
            break;
        }
        self.spacing();
        match self.read_pipeline() {
            Ok(p) => {
                out.push(p);
                out
            }
            Err(()) => {
                // No pipeline: undo any consumed flags and behave as a bare
                // `time` command with no suffix.
                self.reset(m);
                Vec::new()
            }
        }
    }

    fn read_cmd_prefix(&mut self) -> Vec<Token> {
        let mut out = Vec::new();
        loop {
            self.spacing();
            // redirect?
            if let Ok(r) = self.read_io_redirect() {
                out.push(r);
                continue;
            }
            // assignment?
            let m = self.mark();
            if let Ok(a) = self.read_assignment_word() {
                out.push(a);
                continue;
            }
            self.reset(m);
            break;
        }
        out
    }

    fn read_cmd_name(&mut self) -> Option<Token> {
        let m = self.mark();
        // don't treat keywords as command names in command position handled by caller
        match self.read_normal_word() {
            Ok(w) => Some(w),
            Err(()) => {
                self.reset(m);
                None
            }
        }
    }

    fn read_cmd_suffix(&mut self, modifier: bool) -> Vec<Token> {
        let mut out = Vec::new();
        loop {
            self.spacing();
            if let Ok(r) = self.read_io_redirect() {
                out.push(r);
                continue;
            }
            // Modifier commands (declare/export/local/readonly/typeset) parse
            // well-formed assignments as T_Assignment (readModifierSuffix).
            if modifier {
                let am = self.mark();
                if let Ok(a) = self.read_assignment_word() {
                    out.push(a);
                    continue;
                }
                self.reset(am);
            }
            let m = self.mark();
            match self.read_normal_word() {
                Ok(w) => out.push(w),
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        out
    }

    /// `reparseIndices`: reparse each `T_UnparsedIndex` as arithmetic (indexed
    /// arrays) or an index word (associative arrays), matching ShellCheck.
    fn reparse_indices_root(
        &mut self,
        mut root: Token,
        assoc: &std::collections::HashSet<String>,
    ) -> Token {
        self.reparse_walk(&mut root, assoc);
        root
    }

    fn reparse_walk(&mut self, t: &mut Token, assoc: &std::collections::HashSet<String>) {
        let name = match &*t.inner {
            InnerToken::T_Assignment { var, .. } => Some(var.clone()),
            InnerToken::TA_Variable { name, .. } => Some(name.clone()),
            _ => None,
        };
        if let Some(name) = name {
            let is_assoc = assoc.contains(&name);
            let indices: Option<&mut Vec<Token>> = match &mut *t.inner {
                InnerToken::T_Assignment { indices, .. } => Some(indices),
                InnerToken::TA_Variable { indices, .. } => Some(indices),
                _ => None,
            };
            if let Some(indices) = indices {
                let jobs: Vec<(usize, Position, String)> = indices
                    .iter()
                    .enumerate()
                    .filter_map(|(i, slot)| match &*slot.inner {
                        InnerToken::T_UnparsedIndex { pos, str } => {
                            Some((i, pos.clone(), str.clone()))
                        }
                        _ => None,
                    })
                    .collect();
                for (i, pos, src) in jobs {
                    let newtok = if is_assoc {
                        self.sub_parse_index_word(&pos, &src)
                    } else {
                        self.sub_parse_arithmetic(&pos, &src)
                    };
                    if let Some(nt) = newtok {
                        // Re-fetch the indices vec (borrow released after sub_parse).
                        if let Some(slot) = match &mut *t.inner {
                            InnerToken::T_Assignment { indices, .. } => indices.get_mut(i),
                            InnerToken::TA_Variable { indices, .. } => indices.get_mut(i),
                            _ => None,
                        } {
                            *slot = nt;
                        }
                    }
                }
            }
            // Reparse T_IndexedElement indices inside a T_Assignment's array value,
            // using the assignment's array name (fixIndexElement).
            if let InnerToken::T_Assignment { value, .. } = &mut *t.inner {
                if let InnerToken::T_Array(elems) = &mut *value.inner {
                    for elem in elems.iter_mut() {
                        self.reparse_indexed_element(elem, is_assoc);
                    }
                }
            }
        }
        for c in t.inner.children_mut() {
            self.reparse_walk(c, assoc);
        }
    }

    fn reparse_indexed_element(&mut self, elem: &mut Token, is_assoc: bool) {
        if let InnerToken::T_IndexedElement { indices, .. } = &*elem.inner {
            let jobs: Vec<(usize, Position, String)> = indices
                .iter()
                .enumerate()
                .filter_map(|(i, slot)| match &*slot.inner {
                    InnerToken::T_UnparsedIndex { pos, str } => Some((i, pos.clone(), str.clone())),
                    _ => None,
                })
                .collect();
            for (i, pos, src) in jobs {
                let newtok = if is_assoc {
                    self.sub_parse_index_word(&pos, &src)
                } else {
                    self.sub_parse_arithmetic(&pos, &src)
                };
                if let Some(nt) = newtok {
                    if let InnerToken::T_IndexedElement { indices, .. } = &mut *elem.inner {
                        if let Some(slot) = indices.get_mut(i) {
                            *slot = nt;
                        }
                    }
                }
            }
        }
    }

    /// Sub-parse `src` (starting at `pos`) as arithmetic contents, merging the
    /// sub-parser's positions and id counter. Mirrors ShellCheck's `subParse`.
    fn sub_parse_arithmetic(&mut self, pos: &Position, src: &str) -> Option<Token> {
        let mut sub = Parser::new(&self.filename, src);
        sub.line = pos.line;
        sub.col = pos.column;
        sub.next_id = self.next_id;
        sub.spacing();
        let tok = sub.read_arithmetic_contents().ok()?;
        // require eof (readArithmeticContents <* eof)
        sub.spacing();
        if !sub.eof() {
            return None;
        }
        for (k, v) in sub.positions.iter() {
            self.positions.insert(*k, v.clone());
        }
        self.next_id = sub.next_id;
        Some(tok)
    }

    /// Sub-parse `src` (at `pos`) as an associative-array index word.
    fn sub_parse_index_word(&mut self, pos: &Position, src: &str) -> Option<Token> {
        let mut sub = Parser::new(&self.filename, src);
        sub.line = pos.line;
        sub.col = pos.column;
        sub.next_id = self.next_id;
        let tok = sub.read_normal_word().ok();
        let tok = tok.unwrap_or_else(|| sub.empty_literal_word());
        for (k, v) in sub.positions.iter() {
            self.positions.insert(*k, v.clone());
        }
        self.next_id = sub.next_id;
        Some(tok)
    }

    /// Read one raw `let` argument word (tracking quotes), returning the raw
    /// text and its start position. Mirrors `readStringForParser readCmdWord`.
    fn read_let_arg_raw(&mut self) -> Option<(String, Position)> {
        let start = self.pos();
        let mut raw = String::new();
        let mut in_single = false;
        let mut in_double = false;
        while let Some(c) = self.peek() {
            if in_single {
                raw.push(c);
                self.bump();
                if c == '\'' {
                    in_single = false;
                }
                continue;
            }
            if in_double {
                raw.push(c);
                self.bump();
                if c == '"' {
                    in_double = false;
                }
                continue;
            }
            match c {
                ' ' | '\t' | '\n' | '\r' | ';' | '&' | '|' | ')' => break,
                '\'' => {
                    in_single = true;
                    raw.push(c);
                    self.bump();
                }
                '"' => {
                    in_double = true;
                    raw.push(c);
                    self.bump();
                }
                _ => {
                    raw.push(c);
                    self.bump();
                }
            }
        }
        if raw.is_empty() {
            None
        } else {
            Some((raw, start))
        }
    }

    /// `readLetSuffix`: parse `let` arguments as arithmetic expressions.
    fn read_let_suffix(&mut self) -> Vec<Token> {
        let mut out = Vec::new();
        loop {
            self.spacing();
            if let Ok(r) = self.read_io_redirect() {
                out.push(r);
                continue;
            }
            let m = self.mark();
            if let Some((raw, start)) = self.read_let_arg_raw() {
                // kludgeAwayQuotes: strip matching surrounding quotes.
                let chars: Vec<char> = raw.chars().collect();
                let (unquoted, adj_pos) = if chars.len() >= 2
                    && (chars[0] == '\'' || chars[0] == '"')
                    && chars[0] == chars[chars.len() - 1]
                {
                    let mut p = start.clone();
                    p.column += 1;
                    (chars[1..chars.len() - 1].iter().collect::<String>(), p)
                } else {
                    (raw.clone(), start.clone())
                };
                if let Some(tok) = self.sub_parse_arithmetic(&adj_pos, &unquoted) {
                    out.push(tok);
                    continue;
                }
            }
            // Fall back to a normal word.
            self.reset(m);
            match self.read_normal_word() {
                Ok(w) => out.push(w),
                Err(()) => break,
            }
        }
        out
    }

    /// `validateCommand` (Parser.hs): emit SC1127 when a command word is really
    /// a C-style comment — either the word `//`, or a word starting `/*`.
    fn validate_command_comment(&mut self, cmd: &Token) {
        if let InnerToken::T_NormalWord(parts) = &*cmd.inner {
            let is_comment = match parts.as_slice() {
                [only] => matches!(&*only.inner, InnerToken::T_Literal(s) if s == "//"),
                [first, second, ..] => {
                    matches!(&*first.inner, InnerToken::T_Literal(s) if s == "/")
                        && matches!(&*second.inner, InnerToken::T_Glob(g) if g == "*")
                }
                _ => false,
            };
            if is_comment {
                let (s, e) = self.span_for(cmd.id());
                self.problem_at(
                    s,
                    e,
                    Severity::ErrorC,
                    1127,
                    "Was this intended as a comment? Use # in sh.",
                );
            }
        }
    }

    /// The single-literal command name of a T_NormalWord, if any.
    fn command_literal_name(t: &Token) -> Option<String> {
        if let InnerToken::T_NormalWord(parts) = &*t.inner {
            if parts.len() == 1 {
                if let InnerToken::T_Literal(s) = &*parts[0].inner {
                    return Some(s.clone());
                }
            }
        }
        None
    }

    fn read_assignment_word(&mut self) -> PResult<Token> {
        let start = self.pos();
        // name
        let name = self.read_variable_name()?;
        // optional [index] indices -> T_UnparsedIndex (like top-level readArrayIndex)
        let mut indices = Vec::new();
        while self.peek() == Some('[') {
            let istart = self.pos();
            self.bump();
            let pos = self.pos();
            let mut raw = String::new();
            let mut depth = 1;
            while let Some(c) = self.peek() {
                if c == '[' {
                    depth += 1;
                } else if c == ']' {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                self.bump();
                raw.push(c);
            }
            self.char(']')?;
            let idx_id = self.next_id_between(istart, self.pos());
            indices.push(Token::new(
                idx_id,
                InnerToken::T_UnparsedIndex { pos, str: raw },
            ));
        }
        // The T_Assignment span ends here (variable name + indices), before the
        // `=` — matching ShellCheck's `id <- endSpan start` placement, so that
        // SC2034 etc. point at the variable name rather than the whole word.
        let op_start = self.pos();
        // += or =
        let mode = if self.string("+=").is_ok() {
            AssignmentMode::Append
        } else if self.char('=').is_ok() {
            AssignmentMode::Assign
        } else {
            return Err(());
        };
        // value: array (..) or word (possibly empty)
        let value = if self.peek() == Some('(') {
            self.read_array()?
        } else {
            let m = self.mark();
            match self.read_normal_word() {
                Ok(w) => w,
                Err(()) => {
                    self.reset(m);
                    // empty value
                    self.empty_literal_word()
                }
            }
        };
        let id = self.next_id_between(start, op_start);
        Ok(Token::new(
            id,
            InnerToken::T_Assignment {
                mode,
                var: name,
                indices,
                value,
            },
        ))
    }

    fn empty_literal_word(&mut self) -> Token {
        let p = self.pos();
        let lit_id = self.next_id_between(p.clone(), p.clone());
        let lit = Token::new(lit_id, InnerToken::T_Literal(String::new()));
        let wid = self.next_id_between(p.clone(), p);
        Token::new(wid, InnerToken::T_NormalWord(vec![lit]))
    }

    fn read_array(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('(')?;
        let mut elems = Vec::new();
        loop {
            self.allspacing();
            if self.peek() == Some(')') || self.peek().is_none() {
                break;
            }
            // readIndexed: `[idx]...=value` -> T_IndexedElement
            if self.peek() == Some('[') {
                let em = self.mark();
                let estart = self.pos();
                let mut indices = Vec::new();
                while self.peek() == Some('[') {
                    let istart = self.pos();
                    self.bump();
                    let pos = self.pos();
                    let mut raw = String::new();
                    let mut depth = 1;
                    while let Some(c) = self.peek() {
                        if c == '[' {
                            depth += 1;
                        } else if c == ']' {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        self.bump();
                        raw.push(c);
                    }
                    if self.char(']').is_err() {
                        break;
                    }
                    let idx_id = self.next_id_between(istart, self.pos());
                    indices.push(Token::new(
                        idx_id,
                        InnerToken::T_UnparsedIndex { pos, str: raw },
                    ));
                }
                if !indices.is_empty() && self.char('=').is_ok() {
                    let value = match self.read_normal_word() {
                        Ok(w) => w,
                        Err(()) => self.empty_literal_word(),
                    };
                    let eid = self.next_id_between(estart, self.pos());
                    elems.push(Token::new(
                        eid,
                        InnerToken::T_IndexedElement { indices, value },
                    ));
                    continue;
                }
                self.reset(em);
            }
            match self.read_normal_word() {
                Ok(w) => elems.push(w),
                Err(()) => break,
            }
        }
        self.char(')')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Array(elems)))
    }

    // ---- redirections ------------------------------------------------------

    fn read_redirect_list(&mut self) -> Vec<Token> {
        let mut out = Vec::new();
        loop {
            self.spacing();
            match self.read_io_redirect() {
                Ok(r) => out.push(r),
                Err(()) => break,
            }
        }
        out
    }

    fn read_io_redirect(&mut self) -> PResult<Token> {
        let m = self.mark();
        let start = self.pos();
        // optional fd number or {var}
        let mut fd = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                fd.push(c);
                self.bump();
            } else {
                break;
            }
        }
        // `{varname}` file-descriptor variable, only when directly followed by a
        // redirection operator (otherwise it's a brace group / word).
        if fd.is_empty() && self.peek() == Some('{') {
            let fdmark = self.mark();
            self.bump(); // {
            let mut name = String::new();
            if let Some(c) = self.peek() {
                if c == '_' || c.is_ascii_alphabetic() {
                    name.push(c);
                    self.bump();
                    while let Some(c) = self.peek() {
                        if c == '_' || c.is_ascii_alphanumeric() {
                            name.push(c);
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
            }
            let ok = !name.is_empty()
                && self.peek() == Some('}')
                && matches!(self.peek_at(1), Some('<') | Some('>'));
            if ok {
                self.bump(); // }
                fd = format!("{{{}}}", name);
            } else {
                self.reset(fdmark);
            }
        }
        // `&>` / `&>>` combined redirect: `readIoSource` accepts `&` as the
        // source when it is immediately followed by a redirection operator
        // (`lookAhead $ readIoFileOp <|> string "<<"`). Consume the `&` here so
        // the following operator (`>`/`>>`/`<`/`<<`/...) is parsed as the
        // redirection, matching Parser.hs (`ls &> bar`, `ls &>> bar`).
        if fd.is_empty()
            && self.peek() == Some('&')
            && matches!(self.peek_at(1), Some('<') | Some('>'))
        {
            self.bump(); // &
            fd = "&".to_string();
        }
        // `op_start` is the position after the fd source, where the redirection
        // operator begins. Parser.hs captures `startSpan` for the inner redir
        // token (T_IoFile/T_IoDuplicate/T_HereString/T_HereDoc) here, *after*
        // `readIoSource` has consumed the fd, so a glued `1>2` anchors T_IoFile
        // (and thus SC2210) at the `>`, not the fd digit.
        let op_start = self.pos();
        // heredoc
        if self.peek() == Some('<') && self.peek_at(1) == Some('<') {
            return self.read_heredoc_or_herestring(start, op_start, fd);
        }
        // dup: <& or >&
        if (self.peek() == Some('<') || self.peek() == Some('>')) && self.peek_at(1) == Some('&') {
            let opc = self.bump().unwrap();
            self.bump(); // &
            // `digitsAndOrDash`: digits then optional `-`, or a required `-` when
            // there are no digits. If neither, this is NOT a duplicate but a
            // `>& file` / `<& file` redirect (readIoDuplicate `try` fails).
            let mut num = String::new();
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    num.push(c);
                    self.bump();
                } else {
                    break;
                }
            }
            if self.peek() == Some('-') {
                num.push('-');
                self.bump();
            }
            let opid = self.next_id_between(op_start.clone(), self.pos());
            let op_tok = Token::new(
                opid,
                if opc == '<' {
                    InnerToken::T_LESSAND
                } else {
                    InnerToken::T_GREATAND
                },
            );
            if !num.is_empty() {
                let dup_id = self.next_id_between(op_start.clone(), self.pos());
                let dup = Token::new(dup_id, InnerToken::T_IoDuplicate { op: op_tok, num });
                let id = self.next_id_between(start, self.pos());
                return Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: dup }));
            }
            // `>& file` / `<& file`: a file redirect to the following word.
            self.spacing();
            let file = match self.read_normal_word() {
                Ok(w) => w,
                Err(()) => {
                    self.reset(m);
                    return Err(());
                }
            };
            let iofile_id = self.next_id_between(op_start.clone(), self.pos());
            let iofile = Token::new(iofile_id, InnerToken::T_IoFile { op: op_tok, file });
            let id = self.next_id_between(start, self.pos());
            return Ok(Token::new(
                id,
                InnerToken::T_FdRedirect { fd, target: iofile },
            ));
        }
        // file redirect operators
        let op = self.read_io_file_op(op_start.clone());
        match op {
            Some(op_tok) => {
                self.spacing();
                let file = match self.read_normal_word() {
                    Ok(w) => w,
                    Err(()) => {
                        self.reset(m);
                        return Err(());
                    }
                };
                let iofile_id = self.next_id_between(op_start.clone(), self.pos());
                let iofile = Token::new(iofile_id, InnerToken::T_IoFile { op: op_tok, file });
                let id = self.next_id_between(start, self.pos());
                Ok(Token::new(
                    id,
                    InnerToken::T_FdRedirect { fd, target: iofile },
                ))
            }
            None => {
                self.reset(m);
                Err(())
            }
        }
    }

    fn read_io_file_op(&mut self, start: Position) -> Option<Token> {
        let (inner, len): (InnerToken, usize) = match (self.peek(), self.peek_at(1)) {
            (Some('>'), Some('>')) => (InnerToken::T_DGREAT, 2),
            (Some('<'), Some('>')) => (InnerToken::T_LESSGREAT, 2),
            (Some('>'), Some('|')) => (InnerToken::T_CLOBBER, 2),
            (Some('<'), _) => (InnerToken::T_Less, 1),
            (Some('>'), _) => (InnerToken::T_Greater, 1),
            _ => return None,
        };
        for _ in 0..len {
            self.bump();
        }
        let id = self.next_id_between(start, self.pos());
        Some(Token::new(id, inner))
    }

    fn read_heredoc_or_herestring(
        &mut self,
        start: Position,
        op_start: Position,
        fd: String,
    ) -> PResult<Token> {
        // << , <<- , <<<
        self.string("<<")?;
        if self.char('<').is_ok() {
            // here string: `readHereString` spans just `<<<` (id captured before
            // the word is read).
            let hs_id = self.next_id_between(op_start.clone(), self.pos());
            self.spacing();
            let word = self.read_normal_word()?;
            let hs = Token::new(hs_id, InnerToken::T_HereString(word));
            let id = self.next_id_between(start, self.pos());
            return Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: hs }));
        }
        let dashed = if self.char('-').is_ok() {
            Dashed::Dashed
        } else {
            Dashed::Undashed
        };
        self.spacing();
        // delimiter (may be quoted). `readHereDoc` captures `startSpan` here,
        // *after* `<<`/`-`/spacing, so T_HereDoc spans only the end token.
        let delim_start = self.pos();
        let (delim, quoted) = self.read_heredoc_delim()?;
        // Body is read lazily at next newline; for the slice, capture nothing now
        // and register a pending heredoc.
        let hd_id = self.next_id_between(delim_start, self.pos());
        self.pending_heredocs.push(PendingHereDoc {
            dashed,
            quoted,
            delim: delim.clone(),
            id: hd_id,
        });
        let hd = Token::new(
            hd_id,
            InnerToken::T_HereDoc {
                dashed,
                quoted,
                delim,
                body: Vec::new(),
            },
        );
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: hd }))
    }

    fn read_heredoc_delim(&mut self) -> PResult<(String, Quoted)> {
        match self.peek() {
            Some('\'') => {
                self.bump();
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    if c == '\'' {
                        break;
                    }
                    self.bump();
                    s.push(c);
                }
                self.char('\'')?;
                Ok((s, Quoted::Quoted))
            }
            Some('"') => {
                self.bump();
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    if c == '"' {
                        break;
                    }
                    self.bump();
                    s.push(c);
                }
                self.char('"')?;
                Ok((s, Quoted::Quoted))
            }
            _ => {
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    if c.is_ascii_alphanumeric() || "_-.!/".contains(c) {
                        self.bump();
                        s.push(c);
                    } else {
                        break;
                    }
                }
                if s.is_empty() {
                    Err(())
                } else {
                    Ok((s, Quoted::Unquoted))
                }
            }
        }
    }

    fn read_pending_heredocs(&mut self) {
        if self.pending_heredocs.is_empty() {
            return;
        }
        let pending: Vec<PendingHereDoc> = std::mem::take(&mut self.pending_heredocs);
        for hd in pending {
            // `docStartPos`: the position of the first byte of the body (this is
            // invoked right after the `<<EOF` line's newline).
            let doc_start = self.pos();
            // consume lines until a line equal to delim (trimmed if dashed)
            let mut body = String::new();
            loop {
                if self.eof() {
                    break;
                }
                // read one line
                let line_start = self.idx;
                let mut line = String::new();
                while let Some(c) = self.peek() {
                    if c == '\n' {
                        break;
                    }
                    self.bump();
                    line.push(c);
                }
                let terminator = if hd.dashed == Dashed::Dashed {
                    line.trim_start_matches('\t')
                } else {
                    line.as_str()
                };
                if terminator == hd.delim {
                    // consume trailing newline
                    let _ = self.char('\n');
                    break;
                }
                let _ = line_start;
                body.push_str(&line);
                body.push('\n');
                if self.char('\n').is_err() {
                    break;
                }
            }
            let doc_end = self.pos();
            // `parseHereData`: a quoted delimiter keeps the body verbatim as one
            // literal; an unquoted delimiter sub-parses the body for expansions
            // (`$(..)`, `` `..` ``, `${..}`, `$var`) exactly like a double-quoted
            // string, so stdin-consumer detection sees them.
            let tokens = match hd.quoted {
                Quoted::Quoted => {
                    let lit_id = self.next_id_between(doc_start, doc_end);
                    vec![Token::new(lit_id, InnerToken::T_Literal(body))]
                }
                Quoted::Unquoted => self.read_here_data(&body, doc_start),
            };
            self.heredoc_bodies.insert(hd.id, tokens);
        }
    }

    /// `readHereData` (Parser.hs): sub-parse an unquoted here-doc body into the
    /// same token stream a double-quoted string produces (literals, dollar
    /// expansions, backtick command substitutions), with `"` and other
    /// non-`` `$\ `` characters kept literal via `readHereLiteral`.
    fn read_here_data(&mut self, body: &str, start: Position) -> Vec<Token> {
        let mut sub = Parser::new(&self.filename, body);
        sub.line = start.line;
        sub.col = start.column;
        sub.next_id = self.next_id;
        let mut parts = Vec::new();
        while !sub.eof() {
            let progressed_from = sub.idx;
            match sub.peek() {
                // `readDoubleQuotedDollar` always succeeds on `$` (falls back to
                // a literal `$` via `readDollarLonely`).
                Some('$') => {
                    if let Ok(t) = sub.read_double_quoted_dollar() {
                        parts.push(t);
                    }
                }
                // `readQuotedBackTicked`: a `` `..` `` command substitution.
                Some('`') => match sub.read_backticked(true) {
                    Ok(t) => parts.push(t),
                    // An unterminated backtick can't be consumed by
                    // `readHereLiteral` either (it excludes `` ` ``); stop.
                    Err(()) => break,
                },
                // `readDoubleLiteral` (escapes + run up to a double-quotable
                // char), else `readHereLiteral` (run up to `` `$\ ``, so `"` and
                // ordinary text are literal).
                _ => {
                    if let Ok(t) = sub.read_double_literal_run() {
                        parts.push(t);
                    } else if let Ok(t) = sub.read_here_literal() {
                        parts.push(t);
                    } else {
                        break;
                    }
                }
            }
            if sub.idx == progressed_from {
                // No progress (shouldn't happen); guard against an infinite loop.
                break;
            }
        }
        self.next_id = sub.next_id;
        for (k, v) in sub.positions {
            self.positions.entry(k).or_insert(v);
        }
        self.notes.extend(sub.notes);
        self.problems.extend(sub.problems);
        parts
    }

    /// `readHereLiteral`: a run of characters that are not `` ` ``, `$` or `\`.
    fn read_here_literal(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '`' || c == '$' || c == '\\' {
                break;
            }
            self.bump();
            s.push(c);
        }
        if s.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }

    // ---- script entry ------------------------------------------------------

    /// `isValidShell` (Parser.hs readScriptFile): `Just true` for a recognized
    /// good shell, `Just false` for a known-unsupported one, `None` otherwise.
    fn is_valid_shell(s: &str) -> Option<bool> {
        const GOOD: &[&str] = &[
            "sh",
            "ash",
            "dash",
            "busybox sh",
            "bash",
            "bats",
            "ksh",
            "oksh",
        ];
        const BAD: &[&str] = &[
            "awk", "csh", "expect", "fish", "perl", "python", "python3", "ruby", "tcsh", "zsh",
        ];
        let good = s.is_empty() || GOOD.iter().any(|g| s.starts_with(g));
        let bad = BAD.iter().any(|b| s.starts_with(b));
        if good {
            Some(true)
        } else if bad {
            Some(false)
        } else {
            None
        }
    }

    fn read_script_file(&mut self) -> Option<Token> {
        let start = self.pos();
        // UTF-8 BOM
        let _ = self.string("\u{FEFF}");
        let shebang = self.read_shebang().unwrap_or_else(|| self.empty_literal());
        self.allspacing();
        // File-wide shellcheck directives after the shebang.
        let file_annotations = self.read_annotations();
        self.allspacing();

        // `verifyShebang` (Parser.hs readScriptFile): warn on an unrecognized
        // interpreter, unless a `# shellcheck shell=...` directive overrides the
        // shebang. Emitted at the start of the file, like `parseProblemAt pos`.
        let shell_annotation_specified = file_annotations
            .iter()
            .any(|a| matches!(a, Annotation::ShellOverride(_)));
        if !shell_annotation_specified {
            if let InnerToken::T_Literal(sb) = &*shebang.inner {
                let exe = astlib::executable_from_shebang(sb);
                if Self::is_valid_shell(&exe).is_none() {
                    self.problem_at(
                        start.clone(),
                        start.clone(),
                        Severity::ErrorC,
                        1008,
                        "This shebang was unrecognized. ShellCheck only supports sh/bash/dash/ksh/'busybox sh'. Add a 'shell' directive to specify.",
                    );
                }
            }
        }

        let commands = self.read_compound_list_or_empty();
        self.read_pending_heredocs();
        // verify EOF: if not at end, it's a parse problem (SC1072-ish). For the
        // slice we record a generic problem but still return the tree.
        self.allspacing();
        if !self.eof() {
            let p = self.pos();
            self.problem_at(
                p.clone(),
                p,
                Severity::ErrorC,
                1072,
                "Unexpected input near here.",
            );
        }
        let script_id = self.next_id_between(start.clone(), self.pos());
        let script = Token::new(script_id, InnerToken::T_Script { shebang, commands });
        let ann_id = self.next_id_between(start.clone(), self.pos());
        let root = Token::new(
            ann_id,
            InnerToken::T_Annotation {
                annotations: file_annotations,
                token: script,
            },
        );
        Some(root)
    }
}

/// Public entry point mirroring `ShellCheck.Parser.parseScript`.
pub fn parse_script(filename: &str, script: &str) -> ParseOutput {
    let mut p = Parser::new(filename, script);
    let root = p.read_script_file();
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
                if let Some(s) = crate::astlib::get_literal_string(a) {
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
                let lit = crate::astlib::get_literal_string(a);
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

// ============================================================================
// ShellCheck directive annotations (# shellcheck ...)
// ============================================================================

impl Parser {
    /// `readAnnotations`: zero or more `# shellcheck ...` directive lines.
    fn read_annotations(&mut self) -> Vec<Annotation> {
        let mut out = Vec::new();
        loop {
            let m = self.mark();
            match self.read_annotation() {
                Some(mut anns) => {
                    out.append(&mut anns);
                    self.allspacing();
                }
                None => {
                    self.reset(m);
                    break;
                }
            }
        }
        out
    }

    /// A single `# shellcheck <keys>` directive; None if the line is not one.
    fn read_annotation(&mut self) -> Option<Vec<Annotation>> {
        let m = self.mark();
        if self.char('#').is_err() {
            self.reset(m);
            return None;
        }
        while self.line_whitespace().is_ok() {}
        if self.string("shellcheck").is_err() {
            self.reset(m);
            return None;
        }
        // require at least one whitespace
        if self.line_whitespace().is_err() {
            // "shellcheck" immediately followed by non-space -> not a directive
            self.reset(m);
            return None;
        }
        while self.line_whitespace().is_ok() {}
        Some(self.read_annotation_keys())
    }

    fn read_annotation_keys(&mut self) -> Vec<Annotation> {
        let mut out = Vec::new();
        loop {
            // stop at end of line
            match self.peek() {
                None | Some('\n') | Some('\r') => break,
                Some('#') => {
                    // trailing comment: consume rest of line
                    while let Some(c) = self.peek() {
                        if c == '\n' {
                            break;
                        }
                        self.bump();
                    }
                    break;
                }
                _ => {}
            }
            let key_pos = self.pos();
            let key = self.read_annotation_key_name();
            if key.is_empty() {
                // not a key=value; skip rest of line
                while let Some(c) = self.peek() {
                    if c == '\n' {
                        break;
                    }
                    self.bump();
                }
                break;
            }
            if self.char('=').is_err() {
                // malformed; stop
                break;
            }
            let mut anns = self.read_annotation_value(&key, key_pos);
            out.append(&mut anns);
            while self.line_whitespace().is_ok() {}
        }
        // consume trailing newline
        let _ = self.char('\r');
        let _ = self.char('\n');
        out
    }

    fn read_annotation_key_name(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_alphabetic() || c == '-' {
                self.bump();
                s.push(c);
            } else {
                break;
            }
        }
        s
    }

    /// Read a directive value (possibly single/double quoted). Returns the raw
    /// string and whether it was quoted.
    fn read_annotation_raw_value(&mut self) -> String {
        match self.peek() {
            Some(q @ ('\'' | '"')) => {
                self.bump();
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    if c == q || c == '\n' {
                        break;
                    }
                    self.bump();
                    s.push(c);
                }
                let _ = self.char(q);
                s
            }
            _ => {
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
                        break;
                    }
                    self.bump();
                    s.push(c);
                }
                s
            }
        }
    }

    fn read_annotation_value(&mut self, key: &str, key_pos: Position) -> Vec<Annotation> {
        match key {
            "disable" => {
                let raw = self.read_annotation_raw_value();
                raw.split(',').filter_map(parse_disable_element).collect()
            }
            "enable" => {
                let raw = self.read_annotation_raw_value();
                raw.split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| Annotation::EnableComment(s.to_string()))
                    .collect()
            }
            "source" => {
                let v = self.read_annotation_raw_value();
                vec![Annotation::SourceOverride(v)]
            }
            "source-path" => {
                let v = self.read_annotation_raw_value();
                vec![Annotation::SourcePath(v)]
            }
            "shell" => {
                let pos = self.pos();
                let v = self.read_annotation_raw_value();
                if crate::data::shell_for_executable(&v).is_none() {
                    self.note_at(
                        pos.clone(),
                        pos,
                        Severity::ErrorC,
                        1103,
                        "This shell type is unknown. Use e.g. sh or bash.",
                    );
                }
                vec![Annotation::ShellOverride(v)]
            }
            "extended-analysis" => {
                let v = self.read_annotation_raw_value();
                match v.as_str() {
                    "true" => vec![Annotation::ExtendedAnalysis(true)],
                    "false" => vec![Annotation::ExtendedAnalysis(false)],
                    _ => Vec::new(),
                }
            }
            "external-sources" => {
                let v = self.read_annotation_raw_value();
                match v.as_str() {
                    "true" => vec![Annotation::ExternalSources(true)],
                    "false" => vec![Annotation::ExternalSources(false)],
                    _ => Vec::new(),
                }
            }
            _ => {
                let _ = self.read_annotation_raw_value();
                self.note_at(
                    key_pos.clone(),
                    key_pos,
                    Severity::WarningC,
                    1107,
                    "This directive is unknown. It will be ignored.",
                );
                Vec::new()
            }
        }
    }
}

fn parse_disable_element(s: &str) -> Option<Annotation> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    if s == "all" {
        return Some(Annotation::DisableComment(0, 1_000_000));
    }
    // [SC]nnnn optionally -[SC]nnnn
    let parse_code = |x: &str| -> Option<i64> {
        let x = x.trim();
        let x = x.strip_prefix("SC").unwrap_or(x);
        x.parse::<i64>().ok()
    };
    if let Some((a, b)) = s.split_once('-') {
        let from = parse_code(a)?;
        let to = parse_code(b)?;
        Some(Annotation::DisableComment(from, to))
    } else {
        let from = parse_code(s)?;
        Some(Annotation::DisableComment(from, from + 1))
    }
}

// ============================================================================
// Test conditions: [ .. ] and [[ .. ]]  (ShellCheck.Parser.readCondition)
// ============================================================================

impl Parser {
    /// `readConditionCommand`: a condition plus optional redirects, wrapped in
    /// T_Redirecting like every other command. Returns Err (with full reset)
    /// on any failure so the caller can fall back to a simple command.
    fn read_condition_command(&mut self) -> PResult<Token> {
        let m = self.mark();
        let start = self.pos();
        let cond = match self.read_condition() {
            Ok(c) => c,
            Err(()) => {
                self.reset(m);
                return Err(());
            }
        };
        let redirs = self.read_redirect_list();
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_Redirecting { redirs, cmd: cond },
        ))
    }

    fn read_condition(&mut self) -> PResult<Token> {
        if self.peek() != Some('[') {
            return Err(());
        }
        let start = self.pos();
        let dbl = self.peek_at(1) == Some('[');
        if dbl {
            self.string("[[")?;
        } else {
            self.char('[')?;
        }
        let single = !dbl;
        let typ = if single {
            ConditionType::SingleBracket
        } else {
            ConditionType::DoubleBracket
        };

        // required space after the bracket
        let space = self.cond_spacing();

        // SC1014: mirror Parser.hs `readConditionContents`'s `attempting`
        // lookahead — peek a variable name followed by whitespace; if it names a
        // common command, warn that a command is being used as a test operand.
        // Non-consuming (lookAhead), so the cursor is always restored.
        {
            let m = self.mark();
            let pos = self.pos();
            if let Ok(name) = self.read_variable_name() {
                if self.spacing1().is_ok() && COMMON_COMMANDS.contains(&name.as_str()) {
                    self.problem_at(
                        pos.clone(),
                        pos,
                        Severity::WarningC,
                        1014,
                        "Use 'if cmd; then ..' to check exit code, or 'if [[ $(cmd) == .. ]]' to check output.",
                    );
                }
            }
            self.reset(m);
        }

        let contents = self.read_cond_contents(single).ok();
        let token = match contents {
            Some(c) => c,
            None => {
                // empty condition: only valid if there was space and a closing ] follows
                if space.is_empty() {
                    return Err(());
                }
                let id = self.next_id_between(start.clone(), self.pos());
                Token::new(id, InnerToken::TC_Empty { typ })
            }
        };
        // closing bracket
        let closed = if dbl {
            self.string("]]").is_ok()
        } else {
            // single ] but not ]]
            self.peek() == Some(']') && {
                self.bump();
                true
            }
        };
        if !closed {
            return Err(());
        }
        self.spacing();
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Condition { typ, token }))
    }

    /// Spacing within a condition (spaces, tabs, line continuations, newlines in
    /// `[[ ]]`). Returns the consumed whitespace.
    fn cond_spacing(&mut self) -> String {
        let mut out = String::new();
        loop {
            let mut progressed = false;
            while let Ok(c) = self.line_whitespace() {
                out.push(c);
                progressed = true;
            }
            let m = self.mark();
            if self.string("\\\n").is_ok() {
                out.push('\n');
                progressed = true;
            } else {
                self.reset(m);
            }
            // allow bare newlines too (only meaningful in [[ ]], but harmless)
            let m2 = self.mark();
            if self.char('\n').is_ok() {
                out.push('\n');
                progressed = true;
            } else {
                self.reset(m2);
            }
            if !progressed {
                break;
            }
        }
        out
    }

    // contents = or-level (chained by && / -a → TC_And)
    fn read_cond_contents(&mut self, single: bool) -> PResult<Token> {
        self.read_cond_or(single)
    }

    fn read_cond_or(&mut self, single: bool) -> PResult<Token> {
        let mut left = self.read_cond_and(single)?;
        loop {
            let m = self.mark();
            let op_start = self.pos();
            if let Some(op) = self.read_cond_and_op() {
                let op_end = self.pos();
                self.cond_spacing();
                match self.read_cond_and(single) {
                    Ok(right) => {
                        let typ = self.cond_typ(single);
                        let id = self.next_id_between(op_start, op_end);
                        left = Token::new(
                            id,
                            InnerToken::TC_And {
                                typ,
                                op,
                                lhs: left,
                                rhs: right,
                            },
                        );
                    }
                    Err(()) => {
                        self.reset(m);
                        break;
                    }
                }
            } else {
                self.reset(m);
                break;
            }
        }
        Ok(left)
    }

    fn read_cond_and(&mut self, single: bool) -> PResult<Token> {
        let mut left = self.read_cond_term(single)?;
        loop {
            let m = self.mark();
            let op_start = self.pos();
            if let Some(op) = self.read_cond_or_op() {
                let op_end = self.pos();
                self.cond_spacing();
                match self.read_cond_term(single) {
                    Ok(right) => {
                        let typ = self.cond_typ(single);
                        let id = self.next_id_between(op_start, op_end);
                        left = Token::new(
                            id,
                            InnerToken::TC_Or {
                                typ,
                                op,
                                lhs: left,
                                rhs: right,
                            },
                        );
                    }
                    Err(()) => {
                        self.reset(m);
                        break;
                    }
                }
            } else {
                self.reset(m);
                break;
            }
        }
        Ok(left)
    }

    fn cond_typ(&self, single: bool) -> ConditionType {
        if single {
            ConditionType::SingleBracket
        } else {
            ConditionType::DoubleBracket
        }
    }

    fn read_cond_and_op(&mut self) -> Option<String> {
        // && (both) or -a (word-bounded)
        if self.peek() == Some('&') && self.peek_at(1) == Some('&') {
            self.bump();
            self.bump();
            return Some("&&".to_string());
        }
        if self.keyword_dash("-a") {
            self.string("-a").ok();
            return Some("-a".to_string());
        }
        None
    }

    fn read_cond_or_op(&mut self) -> Option<String> {
        if self.peek() == Some('|') && self.peek_at(1) == Some('|') {
            self.bump();
            self.bump();
            return Some("||".to_string());
        }
        if self.keyword_dash("-o") {
            self.string("-o").ok();
            return Some("-o".to_string());
        }
        None
    }

    /// A `-x` operator token that is word-bounded (followed by whitespace).
    fn keyword_dash(&self, s: &str) -> bool {
        let chars: Vec<char> = s.chars().collect();
        for (i, &c) in chars.iter().enumerate() {
            if self.peek_at(i) != Some(c) {
                return false;
            }
        }
        matches!(
            self.peek_at(chars.len()),
            Some(' ') | Some('\t') | Some('\n') | None
        )
    }

    fn read_cond_term(&mut self, single: bool) -> PResult<Token> {
        let t = if self.peek() == Some('!') && self.peek_at(1) != Some('=') {
            self.read_cond_not(single)?
        } else {
            self.read_cond_expr(single)?
        };
        self.cond_spacing();
        Ok(t)
    }

    fn read_cond_not(&mut self, single: bool) -> PResult<Token> {
        let start = self.pos();
        self.char('!')?;
        // `readCondNot`: the TC_Unary id spans the `!` alone (`endSpan start`
        // immediately after `char '!'`), not the whole negated expression.
        let id = self.next_id_between(start, self.pos());
        self.cond_spacing();
        let expr = self.read_cond_expr(single)?;
        let typ = self.cond_typ(single);
        Ok(Token::new(
            id,
            InnerToken::TC_Unary {
                typ,
                op: "!".to_string(),
                token: expr,
            },
        ))
    }

    fn read_cond_expr(&mut self, single: bool) -> PResult<Token> {
        if let Ok(g) = self.read_cond_group(single) {
            return Ok(g);
        }
        if let Ok(u) = self.read_cond_unary(single) {
            return Ok(u);
        }
        self.read_cond_nullary_or_binary(single)
    }

    fn read_cond_group(&mut self, single: bool) -> PResult<Token> {
        let m = self.mark();
        let start = self.pos();
        let opened = if single {
            self.string("\\(").is_ok()
        } else {
            self.char('(').is_ok()
        };
        if !opened {
            self.reset(m);
            return Err(());
        }
        self.cond_spacing();
        let inner = match self.read_cond_contents(single) {
            Ok(c) => c,
            Err(()) => {
                self.reset(m);
                return Err(());
            }
        };
        let closed = if single {
            self.string("\\)").is_ok()
        } else {
            self.char(')').is_ok()
        };
        if !closed {
            self.reset(m);
            return Err(());
        }
        self.cond_spacing();
        let typ = self.cond_typ(single);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::TC_Group { typ, token: inner }))
    }

    fn read_cond_unary(&mut self, single: bool) -> PResult<Token> {
        let m = self.mark();
        let start = self.pos();
        // ShellCheck's `readCondUnaryOp` uses `readOp` with NO exclusion of
        // `-a`/`-o`: at a term (expression) position `-a`/`-o` are the unary
        // "file exists"/"option set" tests. Their AND/OR meaning is only reached
        // by `readCondAndOp`/`readCondOrOp` in the chainl1 layer, i.e. between two
        // already-parsed operands — so a left operand must exist first.
        let op = match self.read_cond_op_flag() {
            Some(o) => o,
            None => {
                self.reset(m);
                return Err(());
            }
        };
        // `readCondUnaryOp`: the TC_Unary id spans the OPERATOR ALONE
        // (`startSpan .. endSpan` around `readOp`, before the trailing spacing),
        // mirroring TC_Binary's operator-only span.
        let op_end = self.pos();
        // must be followed by spacing then a word
        let sp = self.cond_spacing();
        if sp.is_empty() {
            self.reset(m);
            return Err(());
        }
        match self.read_cond_word() {
            Ok(word) => {
                let typ = self.cond_typ(single);
                let id = self.next_id_between(start, op_end);
                Ok(Token::new(
                    id,
                    InnerToken::TC_Unary {
                        typ,
                        op,
                        token: word,
                    },
                ))
            }
            Err(()) => {
                self.reset(m);
                Err(())
            }
        }
    }

    /// Read a `-` followed by letters (test operator), word-bounded.
    fn read_cond_op_flag(&mut self) -> Option<String> {
        if self.peek() != Some('-') {
            return None;
        }
        let m = self.mark();
        self.bump();
        let mut s = String::from("-");
        while let Some(c) = self.peek() {
            if c.is_ascii_alphabetic() {
                self.bump();
                s.push(c);
            } else {
                break;
            }
        }
        if s.len() < 2 {
            self.reset(m);
            return None;
        }
        Some(s)
    }

    fn read_cond_nullary_or_binary(&mut self, single: bool) -> PResult<Token> {
        let start = self.pos();
        let x = self.read_cond_word()?;
        // try binary op
        let m = self.mark();
        let op_start = self.pos();
        // `regexOperatorAhead`: a lookahead (non-consuming) for `=~`/`~=`. When
        // true the RHS is read as a regex rather than a normal condition word.
        let is_regex = self.regex_operator_ahead();
        if let Some((op, op_end)) = self.read_cond_binary_op() {
            // TC_Binary inherits the operator token's span (ShellCheck's
            // `getOp`: `startSpan .. endSpan`), so checks emit on the operator.
            let y = if is_regex {
                self.read_regex()
            } else {
                self.read_cond_word()
            };
            match y {
                Ok(y) => {
                    let typ = self.cond_typ(single);
                    let id = self.next_id_between(op_start, op_end);
                    return Ok(Token::new(
                        id,
                        InnerToken::TC_Binary {
                            typ,
                            op,
                            lhs: x,
                            rhs: y,
                        },
                    ));
                }
                Err(()) => {
                    self.reset(m);
                }
            }
        } else {
            self.reset(m);
        }
        let typ = self.cond_typ(single);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::TC_Nullary { typ, token: x }))
    }

    /// `regexOperatorAhead`: lookahead for `=~` (or the quirky `~=`) without
    /// consuming input.
    fn regex_operator_ahead(&self) -> bool {
        self.string_peek("=~") || self.string_peek("~=")
    }

    /// `readCondBinaryOp`: `readRegularOrEscaped anyOp`, then trailing spacing.
    /// Returns the operator string (with a leading `\` re-added for escaped/quoted
    /// `<`/`>`/`(`/`)`, matching `escaped`) and the position just after the
    /// operator (before spacing), used for the TC_Binary span.
    fn read_cond_binary_op(&mut self) -> Option<(String, Position)> {
        let m = self.mark();
        // readEscaped anyOp  (\op  or  'op' / "op")
        if let Some(op) = self.read_cond_escaped_op() {
            let end = self.pos();
            self.cond_spacing();
            return Some((op, end));
        }
        self.reset(m);
        // plain anyOp
        if let Some(op) = self.read_cond_any_op() {
            let end = self.pos();
            self.cond_spacing();
            return Some((op, end));
        }
        self.reset(m);
        None
    }

    /// `anyOp = flagOp <|> flaglessOp`. flagOp is a `-`+letters test operator
    /// that is not `-a`/`-o`; flaglessOp is one of the symbolic comparisons.
    fn read_cond_any_op(&mut self) -> Option<String> {
        let m = self.mark();
        if let Some(o) = self.read_cond_op_flag() {
            if o != "-a" && o != "-o" {
                return Some(o);
            }
        }
        self.reset(m);
        // flaglessOps, longest first
        for op in ["==", "!=", "<=", ">=", "=~", ">", "<", "="] {
            if self.string_peek(op) {
                self.string(op).ok();
                return Some(op.to_string());
            }
        }
        None
    }

    /// `readEscaped anyOp`: `\op` or a quote-wrapped `'op'` / `"op"`. Per
    /// ShellCheck's `escaped`, if the operator contains any of `<>()` a leading
    /// backslash is re-added to the returned string.
    fn read_cond_escaped_op(&mut self) -> Option<String> {
        let m = self.mark();
        match self.peek() {
            Some('\\') => {
                self.bump();
                if let Some(s) = self.read_cond_any_op() {
                    return Some(Self::escape_cond_op(&s));
                }
                self.reset(m);
                None
            }
            Some(q @ ('\'' | '"')) => {
                self.bump();
                if let Some(s) = self.read_cond_any_op() {
                    if self.peek() == Some(q) {
                        self.bump();
                        return Some(Self::escape_cond_op(&s));
                    }
                }
                self.reset(m);
                None
            }
            _ => None,
        }
    }

    fn escape_cond_op(s: &str) -> String {
        if s.chars().any(|c| "<>()".contains(c)) {
            format!("\\{}", s)
        } else {
            s.to_string()
        }
    }

    fn string_peek(&self, s: &str) -> bool {
        for (i, c) in s.chars().enumerate() {
            if self.peek_at(i) != Some(c) {
                return false;
            }
        }
        true
    }

    /// A condition word: a normal word, not the closing bracket. Stops at
    /// whitespace/operators/brackets like the normal word reader.
    fn read_cond_word(&mut self) -> PResult<Token> {
        // don't read the closing ] / ]] as a word
        if self.peek() == Some(']') {
            return Err(());
        }
        let w = self.read_normal_word()?;
        self.cond_spacing_line();
        Ok(w)
    }

    /// Line-spacing only (used after a cond word so we don't cross newlines
    /// unexpectedly in `[ ]`).
    fn cond_spacing_line(&mut self) {
        while self.line_whitespace().is_ok() {}
    }

    /// `readRegex`: the RHS of `=~`. `many1 readPart`, then trailing spacing.
    /// The parts absorb regex syntax (groups, glob chars, `|`) so that an
    /// unquoted `]]`/`)` inside a `( .. )` group does not terminate the
    /// condition, while unquoted whitespace outside a group ends the regex.
    fn read_regex(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut parts = Vec::new();
        loop {
            let before = self.idx;
            match self.read_regex_part() {
                Ok(p) => {
                    // guard against a zero-width part looping forever
                    if self.idx == before {
                        break;
                    }
                    parts.push(p);
                }
                Err(()) => break,
            }
        }
        if parts.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        self.spacing();
        Ok(Token::new(id, InnerToken::T_NormalWord(parts)))
    }

    /// One `readPart` of a regex: group, quoted string, `$`-expression, a normal
    /// literal (stopping at `(`/space), a literal `|`, or a glob literal char.
    fn read_regex_part(&mut self) -> PResult<Token> {
        match self.peek() {
            Some('(') => return self.read_regex_group(),
            Some('\'') => return self.read_single_quoted(),
            Some('"') => return self.read_double_quoted(),
            Some('$') => {
                let m = self.mark();
                if let Ok(t) = self.read_normal_dollar() {
                    return Ok(t);
                }
                self.reset(m);
                // fall through: bare `$` becomes a glob literal below
            }
            _ => {}
        }
        // readLiteralForParser (readNormalLiteral "( ")
        if let Ok(t) = self.read_literal_for_parser_normal("( ") {
            return Ok(t);
        }
        // readLiteralString "|"
        if self.peek() == Some('|') {
            let start = self.pos();
            self.bump();
            let id = self.next_id_between(start, self.pos());
            return Ok(Token::new(id, InnerToken::T_Literal("|".to_string())));
        }
        // readGlobLiteral: extglobStart <|> oneOf "{}[]$"
        if let Some(c) = self.peek() {
            if "?*@!+".contains(c) || "{}[]$".contains(c) {
                let start = self.pos();
                self.bump();
                let id = self.next_id_between(start, self.pos());
                return Ok(Token::new(id, InnerToken::T_Literal(c.to_string())));
            }
        }
        Err(())
    }

    /// `readLiteralForParser (readNormalLiteral end)`: unlike `readNormalLiteral`
    /// on its own, `readLiteralForParser` runs the inner parser only as a
    /// lookahead to discover the END position, then reads the RAW characters up
    /// to it (`readStringForParser`/`readUntil`). This preserves backslash
    /// escapes verbatim (e.g. a regex RHS `\*` stays `\*`, not `*`), and drops
    /// any notes the lookahead would have produced.
    fn read_literal_for_parser_normal(&mut self, custom_end: &str) -> PResult<Token> {
        let m = self.mark();
        let start = self.pos();
        // Lookahead: find where readNormalLiteral would stop. Preserve notes by
        // snapshotting and restoring them (read_normal_literal itself emits none
        // today, but be robust to that changing).
        let notes_len = self.notes.len();
        let problems_len = self.problems.len();
        if self.read_normal_literal(custom_end).is_err() {
            self.reset(m);
            self.notes.truncate(notes_len);
            self.problems.truncate(problems_len);
            return Err(());
        }
        let end_idx = self.idx;
        self.reset(m);
        self.notes.truncate(notes_len);
        self.problems.truncate(problems_len);
        // Read raw characters up to the discovered end.
        let mut s = String::new();
        while self.idx < end_idx {
            if let Some(c) = self.bump() {
                s.push(c);
            } else {
                break;
            }
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }

    /// `readGroup`: `( .. )` inside a regex. Inside, `readRegexLiteral` swallows
    /// runs of chars (including spaces and `]]`) until a `'"$`()` boundary.
    fn read_regex_group(&mut self) -> PResult<Token> {
        let start = self.pos();
        let p1_start = self.pos();
        self.char('(')?;
        let p1 = Token::new(
            self.next_id_between(p1_start, self.pos()),
            InnerToken::T_Literal("(".to_string()),
        );
        let mut parts = vec![p1];
        loop {
            let m = self.mark();
            let before = self.idx;
            if let Ok(p) = self.read_regex_part() {
                if self.idx != before {
                    parts.push(p);
                    continue;
                }
                self.reset(m);
            } else {
                self.reset(m);
            }
            if let Ok(p) = self.read_regex_literal() {
                parts.push(p);
                continue;
            }
            break;
        }
        if self.peek() != Some(')') {
            return Err(());
        }
        let p2_start = self.pos();
        self.char(')')?;
        let p2 = Token::new(
            self.next_id_between(p2_start, self.pos()),
            InnerToken::T_Literal(")".to_string()),
        );
        parts.push(p2);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_NormalWord(parts)))
    }

    /// `readRegexLiteral`: `readGenericLiteral1` stopping at `'`, `"`, `$`,
    /// backtick, `(` or `)` (keeping backslash escapes verbatim).
    fn read_regex_literal(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut s = String::new();
        loop {
            match self.peek() {
                None => break,
                Some('\\') => {
                    self.bump();
                    match self.bump() {
                        Some('\n') => {}
                        Some(c) => {
                            s.push('\\');
                            s.push(c);
                        }
                        None => s.push('\\'),
                    }
                }
                Some('\'') | Some('"') | Some('$') | Some('`') | Some('(') | Some(')') => break,
                Some(c) => {
                    self.bump();
                    s.push(c);
                }
            }
        }
        if s.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }
}

// ============================================================================
// Tests — arithmetic contents (ports of Parser.hs prop_a1..prop_a23)
// ============================================================================

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
}
