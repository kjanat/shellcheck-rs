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
use crate::interface::{Position, Severity};
use std::collections::BTreeMap;

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
        Mark { idx: self.idx, line: self.line, col: self.col }
    }

    #[inline]
    fn reset(&mut self, m: Mark) {
        self.idx = m.idx;
        self.line = m.line;
        self.col = m.col;
    }

    #[inline]
    fn pos(&self) -> Position {
        Position { file: self.filename.clone(), line: self.line, column: self.col }
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

    fn none_of(&mut self, set: &str) -> PResult<char> {
        match self.peek() {
            Some(c) if !set.contains(c) => {
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

    /// `many1 (oneOf set)` collected as String.
    fn many1_of(&mut self, set: &str) -> PResult<String> {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if set.contains(c) {
                self.bump();
                s.push(c);
            } else {
                break;
            }
        }
        if s.is_empty() { Err(()) } else { Ok(s) }
    }

    fn many_of(&mut self, set: &str) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if set.contains(c) {
                self.bump();
                s.push(c);
            } else {
                break;
            }
        }
        s
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

    /// Allocate a new id spanning the same range as an existing one.
    fn new_id_for(&mut self, id: Id) -> Id {
        let (s, e) = self.span_for(id);
        self.next_id_between(s, e)
    }

    fn note_at(&mut self, start: Position, end: Position, sev: Severity, code: i64, msg: &str) {
        self.notes.push(ParseNote { start, end, severity: sev, code, message: msg.to_string() });
    }

    fn problem_at(&mut self, start: Position, end: Position, sev: Severity, code: i64, msg: &str) {
        self.problems.push(ParseNote { start, end, severity: sev, code, message: msg.to_string() });
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
                self.note_at(p.clone(), p, Severity::ErrorC, 1018,
                    "This is a unicode non-breaking space. Delete and retype it.");
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
            loop {
                match self.line_whitespace() {
                    Ok(c) => {
                        out.push(c);
                        progressed = true;
                    }
                    Err(()) => break,
                }
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
        matches!(self.input.get(i), None | Some(' ') | Some('\t') | Some('\n') | Some('\r'))
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
        loop {
            match self.read_normal_word_part() {
                Ok(p) => parts.push(p),
                Err(()) => break,
            }
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
                '`' => self.read_backticked(),
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
                Some('`') => parts.push(self.read_backticked()?),
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
        // standard end: "[{}" ++ quotableChars ++ extglobStartChars ++ unicode quotes
        let standard_end = "[{}|&;<>()\\ \t\n\r\u{A0}\"$`?*@!+";
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
            match self.peek() {
                Some(']') | None => break,
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
        // Try a `{a,b}` / `{1..3}` brace expansion; otherwise read `{` or `}` as
        // a literal char (so `{}`, `foo{...}`, etc. parse as words). The
        // expansion is currently flattened to a literal of its raw text — the
        // structural `T_BraceExpansion` port is refined later; downstream checks
        // that consume it are added alongside.
        let start = self.pos();
        let c = self.peek();
        if c == Some('{') {
            let m = self.mark();
            self.bump();
            // Detect comma/range brace expansion by scanning balanced braces.
            let mut depth = 1;
            let mut raw = String::from("{");
            let mut has_comma_or_range = false;
            let mut ok = false;
            while let Some(ch) = self.peek() {
                match ch {
                    '{' => depth += 1,
                    '}' => {
                        depth -= 1;
                        raw.push('}');
                        self.bump();
                        if depth == 0 {
                            ok = true;
                            break;
                        }
                        continue;
                    }
                    ',' if depth == 1 => has_comma_or_range = true,
                    '.' if depth == 1 && self.peek_at(1) == Some('.') => has_comma_or_range = true,
                    ' ' | '\t' | '\n' | '\r' => break,
                    _ => {}
                }
                self.bump();
                raw.push(ch);
            }
            if ok && has_comma_or_range {
                let id = self.next_id_between(start, self.pos());
                return Ok(Token::new(id, InnerToken::T_Literal(raw)));
            }
            // Not an expansion: emit a bare `{` literal, rewinding the scan.
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

    fn read_proc_sub(&mut self) -> PResult<Token> {
        let start = self.pos();
        let dir = self.one_of("<>")?;
        self.char('(')?;
        let sub_start = self.pos();
        let raw = self.read_balanced_parens_until_close()?;
        let list = self.subparse_commands(&raw, sub_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_ProcSub { op: dir.to_string(), list }))
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
        Ok(Token::new(id, InnerToken::T_Extglob { op: op.to_string(), list: parts }))
    }

    fn read_backticked(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('`')?;
        // collect raw until closing backtick, then subparse
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
        let cmds = self.subparse_commands(&raw, sub_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Backticked(cmds)))
    }

    // ---- dollar expansions -------------------------------------------------

    fn read_normal_dollar(&mut self) -> PResult<Token> {
        // ensureDollar
        if self.peek() != Some('$') {
            return Err(());
        }
        if let Ok(t) = self.read_dollar_exp() {
            return Ok(t);
        }
        // $'...'
        if let Ok(t) = self.read_dollar_single_quote() {
            return Ok(t);
        }
        // $"..."
        if let Ok(t) = self.read_dollar_double_quote() {
            return Ok(t);
        }
        self.read_dollar_lonely()
    }

    fn read_double_quoted_dollar(&mut self) -> PResult<Token> {
        if self.peek() != Some('$') {
            return Err(());
        }
        if let Ok(t) = self.read_dollar_exp() {
            return Ok(t);
        }
        self.read_dollar_lonely()
    }

    fn read_dollar_exp(&mut self) -> PResult<Token> {
        // arithmetic $((, expansion $(, bracket $[, braced ${, variable $x
        let m = self.mark();
        if self.peek() == Some('$') && self.peek_at(1) == Some('(') && self.peek_at(2) == Some('(') {
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
        if self.peek() == Some('$') && self.peek_at(1) == Some('{') {
            return self.read_dollar_braced();
        }
        self.read_dollar_variable()
    }

    fn read_dollar_arithmetic(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$((")?;
        let inner_start = self.pos();
        let raw = self.read_balanced_parens_until_double_close()?;
        let arith = self.make_arith_literal(&raw, inner_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarArithmetic(arith)))
    }

    fn read_dollar_bracket(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$[")?;
        let inner_start = self.pos();
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
        let arith = self.make_arith_literal(&raw, inner_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarBracket(arith)))
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
        // read braced word: everything up to matching }
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
        // Represent the braced content as a NormalWord of a single literal for now.
        let inner = self.make_literal_word(&raw, word_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarBraced { braced: true, op: inner }))
    }

    fn read_dollar_variable(&mut self) -> PResult<Token> {
        let start = self.pos();
        let pos = self.pos();
        self.char('$')?;
        // positional / special / regular
        if let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.bump();
                let word = self.make_literal_word(&c.to_string(), pos.clone());
                let id = self.next_id_between(start, self.pos());
                if let Some(n) = self.peek() {
                    if n.is_ascii_digit() {
                        let p = self.pos();
                        self.note_at(pos, p, Severity::ErrorC, 1037,
                            "Braces are required for positionals over 9, e.g. ${10}.");
                    }
                }
                return Ok(Token::new(id, InnerToken::T_DollarBraced { braced: false, op: word }));
            }
            if "$?!#-@*".contains(c) {
                self.bump();
                let word = self.make_literal_word(&c.to_string(), pos);
                let id = self.next_id_between(start, self.pos());
                return Ok(Token::new(id, InnerToken::T_DollarBraced { braced: false, op: word }));
            }
            if c == '_' || c.is_ascii_alphabetic() {
                let name = self.read_variable_name()?;
                let word = self.make_literal_word(&name, pos);
                let id = self.next_id_between(start, self.pos());
                return Ok(Token::new(id, InnerToken::T_DollarBraced { braced: false, op: word }));
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
                Some('`') => parts.push(self.read_backticked()?),
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

    fn make_literal_word(&mut self, s: &str, start: Position) -> Token {
        let lit_id = self.next_id_between(start.clone(), self.pos());
        let lit = Token::new(lit_id, InnerToken::T_Literal(s.to_string()));
        let wid = self.next_id_between(start, self.pos());
        Token::new(wid, InnerToken::T_NormalWord(vec![lit]))
    }

    fn make_arith_literal(&mut self, s: &str, start: Position) -> Token {
        // Placeholder: arithmetic contents kept as a literal token. Full
        // arithmetic parsing (TA_*) is ported later; downstream checks that need
        // structure will drive it.
        let id = self.next_id_between(start, self.pos());
        Token::new(id, InnerToken::T_Literal(s.to_string()))
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

    fn read_balanced_parens_until_double_close(&mut self) -> PResult<String> {
        // for $(( .. )) : read until )) at depth 0
        let mut raw = String::new();
        let mut depth = 0i32;
        loop {
            match self.peek() {
                None => return Err(()),
                Some('(') => {
                    depth += 1;
                    self.bump();
                    raw.push('(');
                }
                Some(')') => {
                    if depth == 0 && self.peek_at(1) == Some(')') {
                        self.bump();
                        self.bump();
                        break;
                    }
                    depth -= 1;
                    self.bump();
                    raw.push(')');
                }
                Some(c) => {
                    self.bump();
                    raw.push(c);
                }
            }
        }
        Ok(raw)
    }

    /// Subparse a fragment as a compound list, in a nested parser sharing the id
    /// space and position/note collections. Positions are offset by `start`.
    fn subparse_commands(&mut self, raw: &str, _start: Position) -> Vec<Token> {
        // For fidelity we parse the fragment with a fresh sub-parser but continue
        // id numbering and merge positions/notes. Line/col offsetting is
        // approximate for now (positions inside command substitutions are refined
        // later); most checks key off structure, not inner-substitution columns.
        let mut sub = Parser::new(&self.filename, raw);
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
                    self.line_break();
                    let start = self.span_for(left.id()).0;
                    let right = self.read_pipeline()?;
                    let end = self.span_for(right.id()).1;
                    let id = self.next_id_between(start, end);
                    left = if is_and {
                        Token::new(id, InnerToken::T_AndIf { lhs: left, rhs: right })
                    } else {
                        Token::new(id, InnerToken::T_OrIf { lhs: left, rhs: right })
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
            Ok(Token::new(id, InnerToken::T_Annotation { annotations, token: left }))
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

    fn read_pipe_sequence(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut cmds = Vec::new();
        let mut pipes = Vec::new();
        let first = self.read_command()?;
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
                match self.read_command() {
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
        Ok(Token::new(id, InnerToken::T_Pipeline { separators: pipes, commands: cmds }))
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
        self.read_simple_command()
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
            Some('(') if self.peek_at(1) == Some('(') => self.read_arithmetic_command(),
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
                } else if self.keyword_ahead("function") {
                    self.read_function_def()
                } else if self.peek() == Some('(') && self.peek_at(1) == Some('(') {
                    self.read_arithmetic_command()
                } else {
                    Err(())
                }
            }
        };
        match cmd {
            Ok(t) => {
                // compound commands may carry redirections
                let redirs = self.read_redirect_list();
                if redirs.is_empty() {
                    Ok(t)
                } else {
                    let (s, _) = self.span_for(t.id());
                    let e = self.pos();
                    let id = self.next_id_between(s, e);
                    Ok(Token::new(id, InnerToken::T_Redirecting { redirs, cmd: t }))
                }
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
        self.consume_keyword("}").or_else(|_| self.char('}').map(|_| ()))?;
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
        Ok(Token::new(id, InnerToken::T_IfExpression { clauses, elses }))
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
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_WhileExpression { condition: cond, body }))
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
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_UntilExpression { condition: cond, body }))
    }

    fn read_for_clause(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("for")?;
        self.spacing();
        // arithmetic for: for ((...))
        if self.peek() == Some('(') && self.peek_at(1) == Some('(') {
            // simplified: skip to )) then do..done
            self.string("((")?;
            let _ = self.read_balanced_parens_until_double_close();
            self.allspacing();
            let _ = self.char(';');
            self.allspacing();
            self.consume_keyword("do")?;
            let body = self.read_compound_list_or_empty();
            self.allspacing();
            self.consume_keyword("done")?;
            let id = self.next_id_between(start, self.pos());
            let zero = self.empty_literal();
            let one = self.empty_literal();
            let two = self.empty_literal();
            return Ok(Token::new(id, InnerToken::T_ForArithmetic { init: zero, cond: one, step: two, body }));
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
                if self.peek() == Some(';') || self.peek() == Some('\n') || self.peek() == Some('\r') {
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
        let id = self.next_id_between(start, self.pos());
        let _ = is_in;
        Ok(Token::new(id, InnerToken::T_ForIn { var, items, body }))
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

    fn read_case_body(&mut self) -> Vec<Token> {
        // read a compound list until ;; / ;& / ;;& / esac
        self.allspacing();
        if self.keyword_ahead("esac") || self.peek() == Some(';') {
            return Vec::new();
        }
        match self.read_and_or() {
            Ok(first) => {
                // read term-more but stop at ;;
                let mut out = vec![first];
                loop {
                    let m = self.mark();
                    self.spacing();
                    if self.peek() == Some(';') {
                        self.reset(m);
                        break;
                    }
                    if let Some((sep, (s, e))) = self.read_separator() {
                        let _ = sep;
                        let _ = (s, e);
                        self.allspacing();
                        if self.peek() == Some(';') || self.keyword_ahead("esac") {
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
            Err(()) => Vec::new(),
        }
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
        Ok(Token::new(id, InnerToken::T_Function {
            keyword: true,
            parens: has_parens,
            name,
            body,
        }))
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
        let inner_start = self.pos();
        let raw = self.read_balanced_parens_until_double_close()?;
        let arith = self.make_arith_literal(&raw, inner_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Arithmetic(arith)))
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
        if cmd.is_some() {
            suffix = self.read_cmd_suffix();
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
        let simple = Token::new(id2, InnerToken::T_SimpleCommand { assignments: assigns, words: cmd_args });
        Ok(Token::new(id1, InnerToken::T_Redirecting { redirs, cmd: simple }))
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

    fn read_cmd_suffix(&mut self) -> Vec<Token> {
        let mut out = Vec::new();
        loop {
            self.spacing();
            if let Ok(r) = self.read_io_redirect() {
                out.push(r);
                continue;
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

    fn read_assignment_word(&mut self) -> PResult<Token> {
        let start = self.pos();
        // name
        let name = self.read_variable_name()?;
        // optional [index]
        let mut indices = Vec::new();
        if self.peek() == Some('[') {
            let istart = self.pos();
            self.bump();
            let mut raw = String::new();
            let mut depth = 1;
            while let Some(c) = self.peek() {
                if c == '[' { depth += 1; }
                else if c == ']' { depth -= 1; if depth == 0 { break; } }
                self.bump();
                raw.push(c);
            }
            self.char(']')?;
            let idxw = self.make_literal_word(&raw, istart);
            indices.push(idxw);
        }
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
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Assignment { mode, var: name, indices, value }))
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
        // heredoc
        if self.peek() == Some('<') && self.peek_at(1) == Some('<') {
            return self.read_heredoc_or_herestring(start, fd);
        }
        // dup: <& or >&
        if (self.peek() == Some('<') || self.peek() == Some('>')) && self.peek_at(1) == Some('&') {
            let opc = self.bump().unwrap();
            self.bump(); // &
            let mut num = String::new();
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() || c == '-' {
                    num.push(c);
                    self.bump();
                } else {
                    break;
                }
            }
            let opid = self.next_id_between(start.clone(), self.pos());
            let op_tok = Token::new(opid, if opc == '<' { InnerToken::T_LESSAND } else { InnerToken::T_GREATAND });
            let dup_id = self.next_id_between(start.clone(), self.pos());
            let dup = Token::new(dup_id, InnerToken::T_IoDuplicate { op: op_tok, num });
            let id = self.next_id_between(start, self.pos());
            return Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: dup }));
        }
        // file redirect operators
        let op = self.read_io_file_op(start.clone());
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
                let iofile_id = self.next_id_between(start.clone(), self.pos());
                let iofile = Token::new(iofile_id, InnerToken::T_IoFile { op: op_tok, file });
                let id = self.next_id_between(start, self.pos());
                Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: iofile }))
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

    fn read_heredoc_or_herestring(&mut self, start: Position, fd: String) -> PResult<Token> {
        // << , <<- , <<<
        self.string("<<")?;
        if self.char('<').is_ok() {
            // here string
            self.spacing();
            let word = self.read_normal_word()?;
            let hs_id = self.next_id_between(start.clone(), self.pos());
            let hs = Token::new(hs_id, InnerToken::T_HereString(word));
            let id = self.next_id_between(start, self.pos());
            return Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: hs }));
        }
        let dashed = if self.char('-').is_ok() { Dashed::Dashed } else { Dashed::Undashed };
        self.spacing();
        // delimiter (may be quoted)
        let (delim, quoted) = self.read_heredoc_delim()?;
        // Body is read lazily at next newline; for the slice, capture nothing now
        // and register a pending heredoc.
        let hd_id = self.next_id_between(start.clone(), self.pos());
        self.pending_heredocs.push(PendingHereDoc { dashed, quoted, delim: delim.clone(), id: hd_id });
        let hd = Token::new(hd_id, InnerToken::T_HereDoc { dashed, quoted, delim, body: Vec::new() });
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: hd }))
    }

    fn read_heredoc_delim(&mut self) -> PResult<(String, Quoted)> {
        match self.peek() {
            Some('\'') => {
                self.bump();
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    if c == '\'' { break; }
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
                    if c == '"' { break; }
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
                if s.is_empty() { Err(()) } else { Ok((s, Quoted::Unquoted)) }
            }
        }
    }

    fn read_pending_heredocs(&mut self) {
        if self.pending_heredocs.is_empty() {
            return;
        }
        let pending: Vec<PendingHereDoc> = std::mem::take(&mut self.pending_heredocs);
        for hd in pending {
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
            // store body as a single literal
            let bstart = Position::default();
            let lit_id = self.next_id_between(bstart.clone(), bstart);
            let lit = Token::new(lit_id, InnerToken::T_Literal(body));
            self.heredoc_bodies.insert(hd.id, vec![lit]);
        }
    }

    // ---- script entry ------------------------------------------------------

    fn read_script_file(&mut self) -> Option<Token> {
        let start = self.pos();
        // UTF-8 BOM
        let _ = self.string("\u{FEFF}");
        let shebang = self.read_shebang().unwrap_or_else(|| self.empty_literal());
        self.allspacing();
        // File-wide shellcheck directives after the shebang.
        let file_annotations = self.read_annotations();
        self.allspacing();
        let commands = self.read_compound_list_or_empty();
        self.read_pending_heredocs();
        // verify EOF: if not at end, it's a parse problem (SC1072-ish). For the
        // slice we record a generic problem but still return the tree.
        self.allspacing();
        if !self.eof() {
            let p = self.pos();
            self.problem_at(p.clone(), p, Severity::ErrorC, 1072,
                "Unexpected input near here.");
        }
        let script_id = self.next_id_between(start.clone(), self.pos());
        let script = Token::new(script_id, InnerToken::T_Script { shebang, commands });
        let ann_id = self.next_id_between(start.clone(), self.pos());
        let root = Token::new(ann_id, InnerToken::T_Annotation { annotations: file_annotations, token: script });
        Some(root)
    }
}

/// Public entry point mirroring `ShellCheck.Parser.parseScript`.
pub fn parse_script(filename: &str, script: &str) -> ParseOutput {
    let mut p = Parser::new(filename, script);
    let root = p.read_script_file();
    // Reattach here-doc bodies collected during parsing.
    let root = root.map(|r| reattach_heredocs(r, &p.heredoc_bodies));
    // Parse succeeded (we always return a tree in the slice); emit notes+problems.
    let mut notes = p.problems.clone();
    notes.extend(p.notes.clone());
    ParseOutput { root, notes, positions: p.positions }
}

fn reattach_heredocs(t: Token, bodies: &BTreeMap<Id, Vec<Token>>) -> Token {
    // Rebuild the tree, filling T_HereDoc bodies by id.
    let Token { id, inner } = t;
    let new_inner = map_children_inner(*inner, bodies, id);
    Token { id, inner: Box::new(new_inner) }
}

fn map_children_inner(inner: InnerToken, bodies: &BTreeMap<Id, Vec<Token>>, id: Id) -> InnerToken {
    use InnerToken::*;
    // Special-case heredoc body fill.
    if let T_HereDoc { dashed, quoted, delim, .. } = &inner {
        if let Some(body) = bodies.get(&id) {
            return T_HereDoc {
                dashed: *dashed,
                quoted: *quoted,
                delim: delim.clone(),
                body: body.iter().cloned().map(|b| reattach_heredocs(b, bodies)).collect(),
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
            $v.into_iter().map(|x| reattach_heredocs(x, bodies)).collect()
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
        T_Extglob { op, list } => T_Extglob { op, list: rv!(list) },
        T_ProcSub { op, list } => T_ProcSub { op, list: rv!(list) },
        T_DollarArithmetic(t) => T_DollarArithmetic(r!(t)),
        T_DollarBracket(t) => T_DollarBracket(r!(t)),
        T_Arithmetic(t) => T_Arithmetic(r!(t)),
        T_Backgrounded(t) => T_Backgrounded(r!(t)),
        T_Banged(t) => T_Banged(r!(t)),
        T_HereString(t) => T_HereString(r!(t)),
        T_DollarBraced { braced, op } => T_DollarBraced { braced, op: r!(op) },
        T_AndIf { lhs, rhs } => T_AndIf { lhs: r!(lhs), rhs: r!(rhs) },
        T_OrIf { lhs, rhs } => T_OrIf { lhs: r!(lhs), rhs: r!(rhs) },
        T_Pipeline { separators, commands } => T_Pipeline { separators: rv!(separators), commands: rv!(commands) },
        T_Redirecting { redirs, cmd } => T_Redirecting { redirs: rv!(redirs), cmd: r!(cmd) },
        T_SimpleCommand { assignments, words } => T_SimpleCommand { assignments: rv!(assignments), words: rv!(words) },
        T_Assignment { mode, var, indices, value } => T_Assignment { mode, var, indices: rv!(indices), value: r!(value) },
        T_IfExpression { clauses, elses } => T_IfExpression {
            clauses: clauses.into_iter().map(|(c, b)| (rv!(c), rv!(b))).collect(),
            elses: rv!(elses),
        },
        T_WhileExpression { condition, body } => T_WhileExpression { condition: rv!(condition), body: rv!(body) },
        T_UntilExpression { condition, body } => T_UntilExpression { condition: rv!(condition), body: rv!(body) },
        T_ForIn { var, items, body } => T_ForIn { var, items: rv!(items), body: rv!(body) },
        T_ForArithmetic { init, cond, step, body } => T_ForArithmetic { init: r!(init), cond: r!(cond), step: r!(step), body: rv!(body) },
        T_CaseExpression { word, cases } => T_CaseExpression {
            word: r!(word),
            cases: cases.into_iter().map(|(t, p, b)| (t, rv!(p), rv!(b))).collect(),
        },
        T_Function { keyword, parens, name, body } => T_Function { keyword, parens, name, body: r!(body) },
        T_Script { shebang, commands } => T_Script { shebang: r!(shebang), commands: rv!(commands) },
        T_Annotation { annotations, token } => T_Annotation { annotations, token: r!(token) },
        T_IoFile { op, file } => T_IoFile { op: r!(op), file: r!(file) },
        T_IoDuplicate { op, num } => T_IoDuplicate { op: r!(op), num },
        T_FdRedirect { fd, target } => T_FdRedirect { fd, target: r!(target) },
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
            let mut anns = self.read_annotation_value(&key);
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

    fn read_annotation_value(&mut self, key: &str) -> Vec<Annotation> {
        match key {
            "disable" => {
                let raw = self.read_annotation_raw_value();
                raw.split(',')
                    .filter_map(parse_disable_element)
                    .collect()
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
                if crate::astlib::shell_for_executable(&v).is_none() {
                    self.note_at(pos.clone(), pos, Severity::ErrorC, 1103,
                        "This shell type is unknown. Use e.g. sh or bash.");
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
                let pos = self.pos();
                let _ = self.read_annotation_raw_value();
                self.note_at(pos.clone(), pos, Severity::WarningC, 1107,
                    "This directive is unknown. It will be ignored.");
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
