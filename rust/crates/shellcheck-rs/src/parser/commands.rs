//! Lists, pipelines, simple commands, redirections, here-docs and the script entry (`ShellCheck.Parser` readScript / readSimpleCommand family).
use super::*;

/// Which `readCmdSuffix` variant a command's arguments get: the plain one,
/// `readModifierSuffix` (assignments stay assignments) or `readEvalSuffix`
/// (a bare `(` is warned about before it fails).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum CmdSuffix {
    Plain,
    Modifier,
    Eval,
}

impl Parser {
    pub(super) fn empty_literal(&mut self) -> Token {
        let p = self.pos();
        let id = self.next_id_between(p.clone(), p);
        Token::new(id, InnerToken::T_Literal(String::new()))
    }

    /// `readShebang`: the first line, in any of the forms people get wrong.
    pub(super) fn read_shebang(&mut self) -> Option<Token> {
        let start = self.pos();
        let m = self.mark();
        // `anyShebang <|> try readMissingBang <|> withHeader`
        if !(self.any_shebang() || self.read_missing_bang() || self.shebang_with_header()) {
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
        let _ = self.carriage_return();
        let _ = self.char('\n');
        Some(Token::new(id, InnerToken::T_Literal(s)))
    }

    /// `anyShebang`: `#!`, or one of the three near misses, each behind a `try`.
    fn any_shebang(&mut self) -> bool {
        if self.string("#!").is_ok() {
            return true;
        }
        // `readSwapped`
        let m = self.mark();
        let start = self.pos();
        if self.string("!#").is_ok() {
            let end = self.pos();
            self.problem_at(
                start,
                end,
                Severity::ErrorC,
                1084,
                "Use #!, not !#, for the shebang.",
            );
            return true;
        }
        self.reset(m);
        // `readTooManySpaces`
        let start_pos = self.pos();
        let start_spaces = self.skip_line_whitespace();
        if self.char('#').is_ok() {
            let middle_pos = self.pos();
            let middle_spaces = self.skip_line_whitespace();
            if self.char('!').is_ok() {
                if start_spaces {
                    self.problem_at(
                        start_pos.clone(),
                        start_pos,
                        Severity::ErrorC,
                        1114,
                        "Remove leading spaces before the shebang.",
                    );
                }
                if middle_spaces {
                    self.problem_at(
                        middle_pos.clone(),
                        middle_pos,
                        Severity::ErrorC,
                        1115,
                        "Remove spaces between # and ! in the shebang.",
                    );
                }
                return true;
            }
        }
        self.reset(m);
        // `readMissingHash`
        let pos = self.pos();
        if self.char('!').is_ok() && self.ensure_path_ahead() {
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1104,
                "Use #!, not just !, for the shebang.",
            );
            return true;
        }
        self.reset(m);
        false
    }

    /// `readMissingBang`: a `#` where a `#!` was meant, path and all.
    fn read_missing_bang(&mut self) -> bool {
        let m = self.mark();
        if self.char('#').is_ok() {
            let pos = self.pos();
            if self.ensure_path_ahead() {
                self.problem_at(
                    pos.clone(),
                    pos,
                    Severity::ErrorC,
                    1113,
                    "Use #!, not just #, for the shebang.",
                );
                return true;
            }
        }
        self.reset(m);
        false
    }

    /// `withHeader`: a shebang below a block of comments and blank lines.
    fn shebang_with_header(&mut self) -> bool {
        let m = self.mark();
        if !self.shebang_header_line() {
            self.reset(m);
            return false;
        }
        while self.shebang_header_line() {}
        let pos = self.pos();
        if self.any_shebang() {
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1128,
                "The shebang must be on the first line. Delete blanks and move comments.",
            );
            return true;
        }
        self.reset(m);
        false
    }

    /// `headerLine`: whitespace and at most a comment, ending in a linefeed —
    /// and not itself a shebang.
    fn shebang_header_line(&mut self) -> bool {
        let m = self.mark();
        // `notFollowedBy2 anyShebang`. What it reports on the way is not rolled
        // back (problems live outside Parsec), but `anyShebang` runs again once
        // the header ends, and `nub` collapses the repeat.
        let sm = self.mark();
        if self.any_shebang() {
            self.reset(sm);
            self.reset(m);
            return false;
        }
        self.reset(sm);
        self.skip_line_whitespace();
        let _ = self.read_any_comment();
        if self.char('\n').is_ok() {
            return true;
        }
        self.reset(m);
        false
    }

    /// `skipSpaces`: true when there was whitespace to skip.
    fn skip_line_whitespace(&mut self) -> bool {
        let mut any = false;
        while self.line_whitespace().is_ok() {
            any = true;
        }
        any
    }

    /// `ensurePathAhead`: a `/` after optional whitespace, not consumed.
    fn ensure_path_ahead(&mut self) -> bool {
        let m = self.mark();
        self.skip_line_whitespace();
        let ok = self.peek() == Some('/');
        self.reset(m);
        ok
    }

    // ---- separators --------------------------------------------------------

    /// `g_Semi = notFollowedBy2 g_DSEMI >> tryToken ";" T_Semi`: a single `;`,
    /// and never the first half of a `;;`.
    pub(super) fn g_semi(&mut self) -> PResult<()> {
        if self.peek() == Some(';') && self.peek_at(1) == Some(';') {
            // `unexpecting ""` reads `g_DSEMI` before failing, and `tryToken`
            // takes the spacing after its string too, so the error sits past
            // both characters and whatever followed them; the `try` keeps the
            // cursor here.
            self.fail_after("Unexpected ", |p| {
                p.bump();
                p.bump();
                p.spacing();
            });
            return Err(());
        }
        self.char(';')?;
        self.spacing();
        Ok(())
    }

    pub(super) fn read_separator_op(&mut self) -> Option<char> {
        // `notFollowedBy2 (void g_AND_IF <|> void readCaseSeparator)`, whose
        // last arm is `lookAhead (readLineBreak >> g_Esac)`: `g_Esac` reads as
        // much of `esac` as matches before it fails, so a command that ends
        // in `e` (`function f{(c)e`) leaves Parsec's error one past it, with
        // nothing to say, and that is what its failure reports.
        //
        // `unexpecting` wraps it in `try`, and the whole attempt is bound to
        // fail here, so the `try` is what puts everything back: the cursor,
        // the notes, the here documents `readLineBreak` read on the way and
        // the commitment an unterminated one of them made. The error it got
        // to stays, merged into the `<|> return ()` that follows -- which is
        // how an unparsable here document ends the parse where the *body*
        // gave up rather than at the line feed.
        let _: PResult<()> = self.try_parse(|p| {
            p.line_break();
            p.keyword_attempt_failure("esac");
            Err(())
        });
        match self.peek() {
            Some('&') if self.peek_at(1) != Some('&') => {
                let pos = self.pos();
                self.bump();
                // What follows a `&` usually means it was not meant to
                // background anything.
                if ["amp;", "gt;", "lt;"].iter().any(|s| self.string_peek(s)) {
                    self.problem_at(
                        pos.clone(),
                        pos.clone(),
                        Severity::ErrorC,
                        1109,
                        "This is an unquoted HTML entity. Replace with corresponding character.",
                    );
                } else if matches!(self.peek(), Some(c) if c == '_' || c.is_ascii_alphabetic()) {
                    self.problem_at(
                        pos.clone(),
                        pos,
                        Severity::WarningC,
                        1132,
                        "This & terminates the command. Escape it or add space after & to silence.",
                    );
                }
                // `a &; b` is a `&` with a stray `;` after it.
                let m = self.mark();
                self.spacing();
                let semi = self.pos();
                if self.char(';').is_ok() && self.peek() != Some(';') {
                    self.problem_at(
                        semi.clone(),
                        semi,
                        Severity::ErrorC,
                        1045,
                        "It's not 'foo &; bar', just 'foo & bar'.",
                    );
                } else {
                    self.reset(m);
                }
                Some('&')
            }
            Some(';') if matches!(self.peek_at(1), Some(';') | Some('&')) => {
                // `notFollowedBy2 (void g_AND_IF <|> void readCaseSeparator)`,
                // and `notFollowedBy2` is `unexpecting ""`: it reads the case
                // separator -- `;;&`, `;&` or `;;`, and the spacing after it,
                // as `tryToken` does -- and then fails with "Unexpected ",
                // which is where Parsec's error ends up.
                let m = self.mark();
                let dsemi = self.peek_at(1) == Some(';');
                self.bump();
                self.bump();
                if dsemi && self.peek() == Some('&') {
                    self.bump();
                }
                self.spacing();
                let _: PResult<()> = self.fail_recoverable("Unexpected ");
                self.reset(m);
                None
            }
            Some(';') => {
                self.bump();
                Some(';')
            }
            _ => None,
        }
    }

    /// Returns (separator_char, (start,end)) or None.
    pub(super) fn read_separator(&mut self) -> Option<(char, (Position, Position))> {
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

    pub(super) fn newline_list(&mut self) {
        // `many1 ((linefeed <|> carriageReturn) `thenSkip` spacing) <*
        // checkBadBreak`: the spacing comes after each newline, so it takes a
        // comment on the following line with it, and the check only runs once
        // at least one newline was consumed (`many1`).
        let mut any = false;
        loop {
            let m = self.mark();
            if self.linefeed_or_carriage_return().is_err() {
                self.reset(m);
                break;
            }
            any = true;
            self.spacing();
        }
        if any {
            self.check_bad_break();
        }
    }

    // ---- terms / and-or / pipelines ---------------------------------------

    pub(super) fn read_compound_list_or_empty(&mut self) -> Vec<Token> {
        self.allspacing();
        let m = self.mark();
        match self.read_term() {
            Some(t) => t,
            None => {
                // `readTerm <|> return []` only recovers a failure that
                // consumed nothing.
                if self.idx != m.idx {
                    self.commit();
                }
                self.reset(m);
                Vec::new()
            }
        }
    }

    pub(super) fn read_term(&mut self) -> Option<Vec<Token>> {
        self.allspacing();
        let first = self.read_and_or().ok()?;
        self.read_term_more(first).ok()
    }

    pub(super) fn read_term_more(&mut self, current: Token) -> PResult<Vec<Token>> {
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
                    v.extend(self.read_term_more(next)?);
                    Ok(v)
                }
                Err(()) => {
                    // `option (T_EOF id) readAndOr`: a failure that consumed
                    // input is out of reach of that `option`, and of the
                    // `<|> return [current]` around it.
                    if self.idx != m.idx {
                        return Err(());
                    }
                    self.reset(m);
                    Ok(vec![node])
                }
            }
        } else {
            Ok(vec![current])
        }
    }

    pub(super) fn read_and_or(&mut self) -> PResult<Token> {
        let ann_start = self.pos();
        let annotations = self.read_annotations();
        self.allspacing_no_newline();
        // `withAnnotations annotations $ chainl1 readPipeline ..`: the
        // directives cover the command they precede, and what it reports.
        // `unless (null annotations) $ optional $ do { try . lookAhead $
        // readKeyword; SC1123 }`: a directive in front of a keyword is in front
        // of half a compound command.
        if !annotations.is_empty() && self.keyword_len().is_some() {
            self.problem_at(
                ann_start.clone(),
                ann_start.clone(),
                Severity::ErrorC,
                1123,
                "ShellCheck directives are only valid in front of complete compound commands, like 'if', not e.g. individual 'elif' branches.",
            );
        }
        let left = self.with_annotations(&annotations, |p| p.read_and_or_chain())?;
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

    /// `chainl1 readPipeline (g_AND_IF <|> g_OR_IF)`.
    fn read_and_or_chain(&mut self) -> PResult<Token> {
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
        Ok(left)
    }

    pub(super) fn allspacing_no_newline(&mut self) {
        self.spacing();
    }

    pub(super) fn read_pipeline(&mut self) -> PResult<Token> {
        // `unexpecting "keyword/token" readKeyword`: a word that closes a
        // compound command cannot start one. The keyword is read and then
        // rejected, so the error lands past it, and the whole thing sits in a
        // `try`, so an enclosing alternative can still take over.
        if let Some(n) = self.keyword_end() {
            let m = self.mark();
            // The `fail` inside the inner `try` happens from where the keyword
            // token left off -- before the outer one rewinds -- so that is
            // where the error lands.
            for _ in 0..n {
                self.bump();
            }
            let r = self.fail_recoverable("Unexpected keyword/token");
            self.reset(m);
            return r;
        }
        self.read_banged()
    }

    /// How far past the closing keyword ahead `readKeyword` leaves the cursor:
    /// its length, and then the spacing after it for every one of them but
    /// `}`. `tryToken` and `tryWordToken` both end `spacing`; `g_Rbrace` is a
    /// bare `char '}'`, handled specially so ksh's `${ foo; }bar` closes where
    /// it should. A caller that reads the keyword only to reject it still has
    /// to stop where Parsec would, since that is where the error is reported.
    pub(super) fn keyword_end(&mut self) -> Option<usize> {
        let n = self.keyword_len()?;
        let takes_spacing = self.peek() != Some('}');
        let m = self.mark();
        for _ in 0..n {
            self.bump();
        }
        if takes_spacing {
            self.spacing();
        }
        let end = self.idx;
        self.reset(m);
        Some(end - m.idx)
    }

    /// `readKeyword`: how long the closing keyword ahead is, plus the
    /// missing-space warning each word token leaves behind even when the
    /// lookahead that called it goes on to reject the keyword.
    /// What a `tryWordToken w` that does not match leaves behind. `anycaseString`
    /// reads the keyword a character at a time, so a prefix that matches -- the
    /// `e` of `ex` against `esac` -- is read before the mismatch fails, and a
    /// full match still has `lookAhead keywordSeparator` to fail on past the
    /// word. Parsec's error sits there either way, and the `try` around the
    /// token keeps that position.
    pub(super) fn keyword_attempt_failure(&mut self, w: &str) {
        let prefix = w
            .chars()
            .enumerate()
            .take_while(|(i, ch)| matches!(self.peek_at(*i), Some(c) if c.eq_ignore_ascii_case(ch)))
            .count();
        if prefix == 0 {
            return;
        }
        if prefix < w.chars().count() {
            self.fail_past(prefix, "");
        } else if !self.at_keyword_separator(prefix) {
            // The whole word is there and what refused is `keywordSeparator`,
            // whose `allspacingOrFail` is the only alternative in it with
            // anything to say.
            self.fail_past(prefix, "Expected whitespace");
        }
    }

    pub(super) fn keyword_len(&mut self) -> Option<usize> {
        const WORDS: [&str; 7] = ["then", "else", "elif", "fi", "do", "done", "esac"];
        // Every alternative in the `choice` is attempted, so a longer keyword
        // sharing a prefix with a shorter one still gets its own warning.
        let mut found = None;
        for w in WORDS {
            if !self.word_matches(w) {
                self.keyword_attempt_failure(w);
                continue;
            }
            self.warn_keyword_needs_space(w);
            if !self.at_keyword_separator(w.len()) {
                // `lookAhead keywordSeparator` fails past the word.
                self.fail_past(w.len(), "Expected whitespace");
            } else if found.is_none() {
                found = Some(w.len());
            }
        }
        for w in WORDS {
            self.miscased_keyword(w);
        }
        if found.is_some() {
            return found;
        }
        match self.peek() {
            // `g_Rbrace` is a bare `char '}'` with no word boundary, so that
            // ksh's `${ foo; }bar` closes where it should.
            Some('}') => Some(1),
            Some(')') => Some(1),
            Some(';') if self.peek_at(1) == Some(';') => Some(2),
            _ => None,
        }
    }

    /// `g_Bang`: a `!` in command position. The space after it is required, so
    /// a missing one is a problem rather than a reason to read `!` as a word.
    fn g_bang(&mut self) -> PResult<Id> {
        let start = self.pos();
        self.char('!')?;
        let id = self.next_id_between(start, self.pos());
        let m = self.mark();
        if self.spacing1().is_err() {
            // `void spacing1 <|> parseProblemAt ..`: the alternative is only
            // reachable while nothing was consumed. `!#` reads the comment and
            // still has no whitespace to show for it, so the `!` is fatal.
            if self.idx != m.idx {
                return Err(());
            }
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1035,
                "You are missing a required space after the !.",
            );
        }
        Ok(id)
    }

    pub(super) fn read_banged(&mut self) -> PResult<Token> {
        // `readBanged parser = (g_Bang >> readBanged parser) <|> parser`: past
        // the `!` there is no alternative left.
        if self.peek() == Some('!') {
            let bang_id = self.g_bang()?;
            let m = self.mark();
            match self.read_banged() {
                Ok(inner) => return Ok(Token::new(bang_id, InnerToken::T_Banged(inner))),
                Err(()) => {
                    if self.idx != m.idx
                        || self.has_committed_failure()
                        || !self.empty_negation_ok()
                    {
                        return Err(());
                    }
                    // A deliberate deviation from upstream, which rejects this
                    // for every dialect and so throws away the whole file's
                    // analysis over a line bash runs. See PARITY-NOTES.md,
                    // `upstream-false-parse-error`.
                    let here = self.pos();
                    let id = self.next_id_between(here.clone(), here);
                    let nothing = Token::new(
                        id,
                        InnerToken::T_Pipeline {
                            separators: Vec::new(),
                            commands: Vec::new(),
                        },
                    );
                    return Ok(Token::new(bang_id, InnerToken::T_Banged(nothing)));
                }
            }
        }
        self.read_pipe_sequence()
    }

    /// May a `!` stand with nothing to negate here?
    ///
    /// bash takes it — `!` negates the null command, so `! ; echo $?` prints 1
    /// — while dash and the other POSIX shells reject it. The shells only allow
    /// it before the end of a line or a single `;`: `! &`, `! ;;`, `! | x`,
    /// `! && x` and `( ! )` are syntax errors in bash too.
    ///
    /// `!#` is not this case at all: `#` opens a comment only at the start of a
    /// word, so `!#` is one word and every shell treats it as a command name.
    /// That keeps upstream's reading, and its error.
    fn empty_negation_ok(&self) -> bool {
        if self.shell_hint.unwrap_or(Shell::Bash) != Shell::Bash {
            return false;
        }
        match self.peek() {
            // End of input only ends the list when nothing is still open:
            // `(!` is a syntax error in bash as much as anywhere, because the
            // subshell never closes, and upstream's reading of it is right.
            None => self.contexts.is_empty(),
            Some('\n') | Some('\r') => true,
            Some(';') => self.peek_at(1) != Some(';'),
            _ => false,
        }
    }

    /// `readBanged readCommand`: a single pipeline stage, which may itself be
    /// prefixed by one or more `!` (e.g. `true | ! true`, `! ! true`). Unlike
    /// `read_banged`, the fallback reads a single command, not a whole pipe
    /// sequence, so it can be used per-stage inside `read_pipe_sequence`.
    pub(super) fn read_banged_command(&mut self) -> PResult<Token> {
        if self.peek() == Some('!') {
            let bang_id = self.g_bang()?;
            let inner = self.read_banged_command()?;
            return Ok(Token::new(bang_id, InnerToken::T_Banged(inner)));
        }
        self.read_command()
    }

    pub(super) fn read_pipe_sequence(&mut self) -> PResult<Token> {
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
                // `chainl1`: the separator has consumed, so a command that
                // fails after it takes the pipeline down with it (`d|`).
                cmds.push(self.read_banged_command()?);
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

    pub(super) fn read_command(&mut self) -> PResult<Token> {
        // `choice` is a fold of bare `<|>`: once a compound command has
        // consumed input there is no going back to a simple one, so `((`
        // reports an unfinished arithmetic command rather than quietly
        // becoming a word.
        let m = self.mark();
        match self.read_compound_command() {
            Ok(t) => return Ok(t),
            Err(()) => {
                if self.idx != m.idx {
                    self.commit();
                    return Err(());
                }
            }
        }
        match self.read_condition_command() {
            Ok(t) => return Ok(t),
            Err(()) => {
                if self.idx != m.idx {
                    self.commit();
                    return Err(());
                }
            }
        }
        match self.read_coproc() {
            Ok(t) => return Ok(t),
            Err(()) => {
                if self.idx != m.idx {
                    self.commit();
                    return Err(());
                }
            }
        }
        // The last alternative in the `choice`: nothing can take over from a
        // simple command that failed after consuming input.
        let r = self.read_simple_command();
        if r.is_err() && self.idx != m.idx {
            self.commit();
        }
        r
    }

    /// Faithful port of `readCoProc` (Parser.hs). `coproc` + spacing, then either
    /// a compound form (optional name word + compound command body) or a simple
    /// form (a simple-command body). The body is wrapped in `T_CoProcBody`.
    pub(super) fn read_coproc(&mut self) -> PResult<Token> {
        self.called("coproc", |p| p.read_coproc_inner())
    }

    fn read_coproc_inner(&mut self) -> PResult<Token> {
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
        if let Ok(t) = self.try_parse(|p| p.read_compound_coproc(start.clone())) {
            return Ok(t);
        }
        self.read_simple_coproc(start)
    }

    pub(super) fn read_compound_coproc(&mut self, start: Position) -> PResult<Token> {
        // notFollowedBy2 readAssignmentWord
        let ma = self.mark();
        let is_assign = self.read_assignment_word().is_ok();
        self.reset(ma);
        if is_assign {
            return Err(());
        }
        // choice [ try (body only, no name), try (name word + body) ]
        if let Ok(body) = self.try_parse(|p| p.read_coproc_body(true)) {
            let id = self.next_id_between(start.clone(), self.pos());
            return Ok(Token::new(id, InnerToken::T_CoProc { name: None, body }));
        }
        self.try_parse(|p| {
            let var = p.read_normal_word()?;
            p.spacing();
            let body = p.read_coproc_body(true)?;
            let id = p.next_id_between(start, p.pos());
            Ok(Token::new(
                id,
                InnerToken::T_CoProc {
                    name: Some(var),
                    body,
                },
            ))
        })
    }

    pub(super) fn read_simple_coproc(&mut self, start: Position) -> PResult<Token> {
        let body = self.read_coproc_body(false)?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_CoProc { name: None, body }))
    }

    /// `readBody parser`: run `parser`, wrap its result in `T_CoProcBody`.
    pub(super) fn read_coproc_body(&mut self, compound: bool) -> PResult<Token> {
        let start = self.pos();
        let body = if compound {
            self.read_compound_command()?
        } else {
            self.read_simple_command()?
        };
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_CoProcBody(body)))
    }

    // ---- compound commands -------------------------------------------------

    pub(super) fn read_arithmetic_command(&mut self) -> PResult<Token> {
        self.called("((..)) command", |p| p.read_arithmetic_command_body())
    }

    fn read_arithmetic_command_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("((")?;
        let c = self.read_arithmetic_contents()?;
        self.string("))")?;
        // `endSpan` comes before the trailing `spacing`, so the node does not
        // stretch over it.
        let id = self.next_id_between(start, self.pos());
        self.spacing();
        Ok(Token::new(id, InnerToken::T_Arithmetic(c)))
    }

    // ---- simple command ----------------------------------------------------

    pub(super) fn read_simple_command(&mut self) -> PResult<Token> {
        self.called("simple command", |p| p.read_simple_command_body())
    }

    fn read_simple_command_body(&mut self) -> PResult<Token> {
        let prefix = self.read_cmd_prefix();
        self.spacing();
        let cmd = self.read_cmd_name()?;
        if prefix.is_empty() && cmd.is_none() {
            return self.fail_with("Expected a command");
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
                // `ignoreProblemsOf . optionMaybe . try . lookAhead $
                // readCmdWord`. `optionMaybe` makes it total, so
                // `ignoreProblemsOf`'s `p <* put systemState` always runs and
                // puts the whole SystemState back -- the problems this peek
                // reported and the context frames it left behind. Without
                // that, a word that failed after consuming (a `` ` `` with no
                // closing one) leaves its frame on the stack and the real
                // failure names it twice.
                self.peek_ahead(|p| {
                    p.spacing();
                    let w = p.read_normal_word()?;
                    Ok(Self::command_literal_name(&w))
                })
                .flatten()
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
                suffix = self.read_let_suffix()?;
            } else if effective.as_deref() == Some("time") {
                suffix = self.read_time_suffix()?;
            } else {
                suffix = self.read_cmd_suffix(if is_modifier {
                    CmdSuffix::Modifier
                } else if effective.as_deref() == Some("eval") {
                    CmdSuffix::Eval
                } else {
                    CmdSuffix::Plain
                })?;
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
        let result = Token::new(
            id1,
            InnerToken::T_Redirecting {
                redirs,
                cmd: simple,
            },
        );
        // `case () of _ | isCommand ["source", "."] cmd -> readSource result ..`
        match Self::command_literal_name_of(&result).as_deref() {
            Some("source") | Some(".") => return Ok(self.read_source(result)),
            Some("trap") => self.syntax_check_trap(&result),
            _ => {}
        }
        Ok(result)
    }

    /// `readSource`: follow a `source`/`.` command, replacing the command with a
    /// `T_SourceCommand` wrapping both it and the parsed contents of the file.
    ///
    /// Every way of not following ends with the original command and a note:
    /// SC1090 (the name is not constant), SC1093 (already being sourced),
    /// SC1091 (the interface would not read it) or SC1094 (it did not parse).
    fn read_source(&mut self, t: Token) -> Token {
        let (cmd_id, cmd, args) = {
            let InnerToken::T_Redirecting { cmd: simple, .. } = &*t.inner else {
                return t;
            };
            let InnerToken::T_SimpleCommand { words, .. } = &*simple.inner else {
                return t;
            };
            let Some((first, rest)) = words.split_first() else {
                return t;
            };
            (simple.id(), first.clone(), rest.to_vec())
        };
        let file = source_file_arg(&args).cloned();
        let override_file = self.get_source_override();
        // `literalFile`: the directive wins, then a literal name, then a name
        // whose leading expansion can be stripped; a literal `~/` is not a path
        // the parser can resolve, so it counts as non-constant.
        let literal_file = override_file
            .or_else(|| file.as_ref().and_then(ast_lib::get_literal_string))
            .or_else(|| file.as_ref().and_then(strip_dynamic_prefix))
            .filter(|name| !name.starts_with("~/"));
        let file_id = file.as_ref().map_or_else(|| cmd.id(), |f| f.id());

        let Some(filename) = literal_file else {
            let (start, end) = self.span_for(file_id);
            self.note_at(
                start,
                end,
                Severity::WarningC,
                1090,
                "ShellCheck can't follow non-constant source. Use a directive to specify location.",
            );
            return t;
        };

        if !self.should_follow(&filename) {
            // FIXME (upstream): this actually gets squashed without -a.
            let (start, end) = self.span_for(file_id);
            self.note_at(
                start,
                end,
                Severity::InfoC,
                1093,
                "This file appears to be recursively sourced. Ignoring.",
            );
            return t;
        }

        let (input, resolved) = if filename == "/dev/null" {
            // Always allow /dev/null.
            (Ok(String::new()), filename.clone())
        } else {
            let annotations = self.current_annotations();
            let paths: Vec<String> = annotations
                .iter()
                .filter_map(|a| match a {
                    Annotation::SourcePath(p) => Some(p.clone()),
                    _ => None,
                })
                .collect();
            let external = annotations.iter().find_map(|a| match a {
                Annotation::ExternalSources(b) => Some(*b),
                _ => None,
            });
            let root = self.root_filename.clone();
            let sys = std::rc::Rc::clone(&self.sys);
            let resolved = sys.find_source(&root, external, &paths, &filename);
            let contents = sys.read_file(external, &resolved);
            (contents, resolved)
        };

        match input {
            Err(err) => {
                let (start, end) = self.span_for(file_id);
                self.note_at(
                    start,
                    end,
                    Severity::InfoC,
                    1091,
                    &format!("Not following: {err}"),
                );
                t
            }
            Ok(script) => {
                // Both ids copy the span of the original command, and both are
                // allocated before the file is read (`getNewIdFor cmdId`).
                let (start, end) = self.span_for(cmd_id);
                let id1 = self.next_id_between(start.clone(), end.clone());
                let id2 = self.next_id_between(start, end);
                match self.sub_read(&resolved, &script) {
                    Some(src) => {
                        let included = Token::new(id2, InnerToken::T_Include(src));
                        Token::new(
                            id1,
                            InnerToken::T_SourceCommand {
                                includer: t,
                                included,
                            },
                        )
                    }
                    None => {
                        let (start, end) = self.span_for(file_id);
                        self.note_at(
                            start,
                            end,
                            Severity::WarningC,
                            1094,
                            "Parsing of sourced file failed. Ignoring it.",
                        );
                        t
                    }
                }
            }
        }
    }

    /// `subRead`: parse `script` as a whole file of its own, under a
    /// `ContextSource` frame.
    ///
    /// The frame is what makes everything the sourced file reports disappear
    /// without `--check-sourced` (`contextItemDisablesCode`), and what the
    /// recursion guard looks at. `inSeparateContext` throws away the sourced
    /// file's parse *problems* either way -- only its notes, which the frame
    /// filters, can reach the caller.
    fn sub_read(&mut self, name: &str, script: &str) -> Option<Token> {
        let mut sub = Parser::with_shell_flag(
            name,
            script,
            self.shell_flag_specified,
            // The dialect is the one being checked, not one derived from the
            // sourced file's name (`prop_sourcedFileUsesOriginalShellExtension`).
            self.shell_hint,
        );
        sub.next_id = self.next_id;
        sub.next_serial = self.next_serial;
        sub.contexts = self.contexts.clone();
        sub.ann_contexts = self.ann_contexts.clone();
        sub.ann_contexts
            .push(super::AnnContext::Source(name.to_string()));
        sub.sys = std::rc::Rc::clone(&self.sys);
        sub.check_sourced = self.check_sourced;
        sub.root_filename = self.root_filename.clone();
        // `pendingHereDocs = []`: the caller's unread here documents are not the
        // sourced file's business, and are put back afterwards.
        let root = sub.read_script_file();
        let failed = root.is_none() || sub.has_committed_failure();
        if failed {
            // `included <|> failed`: `try` rewinds the parse notes too, and
            // `inSeparateContext` the problems, so nothing of the attempt is
            // kept -- not even the ids, which Parsec's state holds as well.
            return None;
        }
        // `readScriptFile` finishes each file itself: here documents reattached
        // and array indices reparsed, within that file's own state.
        let root = root.map(|r| super::reattach_heredocs(r, &sub.heredoc_bodies));
        let root = root.map(|r| {
            let assoc = super::get_associative_arrays(&r);
            sub.reparse_indices_root(r, &assoc)
        });
        self.next_id = sub.next_id;
        self.next_serial = sub.next_serial;
        for (k, v) in sub.positions {
            self.positions.entry(k).or_insert(v);
        }
        self.notes.extend(sub.notes);
        root
    }

    /// `getSourceOverride`: the innermost `source=` directive in scope within
    /// this file (`takeWhile isSameFile` stops at the enclosing source frame).
    fn get_source_override(&self) -> Option<String> {
        for frame in self.ann_contexts.iter().rev() {
            match frame {
                super::AnnContext::Source(_) => return None,
                super::AnnContext::Annotations(list) => {
                    for a in list {
                        if let Annotation::SourceOverride(s) = a {
                            return Some(s.clone());
                        }
                    }
                }
            }
        }
        None
    }

    /// `getCurrentAnnotations True`: every annotation in scope, innermost
    /// frame first, source frames included -- so a `source-path` in the outer
    /// script still applies while reading a file it sourced.
    fn current_annotations(&self) -> Vec<Annotation> {
        let mut out = Vec::new();
        for frame in self.ann_contexts.iter().rev() {
            if let super::AnnContext::Annotations(list) = frame {
                out.extend(list.iter().cloned());
            }
        }
        out
    }

    /// `shouldFollow`: not if this file is already being read, and not past 100
    /// nested `source` frames.
    fn should_follow(&mut self, file: &str) -> bool {
        let mut sources = 0;
        for frame in &self.ann_contexts {
            if let super::AnnContext::Source(name) = frame {
                if name == file {
                    return false;
                }
                sources += 1;
            }
        }
        if sources >= 100 {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1092,
                "Stopping at 100 'source' frames :O",
            );
            return false;
        }
        true
    }

    /// The literal command name of an assembled `T_Redirecting`, if it has one.
    fn command_literal_name_of(t: &Token) -> Option<String> {
        let InnerToken::T_Redirecting { cmd, .. } = &*t.inner else {
            return None;
        };
        let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner else {
            return None;
        };
        Self::command_literal_name(words.first()?)
    }

    /// `syntaxCheckTrap`: a trap action is shell code, so it is parsed too --
    /// with its failures reported rather than propagated, since the trap itself
    /// parsed fine.
    fn syntax_check_trap(&mut self, t: &Token) {
        let arg = {
            let InnerToken::T_Redirecting { cmd, .. } = &*t.inner else {
                return;
            };
            let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner else {
                return;
            };
            match words.get(1) {
                Some(a) => a.clone(),
                None => return,
            }
        };
        let Some(str) = ast_lib::get_literal_string(&arg) else {
            return;
        };
        // A flag is not a command.
        if str.starts_with('-') {
            return;
        }
        let (start, _) = self.span_for(arg.id());
        self.subparse_commands(&str, start);
    }

    /// `readTimeSuffix`: `time [-p ...] <pipeline>`. Reads optional flag words
    /// (each a `-`-prefixed cmd word), then a full pipeline, appended as the
    /// suffix of the `time` simple command (Parser.hs `readTimeSuffix`). If no
    /// pipeline follows, nothing is consumed and the suffix is empty (mirroring
    /// `option []` over a non-consuming failure).
    pub(super) fn read_time_suffix(&mut self) -> PResult<Vec<Token>> {
        // `readCmdWord` ends with `<* spacing`, so the space after the command
        // name is gone before `readTimeSuffix` begins. The port reads the name
        // without it, so take it here -- and before the mark, or the suffix
        // looks like it consumed when all it did was step over that space.
        self.spacing();
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
                Ok(out)
            }
            Err(()) => {
                // `option []` recovers only from a suffix that consumed
                // nothing: bare `time` is a command, `time -` is a flag with
                // nothing to time.
                if self.idx != m.idx {
                    return Err(());
                }
                self.reset(m);
                Ok(Vec::new())
            }
        }
    }

    pub(super) fn read_cmd_prefix(&mut self) -> Vec<Token> {
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
            match self.read_assignment_word() {
                Ok(a) => {
                    out.push(a);
                    continue;
                }
                Err(()) => {
                    // Only the part up to the `=` is a `try`: past it, a
                    // failure is the parse error (`x=((`).
                    if self.idx != m.idx {
                        self.commit();
                    }
                    self.reset(m);
                    break;
                }
            }
        }
        out
    }

    /// `option Nothing $ Just <$> readCmdName`: `None` when there is no name
    /// to read, an error when reading one failed after consuming input, since
    /// `option` recovers only from a failure that consumed nothing and the
    /// cursor stays where that failure left it.
    pub(super) fn read_cmd_name(&mut self) -> PResult<Option<Token>> {
        // `optional . try $ char '\\' >> lookAhead (variableChars <|> oneOf ":.")`:
        // a leading backslash here suppresses alias expansion, so it is not an
        // escape and reports nothing.
        let bm = self.mark();
        if self.char('\\').is_ok() {
            if !matches!(self.peek(), Some(c) if c == '_'
                || c.is_ascii_alphanumeric()
                || c == ':'
                || c == '.')
            {
                self.reset(bm);
            }
        } else {
            self.reset(bm);
        }
        let m = self.mark();
        // don't treat keywords as command names in command position handled by caller
        match self.read_normal_word() {
            Ok(w) => Ok(Some(w)),
            Err(()) => {
                // `readCmdName` is not behind a `try`, so a word that failed
                // after consuming input ends the parse rather than leaving the
                // command nameless -- and the cursor is not rewound, or the
                // `called "simple command"` around this would take the failure
                // for one that consumed nothing and pop a frame the word left
                // behind (`[-z$('` names the single quoted string).
                if self.idx != m.idx {
                    self.commit();
                    return Err(());
                }
                self.reset(m);
                Ok(None)
            }
        }
    }

    /// `readCmdSuffix = many1 (readIoRedirect <|> readCmdWord)` and its two
    /// variants. `many1` recovers only from a failure that consumed nothing,
    /// so a redirection, assignment or word that failed past its first
    /// character fails the command, and the cursor stays where it failed: a
    /// command that "succeeded" with a shorter suffix would pop a frame the
    /// failure left behind, and name the wrong production.
    pub(super) fn read_cmd_suffix(&mut self, kind: CmdSuffix) -> PResult<Vec<Token>> {
        let mut out = Vec::new();
        loop {
            self.spacing();
            let rm = self.mark();
            match self.read_io_redirect() {
                Ok(r) => {
                    out.push(r);
                    continue;
                }
                Err(()) => {
                    if self.idx != rm.idx {
                        return Err(());
                    }
                }
            }
            // Modifier commands (declare/export/local/readonly/typeset) parse
            // well-formed assignments as T_Assignment (readModifierSuffix).
            if kind == CmdSuffix::Modifier {
                let am = self.mark();
                match self.read_well_formed_assignment() {
                    Ok(a) => {
                        out.push(a);
                        continue;
                    }
                    Err(()) => {
                        // `readWellFormedAssignment` inside `many1`: a failure
                        // that consumed input (`readonly f=(` with no `)`) ends
                        // the whole command, rather than being retried as a word.
                        if self.idx != am.idx {
                            self.commit();
                            return Err(());
                        }
                        self.reset(am);
                    }
                }
            }
            let m = self.mark();
            match self.read_normal_word() {
                Ok(w) => out.push(w),
                Err(()) => {
                    // `many` stops on a failure that consumed nothing; one that
                    // consumed ends the parse, as a trailing `\` does.
                    if self.idx != m.idx {
                        self.commit();
                        return Err(());
                    }
                    self.reset(m);
                    // `evalFallback`: `lookAhead (char '(')`, a warning, and a
                    // `fail` that consumed nothing, so the suffix simply ends
                    // here and the `(` is reported by whatever reads it next.
                    if kind == CmdSuffix::Eval && self.peek() == Some('(') {
                        let pos = self.pos();
                        self.problem_at(
                            pos.clone(),
                            pos,
                            Severity::WarningC,
                            1098,
                            "Quote/escape special characters when using eval, e.g. eval \"a=(b)\".",
                        );
                        // The message ends in a period, and `getStringFromParsec`
                        // adds another: that is what upstream prints.
                        let _: PResult<()> = self.fail_recoverable(
                            "Unexpected parentheses. Make sure to quote when eval'ing as shell parsers differ.",
                        );
                    }
                    break;
                }
            }
        }
        Ok(out)
    }

    /// `reparseIndices`: reparse each `T_UnparsedIndex` as arithmetic (indexed
    /// arrays) or an index word (associative arrays), matching ShellCheck.
    pub(super) fn reparse_indices_root(
        &mut self,
        mut root: Token,
        assoc: &std::collections::HashSet<String>,
    ) -> Token {
        self.reparse_walk(&mut root, assoc);
        root
    }

    pub(super) fn reparse_walk(
        &mut self,
        t: &mut Token,
        assoc: &std::collections::HashSet<String>,
    ) {
        let name = match &*t.inner {
            InnerToken::T_Assignment { var, .. } => Some(var.clone()),
            InnerToken::TA_Variable { name, .. } => Some(name.clone()),
            _ => None,
        };
        if let Some(name) = name {
            let is_assoc = assoc.contains(&name);
            let indices: Option<&mut Vec<Token>> = match t.inner_mut() {
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
                        self.sub_parse_array_index(&pos, &src)
                    };
                    if let Some(nt) = newtok {
                        // Re-fetch the indices vec (borrow released after sub_parse).
                        if let Some(slot) = match t.inner_mut() {
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
            if let InnerToken::T_Assignment { value, .. } = t.inner_mut() {
                if let InnerToken::T_Array(elems) = value.inner_mut() {
                    for elem in elems.iter_mut() {
                        self.reparse_indexed_element(elem, is_assoc);
                    }
                }
            }
        }
        for c in t.inner_mut().children_mut() {
            self.reparse_walk(c, assoc);
        }
    }

    pub(super) fn reparse_indexed_element(&mut self, elem: &mut Token, is_assoc: bool) {
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
                    self.sub_parse_array_index(&pos, &src)
                };
                if let Some(nt) = newtok {
                    if let InnerToken::T_IndexedElement { indices, .. } = elem.inner_mut() {
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
    /// `subParse newPos (readArithmeticContents <* eof) unQuoted`, the
    /// expression of a `let` argument.
    pub(super) fn sub_parse_let_expression(&mut self, pos: &Position, src: &str) -> Option<Token> {
        // `subParse` runs on the same parser state, so whatever the
        // arithmetic reports stays reported: `let $(source x)` sources a file
        // from inside its expression, and that is where SC1090 comes from.
        let mut sub = self.sub_parser(src, pos);
        // `readSequence` skips its own leading arithmetic spacing.
        let tok = sub.read_arithmetic_contents().ok();
        // `readArithmeticContents <* eof`, with no spacing in between: a comment
        // left over from `readCmdWord`'s `spacing` makes this fail, and the
        // argument is read as an ordinary word instead.
        let tok = tok.filter(|_| sub.eof());
        if tok.is_none() {
            // `try readLetExpression`: Parsec's own state goes back, and the
            // notes with it; the problems live outside it and stay.
            self.problems.extend(sub.problems);
            return None;
        }
        self.merge_sub(sub);
        tok
    }

    /// `subParse pos (called "arithmetic array index expression" $ optional
    /// space >> readArithmeticContents) src`, the index of an indexed array
    /// when `reparseIndices` gets to it. No `eof`: whatever the expression
    /// leaves unread is simply left, so `a[$(echo $))]=` has the command
    /// substitution its first `)` closes, and the checks see it.
    pub(super) fn sub_parse_array_index(&mut self, pos: &Position, src: &str) -> Option<Token> {
        let mut sub = self.sub_parser(src, pos);
        let _ = sub.one_of(" \t\n\r");
        let tok = sub.read_arithmetic_contents().ok()?;
        self.merge_sub(sub);
        Some(tok)
    }

    /// Sub-parse `src` (at `pos`) as an associative-array index word.
    pub(super) fn sub_parse_index_word(&mut self, pos: &Position, src: &str) -> Option<Token> {
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

    /// `readStringForParser readCmdWord`: the raw text of one `let` argument,
    /// trailing spacing included, and the position it starts at.
    pub(super) fn read_let_arg_raw(&mut self) -> Option<(String, Position)> {
        let start = self.pos();
        let raw = self
            .read_string_for_parser(|p| {
                p.read_normal_word()?;
                p.spacing();
                Ok(())
            })
            .ok()?;
        if raw.is_empty() {
            return None;
        }
        Some((raw, start))
    }

    /// `readLetSuffix = many1 (readIoRedirect <|> try readLetExpression <|>
    /// readCmdWord)`: `let` arguments as arithmetic expressions. Only the
    /// expression sits behind a `try`, so a redirection or a word that failed
    /// after consuming input fails the suffix, and with it the command:
    /// `let "` is an unterminated string, not a `let` with no arguments.
    pub(super) fn read_let_suffix(&mut self) -> PResult<Vec<Token>> {
        let mut out = Vec::new();
        loop {
            self.spacing();
            let rm = self.mark();
            match self.read_io_redirect() {
                Ok(r) => {
                    out.push(r);
                    continue;
                }
                Err(()) => {
                    if self.idx != rm.idx {
                        return Err(());
                    }
                }
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
                if let Some(tok) = self.sub_parse_let_expression(&adj_pos, &unquoted) {
                    out.push(tok);
                    continue;
                }
            }
            // `try readLetExpression` rewinds; `readCmdWord` reads the word
            // for what it is, and a failure that consumed is the command's.
            self.reset(m);
            match self.read_normal_word() {
                Ok(w) => out.push(w),
                Err(()) => {
                    if self.idx != m.idx {
                        self.commit();
                        return Err(());
                    }
                    break;
                }
            }
        }
        Ok(out)
    }

    /// `validateCommand` (Parser.hs): emit SC1127 when a command word is really
    /// a C-style comment — either the word `//`, or a word starting `/*`.
    pub(super) fn validate_command_comment(&mut self, cmd: &Token) {
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
            } else if let Some(InnerToken::T_Literal(str)) = parts.first().map(|p| &*p.inner) {
                // `takeWhile isAlpha`, lowercased: `elseif[$i==2]` counts.
                let word: String = str
                    .chars()
                    .take_while(|c| c.is_alphabetic())
                    .flat_map(char::to_lowercase)
                    .collect();
                if word == "elsif" || word == "elseif" {
                    let (s, e) = self.span_for(cmd.id());
                    self.problem_at(
                        s,
                        e,
                        Severity::ErrorC,
                        1131,
                        "Use 'elif' to start another branch.",
                    );
                }
            }
        }
    }

    /// The single-literal command name of a T_NormalWord, if any.
    pub(super) fn command_literal_name(t: &Token) -> Option<String> {
        if let InnerToken::T_NormalWord(parts) = &*t.inner {
            if parts.len() == 1 {
                if let InnerToken::T_Literal(s) = &*parts[0].inner {
                    return Some(s.clone());
                }
            }
        }
        None
    }

    /// `readArrayIndex`: `[`, then the index taken verbatim, then `]`. The end
    /// is found by parsing the contents as an index span
    /// (`readStringForParser readIndexSpan`), so an unterminated quote inside
    /// fails the index instead of being swallowed as raw text; the characters
    /// themselves are kept unparsed for `reparseIndices` to revisit.
    pub(super) fn read_array_index(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('[')?;
        let pos = self.pos();
        // `str <- readStringForParser readIndexSpan`.
        let raw = self.read_string_for_parser(|p| p.read_index_span())?;
        self.char(']')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_UnparsedIndex { pos, str: raw },
        ))
    }

    /// `readIndexSpan`: `many (readNormalWordPart "]" <|> someSpace <|>
    /// otherLiteral)`. Only consumes; the caller keeps the raw text.
    fn read_index_span(&mut self) -> PResult<()> {
        loop {
            // `notFollowedBy2 (oneOf "]")`
            if matches!(self.peek(), None | Some(']')) {
                return Ok(());
            }
            let before = self.idx;
            let m = self.mark();
            match self.read_normal_word_part_end("]") {
                Ok(_) if self.idx != before => continue,
                Ok(_) => self.reset(m),
                Err(()) => {
                    if self.idx != before {
                        return Err(());
                    }
                    self.reset(m);
                }
            }
            if self.spacing1().is_ok() {
                continue;
            }
            // `otherLiteral`: a run of the characters a word part cannot take.
            let mut any = false;
            while matches!(self.peek(), Some(c) if QUOTABLE_CHARS.contains(c)) {
                self.bump();
                any = true;
            }
            if !any {
                return Ok(());
            }
        }
    }

    /// `readAssignmentWord = readAssignmentWordExt True`: lenient, so a
    /// leading `$` is read and reported (SC1066) before the word is rejected.
    pub(super) fn read_assignment_word(&mut self) -> PResult<Token> {
        self.called("variable assignment", |p| p.read_assignment_word_body(true))
    }

    /// `readWellFormedAssignment = readAssignmentWordExt False`, what a
    /// modifier command's arguments are read with.
    pub(super) fn read_well_formed_assignment(&mut self) -> PResult<Token> {
        self.called("variable assignment", |p| {
            p.read_assignment_word_body(false)
        })
    }

    fn read_assignment_word_body(&mut self, lenient: bool) -> PResult<Token> {
        let start = self.pos();
        // Everything up to and including the `=` is read inside a `try`: a word
        // that turns out not to be an assignment must leave the cursor where it
        // started, so the enclosing `called` unwinds and leaves no context
        // behind either.
        let prefix = self.mark();
        // `leadingDollarPos <- optionMaybe $ getSpanPositionsFor (char '$')`:
        // read so that `$foo=(bar)` can be warned about at parse time, since
        // it would otherwise fail to parse and never reach the checks.
        let leading_dollar = if lenient && self.peek() == Some('$') {
            let l = self.pos();
            self.bump();
            Some((l, self.pos()))
        } else {
            None
        };
        // name
        let Ok(name) = self.read_variable_name() else {
            self.reset(prefix);
            return Err(());
        };
        // `many readArrayIndex`
        let mut indices = Vec::new();
        while self.peek() == Some('[') {
            match self.read_array_index() {
                Ok(i) => indices.push(i),
                Err(()) => {
                    self.reset(prefix);
                    return Err(());
                }
            }
        }
        // The T_Assignment span ends here (variable name + indices), before the
        // `=` — matching ShellCheck's `id <- endSpan start` placement, so that
        // SC2034 etc. point at the variable name rather than the whole word.
        // `hasLeftSpace <- fmap (not . null) spacing`: space before the `=`
        // is read, and then makes this not an assignment after all.
        let before_left = self.idx;
        self.spacing();
        let has_left_space = self.idx != before_left;
        let op_start = self.pos();
        // += or =
        let mode = if self.string("+=").is_ok() {
            AssignmentMode::Append
        } else if self.char('=').is_ok() {
            AssignmentMode::Assign
        } else {
            self.reset(prefix);
            return Err(());
        };
        if leading_dollar.is_some() || has_left_space {
            // `when (isJust leadingDollarPos || hasLeftSpace)`: not an
            // assignment after all, and with a `$` and a `(` ahead one that
            // would otherwise fail to parse, so it is warned about here. The
            // `fail ""` sits inside the `try`.
            let m = self.mark();
            self.spacing();
            let paren = self.peek() == Some('(');
            self.reset(m);
            if let (true, Some((l, r))) = (paren, leading_dollar) {
                self.problem_at(
                    l,
                    r,
                    Severity::ErrorC,
                    1066,
                    "Don't use $ on the left side of assignments.",
                );
            }
            let _: PResult<()> = self.fail_recoverable("");
            self.reset(prefix);
            return Err(());
        }
        // Space after the `=`, or nothing left of the command, means the value
        // is the empty string — and if it was space, that is rarely intended.
        let right_start = self.pos();
        let before_space = self.idx;
        self.spacing();
        let has_right_space = self.idx != before_space;
        let right_end = self.pos();
        let at_end_of_command = matches!(
            self.peek(),
            None | Some('\r' | '\n' | ';' | '&' | '|' | ')')
        );
        if has_right_space || at_end_of_command {
            if name != "IFS" && has_right_space && !at_end_of_command {
                self.problem_at(
                    right_start,
                    right_end,
                    Severity::WarningC,
                    1007,
                    "Remove space after = if trying to assign a value (for empty string, use var='' ... ).",
                );
            }
            let value = self.empty_literal_word();
            let id = self.next_id_between(start, op_start);
            return Ok(Token::new(
                id,
                InnerToken::T_Assignment {
                    mode,
                    var: name,
                    indices,
                    value,
                },
            ));
        }
        // value: array (..) or word (possibly empty)
        let value = if self.peek() == Some('(') {
            self.read_array()?
        } else {
            // `value <- readArray <|> readNormalWord`, with nothing after it:
            // there is no falling back to an empty value here, and the frame
            // `called "variable assignment"` left behind is what names the
            // failure. An assignment that really has no value took the
            // `readEmptyLiteral` branch above.
            self.read_normal_word()?
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

    pub(super) fn empty_literal_word(&mut self) -> Token {
        let p = self.pos();
        let lit_id = self.next_id_between(p.clone(), p.clone());
        let lit = Token::new(lit_id, InnerToken::T_Literal(String::new()));
        let wid = self.next_id_between(p.clone(), p);
        Token::new(wid, InnerToken::T_NormalWord(vec![lit]))
    }

    pub(super) fn read_array(&mut self) -> PResult<Token> {
        self.called("array assignment", |p| p.read_array_body())
    }

    fn read_array_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        let opening = self.pos();
        self.char('(')?;
        if self.peek() == Some('(') {
            self.problem_at(
                opening.clone(),
                opening,
                Severity::ErrorC,
                1116,
                "Missing $ on a $((..)) expression? (or use ( ( for arrays).",
            );
        }
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
                    match self.read_array_index() {
                        Ok(i) => indices.push(i),
                        Err(()) => break,
                    }
                }
                if !indices.is_empty() && self.char('=').is_ok() {
                    // `value <- readRegular <|> nothing`, and readRegular is
                    // itself `readArray <|> readNormalWord`.
                    let value = if self.peek() == Some('(') {
                        // `readArray <|> readNormalWord`, and past the `(`
                        // neither that `<|>` nor the `<|> nothing` after it can
                        // recover.
                        self.read_array()?
                    } else {
                        let before = self.idx;
                        match self.read_normal_word() {
                            Ok(w) => w,
                            // `<|> nothing` is still an `<|>`: a value that
                            // failed after consuming -- `[]=` and a backtick
                            // that never closes -- is the element's failure
                            // and the array's, and it is that failure the
                            // parse reports rather than the missing `)`.
                            Err(()) if self.idx != before => return Err(()),
                            Err(()) => self.empty_literal_word(),
                        }
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
            // `readRegular = readArray <|> readNormalWord`: an element may
            // itself be an array, as in `a=(1 [2]=(3 4))`.
            if self.peek() == Some('(') {
                elems.push(self.read_array()?);
                continue;
            }
            // `reluctantlyTill`'s trailing `<|> return []` ends the list on a
            // failed element, but `<|>` cannot take over from a failure that
            // consumed input: that one propagates out of `readArray` and ends
            // the parse, so the error reported is the element's own rather
            // than the missing `)` below.
            let before = self.idx;
            match self.read_normal_word() {
                Ok(w) => elems.push(w),
                Err(()) if self.idx == before => break,
                Err(()) => return Err(()),
            }
        }
        if self.char(')').is_err() {
            return self.fail_with("Expected ) to close array assignment");
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Array(elems)))
    }

    // ---- redirections ------------------------------------------------------

    pub(super) fn read_redirect_list(&mut self) -> Vec<Token> {
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

    pub(super) fn read_io_redirect(&mut self) -> PResult<Token> {
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
        if fd.is_empty() && self.peek() == Some('&') {
            if matches!(self.peek_at(1), Some('<') | Some('>')) {
                self.bump(); // &
                fd = "&".to_string();
            } else {
                // `string "&"` consumes before the `lookAhead` turns the source
                // down, and in Parsec an error outlives the `try` that rewinds
                // the input -- so a `&` that starts no redirection still leaves
                // a failure recorded from past itself, which is the position a
                // doomed parse then reports.
                let m = self.mark();
                self.bump();
                self.fail_implicitly();
                self.reset(m);
            }
        }
        // `op_start` is the position after the fd source, where the redirection
        // operator begins. Parser.hs captures `startSpan` for the inner redir
        // token (T_IoFile/T_IoDuplicate/T_HereString/T_HereDoc) here, *after*
        // `readIoSource` has consumed the fd, so a glued `1>2` anchors T_IoFile
        // (and thus SC2210) at the `>`, not the fd digit.
        let op_start = self.pos();
        // heredoc
        if self.peek() == Some('<') && self.peek_at(1) == Some('<') {
            let r = self.read_heredoc_or_herestring(start, op_start, fd);
            if r.is_err() {
                // The `<<` is consumed, so this is a here document whatever
                // follows: `read -ra a<<)` is a parse error, not a word.
                self.commit();
            }
            return r;
        }
        // dup: <& or >&
        // `readIoDuplicate` is a `try`, and its target is `digitsAndOrDash`:
        // digits with an optional dash, or a bare dash. With neither, this is
        // not a duplicate but a `>& file` / `<& file` redirect, which
        // `readIoFile` takes with `>&`/`<&` as the operator.
        if (self.peek() == Some('<') || self.peek() == Some('>'))
            && self.peek_at(1) == Some('&')
            && matches!(self.peek_at(2), Some(c) if c.is_ascii_digit() || c == '-')
        {
            let opc = self.bump().unwrap();
            self.bump(); // &
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
            let dup_id = self.next_id_between(op_start.clone(), self.pos());
            let dup = Token::new(dup_id, InnerToken::T_IoDuplicate { op: op_tok, num });
            let id = self.next_id_between(start, self.pos());
            return Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: dup }));
        }
        // `readIoFile = called "redirection"`, so a redirection operator left
        // without a filename is reported as one — and, having consumed the
        // operator, it is not something the caller can back out of.
        let (os, fdc, st) = (op_start.clone(), fd.clone(), start.clone());
        let om = self.mark();
        let r = self.called("redirection", move |p| {
            let op_tok = p.read_io_file_op(os.clone()).ok_or(())?;
            p.spacing();
            let file = p.read_normal_word()?;
            let iofile_id = p.next_id_between(os.clone(), p.pos());
            let iofile = Token::new(iofile_id, InnerToken::T_IoFile { op: op_tok, file });
            let id = p.next_id_between(st, p.pos());
            Ok(Token::new(
                id,
                InnerToken::T_FdRedirect {
                    fd: fdc,
                    target: iofile,
                },
            ))
        });
        if r.is_err() {
            if self.idx == om.idx {
                // `readIoSource` is a `try`, so the fd source rolls back when
                // no redirection operator follows it.
                self.reset(m);
            } else {
                // The operator was consumed, so neither the `<|>` in
                // `readIoRedirect` nor the `many`/`many1` around it can
                // recover: the parse is over.
                self.commit();
            }
        }
        r
    }

    pub(super) fn read_io_file_op(&mut self, start: Position) -> Option<Token> {
        let (inner, len): (InnerToken, usize) = match (self.peek(), self.peek_at(1)) {
            (Some('>'), Some('>')) => (InnerToken::T_DGREAT, 2),
            (Some('<'), Some('>')) => (InnerToken::T_LESSGREAT, 2),
            (Some('>'), Some('&')) => (InnerToken::T_GREATAND, 2),
            (Some('<'), Some('&')) => (InnerToken::T_LESSAND, 2),
            (Some('>'), Some('|')) => (InnerToken::T_CLOBBER, 2),
            // `redirToken` ends with `notFollowedBy2 (char '(')`, so `<(`/`>(`
            // stay whole for `readProcSub` to take as a word.
            (Some('<'), Some('(')) | (Some('>'), Some('(')) => return None,
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

    pub(super) fn read_heredoc_or_herestring(
        &mut self,
        start: Position,
        op_start: Position,
        fd: String,
    ) -> PResult<Token> {
        if !self.string_peek("<<") {
            return Err(());
        }
        if self.string_peek("<<<") {
            return self.called("here string", |p| p.read_here_string(start, op_start, fd));
        }
        self.called("here document", |p| p.read_here_doc(start, op_start, fd))
    }

    fn read_here_string(
        &mut self,
        start: Position,
        op_start: Position,
        fd: String,
    ) -> PResult<Token> {
        self.string("<<<")?;
        // here string: `readHereString` spans just `<<<` (id captured before
        // the word is read).
        let hs_id = self.next_id_between(op_start, self.pos());
        self.spacing();
        let word = self.read_normal_word()?;
        let hs = Token::new(hs_id, InnerToken::T_HereString(word));
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_FdRedirect { fd, target: hs }))
    }

    fn read_here_doc(
        &mut self,
        start: Position,
        _op_start: Position,
        fd: String,
    ) -> PResult<Token> {
        self.string("<<")?;
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
            contexts: self.contexts.clone(),
            ann_contexts: self.ann_contexts.clone(),
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

    /// `readToken`: the end token is the raw text of whatever `readNormalWord`
    /// accepts, with its diagnostics forgotten, plus a trailing CR if there is
    /// one -- a here document really does work with CRLF, because the CR ends
    /// up part of the token.
    pub(super) fn read_heredoc_delim(&mut self) -> PResult<(String, Quoted)> {
        let mut str = self.read_string_for_parser(|p| p.read_normal_word().map(|_| ()))?;
        if self.carriage_return().is_ok() {
            str.push('\r');
        }
        Ok(unquote_here_delim(&str))
    }

    pub(super) fn read_pending_heredocs(&mut self) -> PResult<()> {
        // Past a commitment the parse is over in Parsec: a `<<` read after
        // the failure that ended it (`e<;<<x`) has no body to look for, and
        // reports nothing.
        if self.pending_heredocs.is_empty() || self.committed {
            return Ok(());
        }
        let pending: Vec<PendingHereDoc> = std::mem::take(&mut self.pending_heredocs);
        for hd in pending {
            // `swapContext`: the body is read long after the redirection was
            // parsed, so the diagnostics name the `<<` and what contained it.
            let outer = std::mem::replace(&mut self.contexts, hd.contexts.clone());
            let outer_disabled = std::mem::replace(&mut self.ann_contexts, hd.ann_contexts.clone());
            let from = self.idx;
            let r = self.read_pending_here_doc(&hd);
            // `parsecBracket` restores the outer stack unless the body both
            // failed and consumed: an unterminated document with no lines at
            // all leaves nothing behind to name.
            if r.is_ok() || self.idx == from {
                self.contexts = outer.clone();
                self.ann_contexts = outer_disabled;
                // The restore happens before the failure reaches the top, so
                // the report names the restored stack.
                if self.frozen_contexts.as_ref() == Some(&hd.contexts) {
                    self.frozen_contexts = Some(outer);
                }
            }
            r?;
        }
        Ok(())
    }

    fn read_pending_here_doc(&mut self, hd: &PendingHereDoc) -> PResult<()> {
        {
            // `docStartPos`: the position of the first byte of the body (this is
            // invoked right after the `<<EOF` line's newline).
            let doc_start = self.pos();
            let (terminated, was_warned, lines) = self.read_doc_lines(hd);
            let doc_end = self.pos();
            let body: String = lines.iter().map(|l| format!("{l}\n")).collect();
            if !terminated {
                if !was_warned {
                    self.debug_here_doc(hd, &body);
                }
                // Reached from `linefeed`, deep inside `spacing`: in Parsec the
                // consuming failure propagates straight out of `readScript`,
                // with nothing above it able to recover.
                // Record the failure before committing: the commitment is what
                // makes it the last word, so it must not suppress its own
                // message.
                let r: PResult<()> = self.fail_with("Here document was not correctly terminated");
                self.commit();
                return r;
            }
            // `parseHereData`: a quoted delimiter keeps the body verbatim as one
            // literal; an unquoted delimiter sub-parses the body for expansions
            // (`$(..)`, `` `..` ``, `${..}`, `$var`) exactly like a double-quoted
            // string, so stdin-consumer detection sees them.
            let tokens = match hd.quoted {
                Quoted::Quoted => {
                    let lit_id = self.next_id_between(doc_start, doc_end);
                    vec![Token::new(lit_id, InnerToken::T_Literal(body))]
                }
                Quoted::Unquoted => self.read_here_data(&body, doc_start)?,
            };
            self.heredoc_bodies.insert(hd.id, tokens);
        }
        Ok(())
    }

    /// `readDocLines`: the body lines up to the end token, with whether it was
    /// found and whether a near-miss was already explained.
    fn read_doc_lines(&mut self, hd: &PendingHereDoc) -> (bool, bool, Vec<String>) {
        let mut lines = Vec::new();
        let mut warned = false;
        loop {
            let line_pos = self.pos();
            let mut line = String::new();
            while let Some(c) = self.peek() {
                if c == '\n' {
                    break;
                }
                self.bump();
                line.push(c);
            }
            let at_eof = self.char('\n').is_err();
            let (is_end, was_warned) = self.check_here_doc_end(hd, &line, &line_pos);
            warned = warned || was_warned;
            if is_end {
                return (true, warned, lines);
            }
            lines.push(line);
            if at_eof {
                return (false, warned, lines);
            }
        }
    }

    /// `checkEnd`: is this line the end token, and if it only looks like it,
    /// say why it isn't.
    fn check_here_doc_end(
        &mut self,
        hd: &PendingHereDoc,
        line: &str,
        line_pos: &Position,
    ) -> (bool, bool) {
        // `linewhitespace \`reluctantlyTill\` string endToken`: blanks, then the
        // token. Reluctant, so the blanks stop at the first position where the
        // token matches — an end token that itself starts with a space still
        // lines up. Anything else in front and this is an ordinary body line.
        let mut split = None;
        for (i, c) in line
            .char_indices()
            .chain(std::iter::once((line.len(), '\0')))
        {
            if line[i..].starts_with(hd.delim.as_str()) {
                split = Some(i);
                break;
            }
            if c != ' ' && c != '\t' {
                break;
            }
        }
        let Some(split) = split else {
            return (false, false);
        };
        let leading = line[..split].to_string();
        let after = &line[split + hd.delim.len()..];
        let trailing: String = after
            .chars()
            .take_while(|c| *c == ' ' || *c == '\t')
            .collect();
        let trailer = &after[trailing.len()..];

        let leading_spaces_are_tabs = leading.chars().all(|c| c == '\t');
        let leader_is_ok =
            leading.is_empty() || (hd.dashed == Dashed::Dashed && leading_spaces_are_tabs);
        if leader_is_ok && trailing.is_empty() && trailer.is_empty() {
            return (true, false);
        }

        let col = |offset: usize| Position {
            file: line_pos.file.clone(),
            line: line_pos.line,
            column: line_pos.column + offset as i64,
        };
        let trailing_pos = col(leading.len() + hd.delim.chars().count());
        let trailer_pos = col(leading.len() + hd.delim.chars().count() + trailing.len());
        let mut ppt = |pos: Position, code: i64, msg: &str| {
            // `ppt` is `parseProblemAt`, which checks `shouldIgnoreCode`: a
            // `disable=` in front of the command covers this.
            if self.code_is_disabled(code) {
                return;
            }
            self.problems.push(ParseNote {
                start: pos.clone(),
                end: pos,
                severity: Severity::ErrorC,
                code,
                message: msg.to_string(),
            });
        };
        match trailer.chars().next() {
            Some(')') => {
                ppt(
                    trailer_pos,
                    1119,
                    "Add a linefeed between end token and terminating ')'.",
                );
                (false, true)
            }
            Some('#') => {
                ppt(
                    trailer_pos,
                    1120,
                    "No comments allowed after here-doc token. Comment the next line instead.",
                );
                (false, true)
            }
            Some(c) if ";>|&".contains(c) => {
                ppt(
                    trailer_pos,
                    1121,
                    "Add ;/& terminators (and other syntax) on the line with the <<, not here.",
                );
                (false, true)
            }
            Some(_) if !trailing.is_empty() => {
                ppt(
                    trailer_pos,
                    1122,
                    "Nothing allowed after end token. To continue a command, put it on the line with the <<.",
                );
                (false, true)
            }
            // The end token is only a prefix of this line's first word.
            Some(_) => (false, false),
            None if !trailing.is_empty() && leader_is_ok => {
                ppt(
                    trailing_pos,
                    1118,
                    "Delete whitespace after the here-doc end token.",
                );
                // Taken as the end anyway, as ShellCheck does.
                (true, true)
            }
            None if hd.dashed == Dashed::Undashed && !leading.is_empty() => {
                ppt(
                    col(0),
                    1039,
                    "Remove indentation before end token (or use <<- and indent with tabs).",
                );
                (false, true)
            }
            None if hd.dashed == Dashed::Dashed && !leading_spaces_are_tabs => {
                ppt(
                    col(0),
                    1040,
                    "When using <<-, you can only indent with tabs.",
                );
                (false, true)
            }
            None => (false, false),
        }
    }

    /// `debugHereDoc`: the end token was never found, so guess at why.
    fn debug_here_doc(&mut self, hd: &PendingHereDoc, doc: &str) {
        let (start, end) = self.span_for(hd.id);
        // `parseProblemAtId`, so a `disable=` in scope at the `<<` -- the
        // scope this body is read in -- silences these like any problem.
        let mut at_token = |code: i64, msg: String| {
            self.problem_at(start.clone(), end.clone(), Severity::ErrorC, code, &msg);
        };
        // The containment tests use the raw text; only the messages are escaped.
        let token = &hd.delim;
        let tok = ast_lib::e4m(token);
        if doc.contains(token.as_str()) {
            at_token(
                1041,
                format!("Found '{tok}' further down, but not on a separate line."),
            );
            // Haskell's `lines` keeps a trailing CR; Rust's `str::lines` strips
            // it, and the CR is exactly what makes a close match not a match.
            for line in haskell_lines(doc) {
                if line.contains(token.as_str()) {
                    at_token(
                        1042,
                        format!(
                            "Close matches include '{}' (!= '{tok}').",
                            ast_lib::e4m(line)
                        ),
                    );
                }
            }
        } else if doc.to_lowercase().contains(&token.to_lowercase()) {
            at_token(
                1043,
                format!("Found {tok} further down, but with wrong casing."),
            );
        } else {
            at_token(
                1044,
                format!("Couldn't find end token `{tok}' in the here document."),
            );
        }
    }

    /// `readHereData` (Parser.hs): sub-parse an unquoted here-doc body into the
    /// same token stream a double-quoted string produces (literals, dollar
    /// expansions, backtick command substitutions), with `"` and other
    /// non-`` `$\ `` characters kept literal via `readHereLiteral`.
    pub(super) fn read_here_data(&mut self, body: &str, start: Position) -> PResult<Vec<Token>> {
        let mut sub = self.sub_parser(body, &start);
        let r = sub.read_here_data_parts();
        // The stack the sub-parse reports from: the one it froze when it
        // committed, or the live one if nothing did.
        let contexts = sub
            .frozen_contexts
            .clone()
            .unwrap_or_else(|| sub.contexts.clone());
        let failure = sub.failure.clone();
        self.merge_sub(sub);
        match r {
            Ok(parts) => Ok(parts),
            Err(()) => {
                // A plain `subParse`, not `tryWithErrors`: the failure comes
                // straight back out, and the contexts it was left in -- the
                // here document's own among them -- are what gets reported.
                self.contexts = contexts.clone();
                self.failure = failure;
                self.commit();
                self.frozen_contexts = Some(contexts);
                Err(())
            }
        }
    }

    /// `many $ doubleQuotedPart <|> readHereLiteral`, on the body's own input.
    fn read_here_data_parts(&mut self) -> PResult<Vec<Token>> {
        let mut parts = Vec::new();
        loop {
            let before = self.idx;
            match self.read_here_data_part() {
                Ok(t) => parts.push(t),
                Err(()) => {
                    // `many`: an alternative that consumed before failing takes
                    // the here document down with it.
                    if self.idx != before {
                        return Err(());
                    }
                    return Ok(parts);
                }
            }
        }
    }

    /// `doubleQuotedPart <|> readHereLiteral`: outside a double quote, a `"` and
    /// the ordinary text around it are literal too.
    fn read_here_data_part(&mut self) -> PResult<Token> {
        let m = self.mark();
        match self.read_double_quoted_part() {
            Ok(t) => return Ok(t),
            Err(()) => {
                if self.idx != m.idx {
                    return Err(());
                }
            }
        }
        self.read_here_literal()
    }

    /// `readHereLiteral`: a run of characters that are not `` ` ``, `$` or `\`.
    pub(super) fn read_here_literal(&mut self) -> PResult<Token> {
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
    /// `verifyEof`: input the grammar could not consume is *reported*, not
    /// fatal — ShellCheck keeps the tree it managed to build and still
    /// analyses it, which is why `r=\$(` yields SC1036/SC1088 alongside its
    /// ordinary warnings instead of a parse failure.
    pub(super) fn verify_eof(&mut self) {
        let p = self.pos();
        let (code, message) = if self.peek() == Some('(') {
            (1088, "Parsing stopped here. Invalid use of parentheses?")
        } else if self.at_keyword() {
            (
                1089,
                "Parsing stopped here. Is this keyword correctly matched up?",
            )
        } else {
            (
                1070,
                "Parsing stopped here. Mismatched keywords or invalid parentheses?",
            )
        };
        self.problem_at(p.clone(), p, Severity::ErrorC, code, message);
    }

    /// `readKeyword`: the tokens that close a compound command.
    fn at_keyword(&mut self) -> bool {
        const WORDS: [&str; 7] = ["then", "else", "elif", "fi", "do", "done", "esac"];
        WORDS.iter().any(|k| self.keyword_ahead(k))
            || matches!(self.peek(), Some('}') | Some(')'))
            || (self.peek() == Some(';') && self.peek_at(1) == Some(';'))
    }

    pub(super) fn is_valid_shell(s: &str) -> Option<bool> {
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

    pub(super) fn read_script_file(&mut self) -> Option<Token> {
        let start = self.pos();
        // UTF-8 BOM
        let _ = self.string("\u{FEFF}");
        let shebang = self.read_shebang().unwrap_or_else(|| self.empty_literal());
        self.allspacing();
        // File-wide shellcheck directives after the shebang.
        let file_annotations = self.read_annotations();
        self.allspacing();
        // `withAnnotations fileAnnotations` wraps the whole file, so these
        // never go out of scope again.
        self.push_disables(&file_annotations);

        // `verifyShebang` (Parser.hs readScriptFile): warn on an unrecognized
        // interpreter, unless a `# shellcheck shell=...` directive overrides the
        // shebang. Emitted at the start of the file, like `parseProblemAt pos`.
        let ignore_shebang = self.shell_flag_specified
            || file_annotations
                .iter()
                .any(|a| matches!(a, Annotation::ShellOverride(_)));

        // Settle the dialect before the body is read, in the order the analyzer
        // resolves it: what the caller said (already in `shell_hint`), then a
        // file-wide `shell=` directive, then the shebang. Only one parse
        // decision consults it -- see `empty_negation_ok`.
        if self.shell_hint.is_none() {
            self.shell_hint = file_annotations.iter().find_map(|a| match a {
                Annotation::ShellOverride(s) => crate::data::shell_for_executable(s),
                _ => None,
            });
        }
        if self.shell_hint.is_none() {
            if let InnerToken::T_Literal(sb) = &*shebang.inner {
                self.shell_hint =
                    crate::data::shell_for_executable(&ast_lib::executable_from_shebang(sb));
            }
        }
        let mut unsupported_shell = false;
        if !ignore_shebang {
            if let InnerToken::T_Literal(sb) = &*shebang.inner {
                let exe = ast_lib::executable_from_shebang(sb);
                match Self::is_valid_shell(&exe) {
                    Some(true) => {}
                    Some(false) => {
                        self.problem_at(
                            start.clone(),
                            start.clone(),
                            Severity::ErrorC,
                            1071,
                            "ShellCheck only supports sh/bash/dash/ksh/'busybox sh' scripts. Sorry!",
                        );
                        unsupported_shell = true;
                    }
                    None => {
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
        }

        // A shebang for a shell ShellCheck does not implement: the body is not
        // parsed at all (`many anyChar`), leaving a script whose only content
        // is the shebang, so the checks that look at the shebang still run and
        // nothing else does. Mirrors `readScriptFile`'s else branch, including
        // its dropping of the annotations.
        if unsupported_shell {
            while self.bump().is_some() {}
            let id = self.next_id_between(start.clone(), self.pos());
            return Some(Token::new(
                id,
                InnerToken::T_Script {
                    shebang,
                    commands: Vec::new(),
                },
            ));
        }

        let commands = self.read_compound_list_or_empty();
        self.read_pending_heredocs().ok()?;
        // verify EOF: if not at end, it's a parse problem (SC1072-ish). For the
        // slice we record a generic problem but still return the tree.
        self.allspacing();
        // `verifyEof` is only reached when the grammar ran to completion: if a
        // production already failed outright, that failure propagates out of
        // `readScriptFile` and this is never evaluated.
        if !self.eof() && !self.has_committed_failure() {
            self.verify_eof();
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

/// `readSource`'s `getFile`: the argument naming the sourced file, honouring
/// `--` and `source -p PATH file`.
fn source_file_arg(args: &[Token]) -> Option<&Token> {
    let (first, rest) = args.split_first()?;
    match ast_lib::get_literal_string(first).as_deref() {
        Some("--") => rest.first(),
        Some("-p") => rest.get(1),
        _ => Some(first),
    }
}

/// `ASTLib.isStringExpansion`: an expansion that yields a string, as opposed to
/// an array or a glob.
fn is_string_expansion(t: &Token) -> bool {
    ast_lib::is_command_substitution(t)
        || match &*t.inner {
            InnerToken::T_DollarArithmetic(_) => true,
            InnerToken::T_DollarBraced { .. } => !crate::analyzer_lib::is_array_expansion(t),
            _ => false,
        }
}

/// `readSource`'s `stripDynamicPrefix`: a word whose single leading expansion is
/// the directory part, as in `$foo/bar` (but not `${foo}-dir/bar` or
/// `/foo/$file`), is looked for relative to the working directory instead.
fn strip_dynamic_prefix(word: &Token) -> Option<String> {
    let parts = ast_lib::get_word_parts(word);
    let (first, rest) = parts.split_first()?;
    if !is_string_expansion(first) {
        return None;
    }
    let rest_word = Token::new(
        Id(0),
        InnerToken::T_NormalWord(rest.iter().map(|t| (*t).clone()).collect()),
    );
    let str = ast_lib::get_literal_string(&rest_word)?;
    if !str.starts_with('/') {
        return None;
    }
    Some(format!(".{str}"))
}

/// `unquote`: a delimiter wrapped in matching quotes is quoted and loses them;
/// otherwise a backslash anywhere makes it quoted, and the backslashes go.
fn unquote_here_delim(s: &str) -> (String, Quoted) {
    let chars: Vec<char> = s.chars().collect();
    if chars.len() < 2 {
        return (s.to_string(), Quoted::Unquoted);
    }
    let first = chars[0];
    let last = chars[chars.len() - 1];
    if first == last && (first == '"' || first == '\'') {
        return (chars[1..chars.len() - 1].iter().collect(), Quoted::Quoted);
    }
    if s.contains('\\') {
        return (s.chars().filter(|c| *c != '\\').collect(), Quoted::Quoted);
    }
    (s.to_string(), Quoted::Unquoted)
}

/// Haskell's `lines`: split on `\n`, and no empty piece after a trailing one.
/// Unlike `str::lines` it leaves a `\r` where it found it.
fn haskell_lines(s: &str) -> impl Iterator<Item = &str> {
    let body = s.strip_suffix('\n').unwrap_or(s);
    let mut done = false;
    std::iter::from_fn(move || {
        if done {
            return None;
        }
        done = true;
        Some(body)
    })
    .flat_map(|b| b.split('\n'))
}
