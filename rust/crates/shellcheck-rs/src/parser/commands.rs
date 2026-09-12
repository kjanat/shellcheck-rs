//! Lists, pipelines, simple commands, redirections, here-docs and the script entry (`ShellCheck.Parser` readScript / readSimpleCommand family).
use super::*;

impl Parser {
    pub(super) fn empty_literal(&mut self) -> Token {
        let p = self.pos();
        let id = self.next_id_between(p.clone(), p);
        Token::new(id, InnerToken::T_Literal(String::new()))
    }

    pub(super) fn read_shebang(&mut self) -> Option<Token> {
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

    pub(super) fn read_separator_op(&mut self) -> Option<char> {
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
            Some(';') if self.peek_at(1) != Some(';') => {
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

    pub(super) fn read_compound_list_or_empty(&mut self) -> Vec<Token> {
        self.allspacing();
        self.read_term().unwrap_or_default()
    }

    pub(super) fn read_term(&mut self) -> Option<Vec<Token>> {
        self.allspacing();
        let first = self.read_and_or().ok()?;
        Some(self.read_term_more(first))
    }

    pub(super) fn read_term_more(&mut self, current: Token) -> Vec<Token> {
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

    pub(super) fn read_and_or(&mut self) -> PResult<Token> {
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

    pub(super) fn allspacing_no_newline(&mut self) {
        self.spacing();
    }

    pub(super) fn read_pipeline(&mut self) -> PResult<Token> {
        // `unexpecting "keyword/token" readKeyword`: a word that closes a
        // compound command cannot start one. The keyword is read and then
        // rejected, so the error lands past it, and the whole thing sits in a
        // `try`, so an enclosing alternative can still take over.
        if let Some(n) = self.keyword_len() {
            let m = self.mark();
            for _ in 0..n {
                self.bump();
            }
            // Recorded from past the keyword, where the `fail` inside the
            // inner `try` happens, before the outer one rewinds.
            let r = self.fail_recoverable("Unexpected keyword/token");
            self.reset(m);
            return r;
        }
        self.read_banged()
    }

    /// `readKeyword`: how long the closing keyword ahead is, plus the
    /// missing-space warning each word token leaves behind even when the
    /// lookahead that called it goes on to reject the keyword.
    pub(super) fn keyword_len(&mut self) -> Option<usize> {
        const WORDS: [&str; 7] = ["then", "else", "elif", "fi", "do", "done", "esac"];
        // Every alternative in the `choice` is attempted, so a longer keyword
        // sharing a prefix with a shorter one still gets its own warning.
        let mut found = None;
        for w in WORDS {
            if !self.word_matches(w) {
                continue;
            }
            self.warn_keyword_needs_space(w);
            if found.is_none() && self.at_keyword_separator(w.len()) {
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

    pub(super) fn read_banged(&mut self) -> PResult<Token> {
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
    pub(super) fn read_banged_command(&mut self) -> PResult<Token> {
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

    pub(super) fn read_command(&mut self) -> PResult<Token> {
        // Reserved words that close a compound list must not be read as command
        // names (mirrors `readPipeline`'s `unexpecting readKeyword`). Without
        // this, e.g. `for..do..done`'s body swallows `done` and the loop fails.
        if self.at_command_terminator() {
            return Err(());
        }
        // `choice` is a fold of bare `<|>`: once a compound command has
        // consumed input there is no going back to a simple one, so `((`
        // reports an unfinished arithmetic command rather than quietly
        // becoming a word.
        let m = self.mark();
        match self.read_compound_command() {
            Ok(t) => return Ok(t),
            Err(()) => {
                if self.idx != m.idx {
                    self.committed = true;
                    return Err(());
                }
            }
        }
        match self.read_condition_command() {
            Ok(t) => return Ok(t),
            Err(()) => {
                if self.idx != m.idx {
                    self.committed = true;
                    return Err(());
                }
            }
        }
        match self.read_coproc() {
            Ok(t) => return Ok(t),
            Err(()) => {
                if self.idx != m.idx {
                    self.committed = true;
                    return Err(());
                }
            }
        }
        // The last alternative in the `choice`: nothing can take over from a
        // simple command that failed after consuming input.
        let r = self.read_simple_command();
        if r.is_err() && self.idx != m.idx {
            self.committed = true;
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
        let mc = self.mark();
        if let Ok(t) = self.read_compound_coproc(start.clone()) {
            return Ok(t);
        }
        self.reset(mc);
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

    /// True if the upcoming token is a reserved word/operator that terminates a
    /// command list (`then else elif fi do done esac`, `}`).
    pub(super) fn at_command_terminator(&self) -> bool {
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

    pub(super) fn read_arithmetic_command(&mut self) -> PResult<Token> {
        self.called("((..)) command", |p| p.read_arithmetic_command_body())
    }

    fn read_arithmetic_command_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("((")?;
        let c = self.read_arithmetic_contents()?;
        self.string("))")?;
        // `spacing`, not `allspacing`: the node ends on its own line.
        self.spacing();
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Arithmetic(c)))
    }

    // ---- simple command ----------------------------------------------------

    pub(super) fn read_simple_command(&mut self) -> PResult<Token> {
        self.called("simple command", |p| p.read_simple_command_body())
    }

    fn read_simple_command_body(&mut self) -> PResult<Token> {
        let prefix = self.read_cmd_prefix();
        self.spacing();
        let cmd = self.read_cmd_name();
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
                suffix = self.read_time_suffix()?;
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
    pub(super) fn read_time_suffix(&mut self) -> PResult<Vec<Token>> {
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
            if let Ok(a) = self.read_assignment_word() {
                out.push(a);
                continue;
            }
            self.reset(m);
            break;
        }
        out
    }

    pub(super) fn read_cmd_name(&mut self) -> Option<Token> {
        let m = self.mark();
        // don't treat keywords as command names in command position handled by caller
        match self.read_normal_word() {
            Ok(w) => Some(w),
            Err(()) => {
                // `readCmdName` is not behind a `try`, so a word that failed
                // after consuming input ends the parse rather than leaving the
                // command nameless.
                if self.idx != m.idx {
                    self.committed = true;
                }
                self.reset(m);
                None
            }
        }
    }

    pub(super) fn read_cmd_suffix(&mut self, modifier: bool) -> Vec<Token> {
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
                    // `many` stops on a failure that consumed nothing; one that
                    // consumed ends the parse, as a trailing `\` does.
                    if self.idx != m.idx {
                        self.committed = true;
                    }
                    self.reset(m);
                    break;
                }
            }
        }
        out
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
    pub(super) fn sub_parse_arithmetic(&mut self, pos: &Position, src: &str) -> Option<Token> {
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

    /// Read one raw `let` argument word (tracking quotes), returning the raw
    /// text and its start position. Mirrors `readStringForParser readCmdWord`.
    pub(super) fn read_let_arg_raw(&mut self) -> Option<(String, Position)> {
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
    pub(super) fn read_let_suffix(&mut self) -> Vec<Token> {
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
        // `inSeparateContext $ lookAhead ..` rolls its state back whether it
        // succeeded or not, so nothing the span leaves behind survives.
        let m = self.mark();
        let notes = self.notes.len();
        let problems = self.problems.len();
        let contexts = self.contexts.clone();
        let failure = self.failure.clone();
        let spanned = self.read_index_span();
        let end_idx = self.idx;
        self.reset(m);
        self.notes.truncate(notes);
        self.problems.truncate(problems);
        self.contexts = contexts;
        self.failure = failure;
        spanned?;
        let raw: String = self.input[m.idx..end_idx].iter().collect();
        while self.idx < end_idx {
            self.bump();
        }
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

    pub(super) fn read_assignment_word(&mut self) -> PResult<Token> {
        self.called("variable assignment", |p| p.read_assignment_word_body())
    }

    fn read_assignment_word_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        // Everything up to and including the `=` is read inside a `try`: a word
        // that turns out not to be an assignment must leave the cursor where it
        // started, so the enclosing `called` unwinds and leaves no context
        // behind either.
        let prefix = self.mark();
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
                        let vm = self.mark();
                        match self.read_array() {
                            Ok(a) => a,
                            Err(()) => {
                                self.reset(vm);
                                self.empty_literal_word()
                            }
                        }
                    } else {
                        match self.read_normal_word() {
                            Ok(w) => w,
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
                let am = self.mark();
                match self.read_array() {
                    Ok(a) => {
                        elems.push(a);
                        continue;
                    }
                    Err(()) => self.reset(am),
                }
            }
            match self.read_normal_word() {
                Ok(w) => elems.push(w),
                Err(()) => break,
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

    pub(super) fn read_io_file_op(&mut self, start: Position) -> Option<Token> {
        let (inner, len): (InnerToken, usize) = match (self.peek(), self.peek_at(1)) {
            (Some('>'), Some('>')) => (InnerToken::T_DGREAT, 2),
            (Some('<'), Some('>')) => (InnerToken::T_LESSGREAT, 2),
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
            return self.read_here_string(start, op_start, fd);
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

    pub(super) fn read_heredoc_delim(&mut self) -> PResult<(String, Quoted)> {
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

    pub(super) fn read_pending_heredocs(&mut self) -> PResult<()> {
        if self.pending_heredocs.is_empty() {
            return Ok(());
        }
        let pending: Vec<PendingHereDoc> = std::mem::take(&mut self.pending_heredocs);
        for hd in pending {
            // `swapContext`: the body is read long after the redirection was
            // parsed, so the diagnostics name the `<<` and what contained it.
            let outer = std::mem::replace(&mut self.contexts, hd.contexts.clone());
            let r = self.read_pending_here_doc(&hd);
            if r.is_ok() {
                self.contexts = outer;
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
                self.committed = true;
                return self.fail_with("Here document was not correctly terminated");
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
                Quoted::Unquoted => self.read_here_data(&body, doc_start),
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
        let mut at_token = |code: i64, msg: String| {
            self.problems.push(ParseNote {
                start: start.clone(),
                end: end.clone(),
                severity: Severity::ErrorC,
                code,
                message: msg,
            });
        };
        let token = &hd.delim;
        if doc.contains(token.as_str()) {
            at_token(
                1041,
                format!("Found '{token}' further down, but not on a separate line."),
            );
            for line in doc.lines() {
                if line.contains(token.as_str()) {
                    at_token(
                        1042,
                        format!("Close matches include '{line}' (!= '{token}')."),
                    );
                }
            }
        } else if doc.to_lowercase().contains(&token.to_lowercase()) {
            at_token(
                1043,
                format!("Found {token} further down, but with wrong casing."),
            );
        } else {
            at_token(
                1044,
                format!("Couldn't find end token `{token}' in the here document."),
            );
        }
    }

    /// `readHereData` (Parser.hs): sub-parse an unquoted here-doc body into the
    /// same token stream a double-quoted string produces (literals, dollar
    /// expansions, backtick command substitutions), with `"` and other
    /// non-`` `$\ `` characters kept literal via `readHereLiteral`.
    pub(super) fn read_here_data(&mut self, body: &str, start: Position) -> Vec<Token> {
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
    fn verify_eof(&mut self) {
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
    fn at_keyword(&self) -> bool {
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

        // `verifyShebang` (Parser.hs readScriptFile): warn on an unrecognized
        // interpreter, unless a `# shellcheck shell=...` directive overrides the
        // shebang. Emitted at the start of the file, like `parseProblemAt pos`.
        let ignore_shebang = self.shell_flag_specified
            || file_annotations
                .iter()
                .any(|a| matches!(a, Annotation::ShellOverride(_)));
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
