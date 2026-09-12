//! Compound commands: subshells, groups, if/while/until/for/select/case and function definitions.
use super::*;

impl Parser {
    /// `readAmbiguous "((" readArithmeticExpression readSubshell`: `((` opens
    /// an arithmetic command in most shells and nested subshells in others.
    fn read_ambiguous_arithmetic(&mut self) -> PResult<Token> {
        self.read_ambiguous(
            |p| p.read_arithmetic_command(),
            |p| p.read_subshell(),
            |p, pos| {
                p.note_at(
                    pos.clone(),
                    pos,
                    Severity::ErrorC,
                    1105,
                    "Shells disambiguate (( differently or not at all. For subshell, add spaces around ( . For ((, fix parsing errors.",
                );
            },
        )
    }

    pub(super) fn read_compound_command(&mut self) -> PResult<Token> {
        let c = self.peek();
        let m = self.mark();
        let cmd = match c {
            Some('(') if self.peek_at(1) == Some('(') => self.read_ambiguous_arithmetic(),
            Some('(') => self.read_subshell(),
            Some('{') => self.read_brace_group(),
            _ => {
                // Each of these is a `tryWordToken`, whose missing-space
                // warning outlives the attempt.
                // `function` is a plain `string`, not a word token, so it has no
                // missing-space warning of its own.
                for kw in ["if", "while", "until", "for", "case", "select"] {
                    if self.word_matches(kw) {
                        self.warn_keyword_needs_space(kw);
                    }
                    self.miscased_keyword(kw);
                }
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
                    self.read_ambiguous_arithmetic()
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
                self.warn_on_tokens_after_compound_command();
                Ok(Token::new(id, InnerToken::T_Redirecting { redirs, cmd: t }))
            }
            Err(()) => {
                // The cursor is left where the attempt gave up: callers need it
                // to tell a recoverable failure from one that has committed.
                if self.idx == m.idx {
                    self.reset(m);
                }
                Err(())
            }
        }
    }

    /// A compound command is finished; anything but a keyword or a `{` still
    /// sitting there is a missing terminator or a mistyped redirection. Read
    /// under `lookAhead`, so the words themselves are put back.
    fn warn_on_tokens_after_compound_command(&mut self) {
        // `notFollowedBy2 $ choice [readKeyword, g_Lbrace]`, and `readKeyword`
        // includes `}`, `)` and `;;` as well as the closing words. It is
        // `unexpecting ""`, so a keyword that *is* there is read -- spacing and
        // all, as `tryToken` does -- and then failed on with "Unexpected ",
        // which is where Parsec's error ends up.
        if let Some(n) = self.keyword_len() {
            let m = self.mark();
            for _ in 0..n {
                self.bump();
            }
            self.spacing();
            // Inside `optional . lookAhead`, so the failure itself goes nowhere:
            // only its message and position survive.
            let _: PResult<()> = self.fail_recoverable("Unexpected ");
            self.reset(m);
            return;
        }
        if self.peek() == Some('{') {
            return;
        }
        let m = self.mark();
        let notes = self.notes.len();
        let pos = self.pos();
        // `many1 readNormalWord`, which does not skip spacing, so this stops at
        // the first gap — and never crosses a line. There is no `try` inside
        // this `lookAhead`, so a word that fails after consuming propagates:
        // `if true; then :; fi \`` is a parse error in the backtick.
        let mut any = false;
        loop {
            let wm = self.mark();
            match self.read_normal_word() {
                Ok(_) => any = true,
                Err(()) => {
                    if self.idx != wm.idx {
                        self.commit();
                        return;
                    }
                    self.reset(wm);
                    break;
                }
            }
        }
        let pos_end = self.pos();
        self.reset(m);
        // `lookAhead` rewinds Parsec's state, so the words' notes go with it;
        // problems live outside it and stay.
        self.notes.truncate(notes);
        if any {
            self.problem_at(
                pos,
                pos_end,
                Severity::ErrorC,
                1141,
                "Unexpected tokens after compound command. Bad redirection or missing ;/&&/||/|?",
            );
        }
    }

    pub(super) fn is_word_boundary_after(&self, n: usize) -> bool {
        match self.peek_at(n) {
            None => true,
            Some(c) => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ';',
        }
    }

    /// True if the input starts with `kw`, ignoring what follows.
    pub(super) fn word_matches(&self, kw: &str) -> bool {
        kw.chars()
            .enumerate()
            .all(|(i, ch)| self.peek_at(i) == Some(ch))
    }

    /// `anycaseString`: the keyword as actually written, if it is there in any
    /// mixture of cases.
    pub(super) fn word_matches_anycase(&self, kw: &str) -> Option<String> {
        let mut written = String::new();
        for (i, ch) in kw.chars().enumerate() {
            let c = self.peek_at(i)?;
            if !c.eq_ignore_ascii_case(&ch) {
                return None;
            }
            written.push(c);
        }
        Some(written)
    }

    /// `tryParseWordToken`: a keyword in the wrong case is recognised and
    /// reported, then rejected — inside a `try`, so the word goes on to parse
    /// as an ordinary one while the problem stands.
    pub(super) fn miscased_keyword(&mut self, kw: &str) {
        let Some(written) = self.word_matches_anycase(kw) else {
            return;
        };
        if written == kw || !self.at_keyword_separator(kw.chars().count()) {
            return;
        }
        let pos = self.pos();
        self.problem_at(
            pos.clone(),
            pos,
            Severity::ErrorC,
            1081,
            &format!(
                "Scripts are case sensitive. Use '{kw}', not '{written}' (or quote if literal)."
            ),
        );
    }

    /// True if the upcoming token is exactly `kw` followed by a word boundary.
    pub(super) fn keyword_ahead(&self, kw: &str) -> bool {
        self.word_matches(kw) && self.at_keyword_separator(kw.chars().count())
    }

    /// `keywordSeparator`: end of input, whitespace (a comment counts, since
    /// `spacing` eats one), or one of `;()[<>&|`. Notably *not* `$`, `'` or
    /// `{`, so `if$(x)` and `case''` are ordinary words.
    pub(super) fn at_keyword_separator(&self, offset: usize) -> bool {
        match self.peek_at(offset) {
            None => true,
            Some('\\') => self.peek_at(offset + 1) == Some('\n'),
            Some(c) => {
                c == ' '
                    || c == '\t'
                    || c == '\n'
                    || c == '\r'
                    || c == '#'
                    || ALMOST_SPACE_CHARS.contains(c)
                    || ";()[<>&|".contains(c)
            }
        }
    }

    /// `tryParseWordToken`'s warning: the keyword is there but runs straight
    /// into something that should have been a separate word. Reported whenever
    /// the keyword text matches, even when the token is then rejected — Haskell
    /// writes it to the problem channel, which no backtracking undoes.
    pub(super) fn warn_keyword_needs_space(&mut self, kw: &str) {
        let offset = kw.chars().count();
        let Some(c) = self.peek_at(offset) else {
            return;
        };
        let code = match c {
            '[' => 1069,
            '#' => 1099,
            '!' => 1129,
            ':' => 1130,
            _ => return,
        };
        let mut pos = self.pos();
        pos.column += offset as i64;
        self.problem_at(
            pos.clone(),
            pos,
            Severity::ErrorC,
            code,
            &format!("You need a space before the {c}."),
        );
    }

    pub(super) fn consume_keyword(&mut self, kw: &str) -> PResult<()> {
        if self.word_matches(kw) {
            self.warn_keyword_needs_space(kw);
        }
        if self.keyword_ahead(kw) {
            for _ in 0..kw.chars().count() {
                self.bump();
            }
            Ok(())
        } else {
            // `anycaseString` consumes the prefix that matched before failing,
            // and that is where Parsec's error sits -- `case '' i` reports the
            // end of input rather than the start of the missing `in`.
            let m = self.mark();
            let mut matched = 0;
            for c in kw.chars() {
                match self.peek() {
                    Some(p) if p.eq_ignore_ascii_case(&c) => {
                        self.bump();
                        matched += 1;
                    }
                    _ => break,
                }
            }
            if matched == kw.chars().count() {
                // The keyword is all there, so what failed is
                // `keywordSeparator`, whose `allspacingOrFail` is the only
                // alternative in it with something to say. `tryWordToken` is a
                // `try`, so the failure itself is caught.
                let _: PResult<()> = self.fail_recoverable("Expected whitespace");
            } else {
                self.fail_implicitly();
            }
            self.reset(m);
            Err(())
        }
    }

    pub(super) fn read_subshell(&mut self) -> PResult<Token> {
        self.called("explicit subshell", |p| p.read_subshell_body())
    }

    fn read_subshell_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('(')?;
        let list = self.read_compound_list_or_empty();
        self.allspacing();
        if list.is_empty() && self.eof() {
            // Haskell reads the body with `readCompoundList`, which is a
            // non-empty term: with nothing inside and nothing left to read,
            // the failure it reports is the missing command, not the `)`.
            return self.fail_with("Expected a command");
        }
        if self.char(')').is_err() {
            return self.fail_with("Expected ) closing the subshell");
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Subshell(list)))
    }

    pub(super) fn read_brace_group(&mut self) -> PResult<Token> {
        self.called("brace group", |p| p.read_brace_group_body())
    }

    fn read_brace_group_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('{')?;
        let spaced = {
            let before = self.idx;
            self.allspacing();
            self.idx != before
        };
        // `{(` is legal, so only an ordinary word needs the space.
        if !spaced && !matches!(self.peek(), None | Some('(')) {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1054,
                "You need a space after the '{'.",
            );
        }
        if self.peek() == Some('}') {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1055,
                "You need at least one command here. Use 'true;' as a no-op.",
            );
        }
        let list = self.read_term().ok_or(())?;
        self.allspacing();
        if self.has_committed_failure() {
            return Err(());
        }
        if self.char('}').is_err() {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1056,
                "Expected a '}'. If you have one, try a ; or \\n in front of it.",
            );
            return self.fail_with("Missing '}'");
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_BraceGroup(list)))
    }

    /// `readArithmeticDelimiter`: the doubled `((` / `))` of an arithmetic for
    /// loop, lenient about a space in the middle but not silent about it.
    fn read_arithmetic_delimiter(&mut self, c: char, msg: &str) -> PResult<()> {
        self.char(c)?;
        let start = self.pos();
        let before = self.idx;
        self.spacing();
        let end = self.pos();
        let spaced = self.idx != before;
        if self.char(c).is_err() {
            self.problem_at(start.clone(), start, Severity::ErrorC, 1137, msg);
            return self.fail_with("");
        }
        if spaced {
            self.problem_at(
                start,
                end,
                Severity::ErrorC,
                1138,
                &format!("Remove spaces between {c}{c} in arithmetic for loop."),
            );
        }
        Ok(())
    }

    /// `readBraced <|> readDoGroup`: `for` also accepts a brace group as its
    /// body, as ksh does.
    fn read_braced_or_do_group(&mut self, kw: &(Position, Position)) -> PResult<Vec<Token>> {
        self.allspacing();
        if self.peek() == Some('{') {
            let m = self.mark();
            if let Ok(t) = self.read_brace_group() {
                let InnerToken::T_BraceGroup(list) = t.inner() else {
                    unreachable!("readBraceGroup returns a T_BraceGroup")
                };
                return Ok(list.clone());
            }
            if self.idx != m.idx {
                return Err(());
            }
            self.reset(m);
        }
        self.read_do_group(kw)
    }

    /// `readDoGroup`: the `do .. done` body every loop shares. `kw` is where
    /// the loop keyword was, so a missing `do`/`done` can point back at it.
    fn read_do_group(&mut self, kw: &(Position, Position)) -> PResult<Vec<Token>> {
        self.allspacing();
        if self.keyword_ahead("done") {
            self.problem_at(
                kw.0.clone(),
                kw.1.clone(),
                Severity::ErrorC,
                1057,
                "Did you forget the 'do' for this loop?",
            );
        }
        let do_pos = self.pos();
        if self.has_committed_failure() {
            return Err(());
        }
        if self.consume_keyword("do").is_err() {
            let here = self.pos();
            self.problem_at(here.clone(), here, Severity::ErrorC, 1058, "Expected 'do'.");
            return self.fail_with("Expected 'do'");
        }
        // `parseProblemAtId (getId doKw)`: the span is the `do` token itself.
        let do_end = self.pos();
        self.accept_but_warn_semi_msg(
            1059,
            "Semicolon is not allowed directly after 'do'. You can just delete it.",
        );
        self.allspacing();
        if self.keyword_ahead("done") {
            self.problem_at(
                do_pos.clone(),
                do_end.clone(),
                Severity::ErrorC,
                1060,
                "Can't have empty do clauses (use 'true' as a no-op).",
            );
        }
        let commands = self.read_term().ok_or(())?;
        self.allspacing();
        if self.has_committed_failure() {
            // Something inside gave up for good; that failure is the report.
            return Err(());
        }
        if self.consume_keyword("done").is_err() {
            self.problem_at(
                do_pos.clone(),
                do_end,
                Severity::ErrorC,
                1061,
                "Couldn't find 'done' for this 'do'.",
            );
            let here = self.pos();
            self.problem_at(
                here.clone(),
                here,
                Severity::ErrorC,
                1062,
                "Expected 'done' matching previously mentioned 'do'.",
            );
            return self.fail_with("Expected 'done'");
        }
        // `g_Done` is `tryWordToken "done" .. `thenSkip` spacing`, so the loop's
        // span extends over the line-whitespace after `done` and a trailing
        // redirect starts beyond it.
        self.spacing();
        if self.string_peek("<(") {
            let here = self.pos();
            self.problem_at(
                here.clone(),
                here,
                Severity::ErrorC,
                1142,
                "Use 'done < <(cmd)' to redirect from process substitution (currently missing one '<').",
            );
        }
        Ok(commands)
    }

    pub(super) fn read_if_clause(&mut self) -> PResult<Token> {
        self.called("if expression", |p| p.read_if_clause_body())
    }

    fn read_if_clause_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        let pos = self.pos();
        let mut clauses: Vec<IfClause> = Vec::new();
        clauses.push(self.read_if_part()?);
        // `many` and `option` recover only from a failure that consumed
        // nothing: an `elif`/`else` that was started and then went wrong is
        // the if expression's failure, not an absent clause.
        loop {
            self.allspacing();
            let m = self.mark();
            match self.read_elif_part() {
                Ok(c) => clauses.push(c),
                Err(()) => {
                    if self.idx != m.idx {
                        return Err(());
                    }
                    self.reset(m);
                    break;
                }
            }
        }
        self.allspacing();
        let m = self.mark();
        let elses = match self.read_else_part() {
            Ok(e) => e,
            Err(()) => {
                if self.idx != m.idx {
                    return Err(());
                }
                self.reset(m);
                Vec::new()
            }
        };
        self.allspacing();
        if self.has_committed_failure() {
            return Err(());
        }
        if self.consume_keyword("fi").is_err() {
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1046,
                "Couldn't find 'fi' for this 'if'.",
            );
            let here = self.pos();
            self.problem_at(
                here.clone(),
                here,
                Severity::ErrorC,
                1047,
                "Expected 'fi' matching previously mentioned 'if'.",
            );
            return self.fail_with("Expected 'fi'");
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_IfExpression { clauses, elses },
        ))
    }

    fn read_if_part(&mut self) -> PResult<IfClause> {
        let pos = self.pos();
        self.consume_keyword("if")?;
        self.allspacing();
        let condition = self.read_condition_list()?;
        if self.at_if_branch_keyword() {
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1049,
                "Did you forget the 'then' for this 'if'?",
            );
        }
        self.called("then clause", |p| {
            p.allspacing();
            if p.has_committed_failure() {
                return Err(());
            }
            if p.consume_keyword("then").is_err() {
                let here = p.pos();
                p.problem_at(
                    here.clone(),
                    here,
                    Severity::ErrorC,
                    1050,
                    "Expected 'then'.",
                );
                return p.fail_with("Expected 'then'");
            }
            p.accept_but_warn_semi(1051, "then");
            p.allspacing();
            p.verify_not_empty_if("then");
            let action = p.read_term().ok_or(())?;
            Ok((condition, action))
        })
    }

    fn read_elif_part(&mut self) -> PResult<IfClause> {
        self.called("elif clause", |p| {
            let pos = p.pos();
            p.consume_keyword("elif")?;
            p.allspacing();
            let condition = p.read_condition_list()?;
            if p.at_if_branch_keyword() {
                p.problem_at(
                    pos.clone(),
                    pos,
                    Severity::ErrorC,
                    1049,
                    "Did you forget the 'then' for this 'elif'?",
                );
            }
            p.allspacing();
            p.consume_keyword("then")?;
            p.accept_but_warn_semi(1052, "then");
            p.allspacing();
            p.verify_not_empty_if("then");
            let action = p.read_term().ok_or(())?;
            Ok((condition, action))
        })
    }

    fn read_else_part(&mut self) -> PResult<Vec<Token>> {
        self.called("else clause", |p| {
            let pos = p.pos();
            p.consume_keyword("else")?;
            // `else if` is a nested `if` needing its own `fi`, which is almost
            // always a typo for `elif`.
            let m = p.mark();
            p.spacing();
            let nested_if = p.keyword_ahead("if");
            p.reset(m);
            if nested_if {
                p.problem_at(
                    pos.clone(),
                    pos,
                    Severity::ErrorC,
                    1075,
                    "Use 'elif' instead of 'else if' (or put 'if' on new line if nesting).",
                );
            }
            p.accept_but_warn_semi(1053, "else");
            p.allspacing();
            p.verify_not_empty_if("else");
            p.read_term().ok_or(())
        })
    }

    /// `ifNextToken (g_Fi <|> g_Elif <|> g_Else)`.
    fn at_if_branch_keyword(&self) -> bool {
        ["fi", "elif", "else"].iter().any(|k| self.keyword_ahead(k))
    }

    /// `verifyNotEmptyIf`: the clause runs straight into what closes it.
    fn verify_not_empty_if(&mut self, clause: &str) {
        if self.at_if_branch_keyword() {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1048,
                &format!("Can't have empty {clause} clauses (use 'true' as a no-op)."),
            );
        }
    }

    /// `acceptButWarn g_Semi`: a `;` right after `then`/`else` is a syntax
    /// error the parser forgives after saying so.
    fn accept_but_warn_semi(&mut self, code: i64, after: &str) {
        let msg = format!("Semicolons directly after '{after}' are not allowed. Just remove it.");
        self.accept_but_warn_semi_msg(code, &msg);
    }

    fn accept_but_warn_semi_msg(&mut self, code: i64, message: &str) {
        let m = self.mark();
        self.spacing();
        if self.peek() == Some(';') && self.peek_at(1) != Some(';') {
            let pos = self.pos();
            self.bump();
            self.problem_at(pos.clone(), pos, Severity::ErrorC, code, message);
        } else {
            self.reset(m);
        }
    }

    pub(super) fn read_condition_list(&mut self) -> PResult<Vec<Token>> {
        self.allspacing();
        let first = self.read_and_or()?;
        self.read_term_more(first)
    }

    pub(super) fn read_while_clause(&mut self) -> PResult<Token> {
        self.called("while loop", |p| p.read_while_clause_body())
    }

    fn read_while_clause_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        // `parseProblemAtId kwId`: the loop keyword's own span.
        let kw_start = self.pos();
        self.consume_keyword("while")?;
        let kw = (kw_start, self.pos());
        let cond = self.read_condition_list()?;
        let body = self.read_do_group(&kw)?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_WhileExpression {
                condition: cond,
                body,
            },
        ))
    }

    pub(super) fn read_until_clause(&mut self) -> PResult<Token> {
        self.called("until loop", |p| p.read_until_clause_body())
    }

    fn read_until_clause_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        let kw_start = self.pos();
        self.consume_keyword("until")?;
        let kw = (kw_start, self.pos());
        let cond = self.read_condition_list()?;
        let body = self.read_do_group(&kw)?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_UntilExpression {
                condition: cond,
                body,
            },
        ))
    }

    pub(super) fn read_for_clause(&mut self) -> PResult<Token> {
        self.called("for loop", |p| p.read_for_clause_body())
    }

    fn read_for_clause_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("for")?;
        let kw = (start.clone(), self.pos());
        // ShellCheck reuses the `for` keyword id for the whole T_ForIn/T_ForArithmetic
        // node, so SC2034 (and others) point at `for`, not the entire loop.
        let for_end = self.pos();
        self.spacing();
        // arithmetic for: for ((init; cond; step))
        if self.peek() == Some('(') {
            let id_span = (start.clone(), for_end.clone());
            return self.called("arithmetic for condition", |p| {
                p.read_arithmetic_delimiter(
                    '(',
                    "Missing second '(' to start arithmetic for ((;;)) loop",
                )?;
                let init = p.read_arithmetic_contents()?;
                p.char(';')?;
                p.spacing();
                let cond = p.read_arithmetic_contents()?;
                p.char(';')?;
                p.spacing();
                let step = p.read_arithmetic_contents()?;
                p.spacing();
                p.read_arithmetic_delimiter(
                    ')',
                    "Missing second ')' to terminate 'for ((;;))' loop condition",
                )?;
                p.spacing();
                // optional sequential separator, then do..done (or brace group)
                p.allspacing();
                let _ = p.char(';');
                p.allspacing();
                let body = p.read_braced_or_do_group(&kw)?;
                let id = p.next_id_between(id_span.0, id_span.1);
                Ok(Token::new(
                    id,
                    InnerToken::T_ForArithmetic {
                        init,
                        cond,
                        step,
                        body,
                    },
                ))
            });
        }
        // `readRegular`: `acceptButWarn (char '$')`, the name, then
        // `allspacing` -- so the `in` may be on the next line.
        let m = self.mark();
        let dollar = self.pos();
        if self.char('$').is_ok() {
            self.problem_at(
                dollar.clone(),
                dollar,
                Severity::ErrorC,
                1086,
                "Don't use $ on the iterator name in for loops.",
            );
        } else {
            self.reset(m);
        }
        let var = self.read_variable_name()?;
        self.allspacing();
        let items = match self.read_in_clause() {
            Ok(v) => v,
            Err(()) => {
                // `optional readSequentialSep >> return []`
                let m = self.mark();
                if self.char(';').is_ok() {
                    self.line_break();
                } else {
                    self.reset(m);
                    self.allspacing();
                }
                Vec::new()
            }
        };
        let body = self.read_braced_or_do_group(&kw)?;
        let id = self.next_id_between(start.clone(), for_end);
        Ok(Token::new(id, InnerToken::T_ForIn { var, items, body }))
    }

    /// `readInClause`: `in`, the words up to the first `;`, linefeed or `do`,
    /// and then the separator that ends the list.
    pub(super) fn read_in_clause(&mut self) -> PResult<Vec<Token>> {
        // `g_In` is a `tryWordToken`, so it backs out without consuming, and
        // takes the spacing after the keyword with it.
        self.consume_keyword("in")?;
        self.spacing();
        let mut items = Vec::new();
        // `readCmdWord `reluctantlyTill` (g_Semi <|> linefeed <|> g_Do)`
        loop {
            if self.eof() || self.at_in_clause_end() {
                break;
            }
            let m = self.mark();
            match self.read_normal_word() {
                Ok(w) => {
                    items.push(w);
                    self.spacing();
                }
                Err(()) => {
                    // `reluctantlyTill` ends on `<|> return []`, which only
                    // catches a failure that consumed nothing.
                    if self.idx != m.idx {
                        return Err(());
                    }
                    self.reset(m);
                    break;
                }
            }
        }
        if self.keyword_ahead("do") {
            let pos = self.pos();
            self.note_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1063,
                "You need a line feed or semicolon before the 'do'.",
            );
        } else {
            let m = self.mark();
            if self.char(';').is_err() {
                self.reset(m);
            }
            self.allspacing();
        }
        Ok(items)
    }

    /// The `reluctantlyTill` end condition of `readInClause`: a `;` that is not
    /// a `;;`, a linefeed, or the `do` keyword.
    fn at_in_clause_end(&mut self) -> bool {
        match self.peek() {
            Some(';') => self.peek_at(1) != Some(';'),
            Some('\n') | Some('\r') => true,
            _ => self.keyword_ahead("do"),
        }
    }

    /// `readBatsTest`: `@test <name> { ... }`, where <name> is everything on the
    /// line up to the last ` {`.
    pub(super) fn read_bats_test(&mut self) -> PResult<Token> {
        self.called("bats @test", |p| p.read_bats_test_body())
    }

    fn read_bats_test_body(&mut self) -> PResult<Token> {
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

    pub(super) fn read_select_clause(&mut self) -> PResult<Token> {
        self.called("select loop", |p| p.read_select_clause_body())
    }

    fn read_select_clause_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("select")?;
        let kw = (start.clone(), self.pos());
        // ShellCheck reuses the `select` keyword id for the whole T_SelectIn node.
        let sel_end = self.pos();
        self.spacing();
        let var = self.read_variable_name()?;
        self.spacing();
        let items = match self.read_in_clause() {
            Ok(v) => v,
            Err(()) => {
                // `readSequentialSep >> return []`: required here, unlike the
                // `for` loop's optional one.
                let m = self.mark();
                if self.char(';').is_ok() {
                    self.line_break();
                } else {
                    self.reset(m);
                    if self.linefeed_or_carriage_return().is_err() {
                        return Err(());
                    }
                    self.allspacing();
                }
                Vec::new()
            }
        };
        let body = self.read_do_group(&kw)?;
        let id = self.next_id_between(start.clone(), sel_end);
        Ok(Token::new(id, InnerToken::T_SelectIn { var, items, body }))
    }

    pub(super) fn read_case_clause(&mut self) -> PResult<Token> {
        self.called("case expression", |p| p.read_case_clause_body())
    }

    fn read_case_clause_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("case")?;
        self.spacing();
        let word = self.read_normal_word()?;
        self.allspacing();
        if self.consume_keyword("in").is_err() {
            return self.fail_with("Expected 'in'");
        }
        self.allspacing();
        // `many readCaseItem`: an item that failed after consuming input is the
        // case expression's failure, not the end of the list.
        let mut cases: Vec<CaseClause> = Vec::new();
        loop {
            self.allspacing();
            let m = self.mark();
            match self.read_case_item() {
                Ok(c) => cases.push(c),
                Err(()) => {
                    if self.idx != m.idx {
                        return Err(());
                    }
                    self.reset(m);
                    break;
                }
            }
        }
        self.allspacing();
        if self.has_committed_failure() {
            return Err(());
        }
        if self.consume_keyword("esac").is_err() {
            return self.fail_with("Expected 'esac' to close the case statement");
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_CaseExpression { word, cases }))
    }

    fn read_case_item(&mut self) -> PResult<CaseClause> {
        // `notFollowedBy2 g_Esac`
        if self.keyword_ahead("esac") {
            return Err(());
        }
        self.called("case item", |p| {
            if p.at_annotation_prefix() {
                let pos = p.pos();
                p.problem_at(
                    pos.clone(),
                    pos,
                    Severity::ErrorC,
                    1124,
                    "ShellCheck directives are only valid in front of complete commands like 'case' statements, not individual case branches.",
                );
            }
            // optional leading (
            let _ = p.char('(');
            p.spacing();
            // `readPattern`: words separated by `|`.
            // `readPattern` is a `sepBy1`: a case item needs at least one
            // pattern word, and without one it is not an item at all.
            let mut pats = vec![p.read_pattern_word()?];
            p.spacing();
            while p.char('|').is_ok() {
                p.spacing();
                pats.push(p.read_pattern_word()?);
                p.spacing();
            }
            if p.char(')').is_err() {
                if p.has_committed_failure() {
                    return Err(());
                }
                let pos = p.pos();
                p.problem_at(
                    pos.clone(),
                    pos,
                    Severity::ErrorC,
                    1085,
                    "Did you forget to move the ;; after extending this case item?",
                );
                return p.fail_with("Expected ) to open a new case item");
            }
            let body = p.read_case_body();
            // `readCaseSeparator`: the `;;` arm and the no-separator-before-esac
            // arm both yield CaseBreak. They are NOT interchangeable — the `;;`
            // condition consumes the separator, the fallback consumes nothing.
            #[allow(clippy::if_same_then_else)]
            let ctype = if p.string(";;&").is_ok() {
                CaseType::CaseContinue
            } else if p.string(";&").is_ok() {
                CaseType::CaseFallThrough
            } else if p.string(";;").is_ok() {
                CaseType::CaseBreak
            } else {
                // `attempting`: a `)` ahead and no separator means the previous
                // item ran straight into the next one.
                let m = p.mark();
                let pos = p.pos();
                if p.peek() == Some(')') {
                    p.problem_at(
                        pos.clone(),
                        pos,
                        Severity::ErrorC,
                        1074,
                        "Did you forget the ;; after the previous case item?",
                    );
                }
                // The last arm of `readCaseSeparator`: a line break and then
                // `esac` ends the item without one. Anything else is a failure.
                p.allspacing();
                let at_esac = p.keyword_ahead("esac");
                p.reset(m);
                if !at_esac {
                    return Err(());
                }
                CaseType::CaseBreak
            };
            Ok((ctype, pats, body))
        })
    }

    /// True at a case-clause terminator: `;;`, `;&`, or `;;&`.
    pub(super) fn at_case_terminator(&self) -> bool {
        self.peek() == Some(';') && matches!(self.peek_at(1), Some(';') | Some('&'))
    }

    pub(super) fn read_case_body(&mut self) -> Vec<Token> {
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
    pub(super) fn looks_like_posix_function(&self) -> bool {
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
        // `readWithoutFunction` is a bare `try` with no lookahead: a `(` after
        // the name is enough to attempt it, and `readParens` reports SC1065 on
        // the way out when the parameter list is botched.
        true
    }

    /// `readWithoutFunction`: `name ( )` then a brace-group or subshell body.
    /// Both this and the `function` keyword form are one `called "function"`
    /// production in Haskell, so both name the function in SC1073/SC1009.
    pub(super) fn read_posix_function(&mut self) -> PResult<Token> {
        self.called("function", |p| p.read_posix_function_body())
    }

    fn read_posix_function_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        // `readWithoutFunction` is a `try`: the signature either parses or
        // leaves nothing consumed, whatever `readParens` reported on the way.
        let sm = self.mark();
        let signature = (|p: &mut Self| -> PResult<String> {
            let name = p.read_function_name()?;
            if name == "time" {
                // `guard $ name /= "time"` -- it would take `time ( foo )`.
                return Err(());
            }
            p.spacing();
            p.read_function_parens()?;
            Ok(name)
        })(self);
        let name = match signature {
            Ok(n) => n,
            Err(()) => {
                self.reset(sm);
                return Err(());
            }
        };
        self.allspacing();
        let body = if self.peek() == Some('{') {
            self.read_brace_group()?
        } else if self.peek() == Some('(') {
            self.read_subshell()?
        } else {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1064,
                "Expected a { to open the function definition.",
            );
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

    /// `readParens`: `( )` with anything between it reported as a doomed
    /// attempt at a parameter list, then skipped.
    fn read_function_parens(&mut self) -> PResult<()> {
        self.char('(')?;
        self.spacing();
        if self.char(')').is_ok() {
            return Ok(());
        }
        let pos = self.pos();
        self.problem_at(
            pos.clone(),
            pos,
            Severity::ErrorC,
            1065,
            "Trying to declare parameters? Don't. Use () and refer to params as $1, $2..",
        );
        while matches!(self.peek(), Some(c) if c != '\n' && c != ')' && c != '{') {
            self.bump();
        }
        self.char(')').map(|_| ())
    }

    pub(super) fn read_function_def(&mut self) -> PResult<Token> {
        self.called("function", |p| p.read_function_def_body())
    }

    fn read_function_def_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.consume_keyword("function")?;
        self.spacing();
        let name = self.read_function_name_ext(true)?;
        let before_spaces = self.idx;
        self.spacing();
        let had_spaces = self.idx != before_spaces;
        // optional ()
        let has_parens = if self.peek() == Some('(') {
            self.read_function_parens()?;
            true
        } else {
            false
        };
        if !has_parens && !had_spaces && matches!(self.peek(), Some('{') | Some('(')) {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1095,
                "You need a space or linefeed between the function name and body.",
            );
        }
        self.allspacing();
        // `readBraceGroup <|> readSubshell`, after a lookahead that says which
        // it should have been.
        let body = if self.peek() == Some('{') {
            self.read_brace_group()?
        } else if self.peek() == Some('(') {
            self.read_subshell()?
        } else {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1064,
                "Expected a { to open the function definition.",
            );
            return Err(());
        };
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

    /// `functionStartChars` then `many functionChars`, which unlike the start
    /// set includes `#` — so `foo#bar` is one name, not a name and a comment.
    /// After the `function` keyword both sets also take `[]*=!`.
    pub(super) fn read_function_name(&mut self) -> PResult<String> {
        self.read_function_name_ext(false)
    }

    pub(super) fn read_function_name_ext(&mut self, extended: bool) -> PResult<String> {
        let extra = if extended { "[]*=!" } else { "" };
        let is_start =
            |c: char| c.is_ascii_alphanumeric() || "_:+?-./^@,".contains(c) || extra.contains(c);
        let is_cont =
            |c: char| c.is_ascii_alphanumeric() || "_#:+?-./^@,".contains(c) || extra.contains(c);
        let mut s = String::new();
        match self.peek() {
            Some(c) if is_start(c) => {
                self.bump();
                s.push(c);
            }
            _ => return Err(()),
        }
        while let Some(c) = self.peek() {
            if is_cont(c) {
                self.bump();
                s.push(c);
            } else {
                break;
            }
        }
        Ok(s)
    }
}
