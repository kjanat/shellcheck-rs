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
        if self.keyword_len().is_some() || self.peek() == Some('{') {
            return;
        }
        let m = self.mark();
        let notes = self.notes.len();
        let pos = self.pos();
        // `many1 readNormalWord`, which does not skip spacing, so this stops at
        // the first gap — and never crosses a line.
        let mut any = false;
        while self.read_normal_word().is_ok() {
            any = true;
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

    /// `readBraced <|> readDoGroup`: `for` also accepts a brace group as its
    /// body, as ksh does.
    fn read_braced_or_do_group(&mut self, kw: &Position) -> PResult<Vec<Token>> {
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
    fn read_do_group(&mut self, kw: &Position) -> PResult<Vec<Token>> {
        self.allspacing();
        if self.keyword_ahead("done") {
            self.problem_at(
                kw.clone(),
                kw.clone(),
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
        Ok(self.read_term_more(first))
    }

    pub(super) fn read_while_clause(&mut self) -> PResult<Token> {
        self.called("while loop", |p| p.read_while_clause_body())
    }

    fn read_while_clause_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        let kw = self.pos();
        self.consume_keyword("while")?;
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
        let kw = self.pos();
        self.consume_keyword("until")?;
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
            let body = self.read_braced_or_do_group(&start)?;
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
        let body = self.read_braced_or_do_group(&start)?;
        let id = self.next_id_between(start.clone(), for_end);
        let _ = is_in;
        Ok(Token::new(id, InnerToken::T_ForIn { var, items, body }))
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
        let body = self.read_do_group(&start)?;
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
            let mut pats = Vec::new();
            while let Ok(w) = p.read_normal_word() {
                pats.push(w);
                p.spacing();
                if p.char('|').is_err() {
                    break;
                }
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
        self.input.get(i) == Some(&')')
    }

    /// `readWithoutFunction`: `name ( )` then a brace-group or subshell body.
    /// Both this and the `function` keyword form are one `called "function"`
    /// production in Haskell, so both name the function in SC1073/SC1009.
    pub(super) fn read_posix_function(&mut self) -> PResult<Token> {
        self.called("function", |p| p.read_posix_function_body())
    }

    fn read_posix_function_body(&mut self) -> PResult<Token> {
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

    pub(super) fn read_function_def(&mut self) -> PResult<Token> {
        self.called("function", |p| p.read_function_def_body())
    }

    fn read_function_def_body(&mut self) -> PResult<Token> {
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

    pub(super) fn read_function_name(&mut self) -> PResult<String> {
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
}
