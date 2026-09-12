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

    pub(super) fn is_word_boundary_after(&self, n: usize) -> bool {
        match self.peek_at(n) {
            None => true,
            Some(c) => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ';',
        }
    }

    /// True if the upcoming token is exactly `kw` followed by a word boundary.
    pub(super) fn keyword_ahead(&self, kw: &str) -> bool {
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

    pub(super) fn consume_keyword(&mut self, kw: &str) -> PResult<()> {
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
        let m = self.mark();
        self.spacing();
        if self.peek() == Some(';') && self.peek_at(1) != Some(';') {
            let pos = self.pos();
            self.bump();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                code,
                &format!("Semicolons directly after '{after}' are not allowed. Just remove it."),
            );
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

    pub(super) fn read_until_clause(&mut self) -> PResult<Token> {
        self.called("until loop", |p| p.read_until_clause_body())
    }

    fn read_until_clause_body(&mut self) -> PResult<Token> {
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
        self.allspacing();
        self.consume_keyword("do")?;
        let body = self.read_compound_list_or_empty();
        self.allspacing();
        self.consume_keyword("done")?;
        let id = self.next_id_between(start, sel_end);
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
