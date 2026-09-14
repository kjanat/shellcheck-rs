//! Test conditions `[ .. ]` and `[[ .. ]]` (`ShellCheck.Parser.readCondition`).
use super::*;

impl Parser {
    /// `readConditionCommand`: a condition plus optional redirects, wrapped in
    /// T_Redirecting like every other command. Returns Err (with full reset)
    /// on any failure so the caller can fall back to a simple command.
    pub(super) fn read_condition_command(&mut self) -> PResult<Token> {
        let m = self.mark();
        let start = self.pos();
        let cond = match self.read_condition() {
            Ok(c) => c,
            Err(()) => {
                // As in `readCommand`'s `choice`: once the test expression has
                // consumed input there is no falling back to a simple command.
                if self.idx != m.idx {
                    self.commit();
                    return Err(());
                }
                self.reset(m);
                return Err(());
            }
        };
        let redirs = self.read_redirect_list()?;
        let id = self.next_id_between(start, self.pos());
        let pos = self.pos();
        let has_dash_ao = ["-o", "-a", "or", "and"]
            .into_iter()
            .find(|s| self.string_peek(s));
        if let Some(c) = has_dash_ao {
            let mut end = pos.clone();
            end.column += c.len() as i64;
            let alt = match c {
                "or" | "-o" => "||",
                _ => "&&",
            };
            self.problem_at(
                pos.clone(),
                end,
                Severity::ErrorC,
                1139,
                &format!("Use {alt} instead of '{c}' between test commands."),
            );
        }
        // A keyword here is reported by readNormalWord instead, and `-o`/`and`
        // already got SC1139; anything else is a stray parameter.
        // `isFollowedBy readKeyword`, and a `lookAhead` that succeeds replies
        // with an unknown error at its own position: the errors the keyword
        // attempts left -- `g_Else` reading the `e` of `esac` -- are given up
        // with it, so what the parse reports is the missing `)` after them.
        let keyword_failure = self.failure.clone();
        let has_keyword = self.keyword_len().is_some();
        if has_keyword {
            self.failure = keyword_failure;
        }
        // `isFollowedBy p = (lookAhead . try $ p $> True) <|> return False`: the
        // `try` catches a word that fails after consuming, so an unterminated
        // backtick after the condition is not a parse error here.
        let has_word = {
            let w = self.mark();
            let failure = self.failure.clone();
            let ok = self.try_parse(|p| p.read_normal_word().map(|_| ())).is_ok();
            if ok {
                // `lookAhead` replies with an unknown error at its own position
                // when `p` succeeds, which loses the merge against whatever
                // stood before: the failures the word ran into finding its
                // end -- past the `$` in `]]$ do` -- are not the furthest one.
                self.failure = failure;
            }
            self.reset(w);
            ok
        };
        if has_word && !has_keyword && has_dash_ao.is_none() {
            let pos_end = self.pos();
            self.problem_at(
                pos,
                pos_end,
                Severity::ErrorC,
                1140,
                "Unexpected parameters after condition. Missing &&/||, or bad expression?",
            );
        }
        Ok(Token::new(
            id,
            InnerToken::T_Redirecting { redirs, cmd: cond },
        ))
    }

    pub(super) fn read_condition(&mut self) -> PResult<Token> {
        self.called("test expression", |p| p.read_condition_body())
    }

    fn read_condition_body(&mut self) -> PResult<Token> {
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
        let space_pos = self.pos();
        let space = self.cond_spacing();
        if space.is_empty() {
            self.problem_at(
                start.clone(),
                space_pos.clone(),
                Severity::ErrorC,
                1035,
                if single {
                    "You need a space after the [ and before the ]."
                } else {
                    "You need a space after the [[ and before the ]]."
                },
            );
        }
        if single && space.contains('\n') {
            self.problem_at(
                space_pos.clone(),
                space_pos,
                Severity::ErrorC,
                1080,
                "You need \\ before line feeds to break lines in [ ].",
            );
        }

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

        let contents_start = self.mark();
        let contents = self.read_cond_contents(single).ok();
        if contents.is_none() && self.idx != contents_start.idx {
            // The contents committed before failing, so the `<|>` that would
            // have made this an empty condition is never reached.
            return Err(());
        }
        let token = match contents {
            Some(c) => c,
            None => {
                // `guard (not (null space)); lookAhead (string "]")`: an empty
                // condition is one whose closing bracket comes next. With
                // anything else there this alternative fails too, and so does
                // the whole `readCondition` -- the line that would have asked
                // for the bracket, message and all, is never reached.
                if space.is_empty() || self.peek() != Some(']') {
                    self.fail_implicitly();
                    return Err(());
                }
                let id = self.next_id_between(start.clone(), self.pos());
                Token::new(id, InnerToken::TC_Empty { typ })
            }
        };
        // `try (string "]]") <|> string "]"`: whichever bracket is actually
        // there, so a mismatched pair still parses and gets reported.
        let close_pos = self.pos();
        let close = if self.string("]]").is_ok() {
            "]]"
        } else if self.char(']').is_ok() {
            "]"
        } else {
            return self.fail_with("Expected test to end here (don't wrap commands in []/[[]])");
        };
        if dbl && close != "]]" {
            self.problem_at(
                close_pos.clone(),
                close_pos,
                Severity::ErrorC,
                1033,
                "Test expression was opened with double [[ but closed with single ]. Make sure they match.",
            );
        }
        if single && close != "]" {
            self.problem_at(
                start.clone(),
                start.clone(),
                Severity::ErrorC,
                1034,
                "Test expression was opened with single [ but closed with double ]]. Make sure they match.",
            );
        }
        let id = self.next_id_between(start, self.pos());
        // `endSpan` before the trailing `spacing`, so the span ends at the
        // closing bracket.
        self.spacing();
        Ok(Token::new(id, InnerToken::T_Condition { typ, token }))
    }

    /// `condSpacing`: spacing within a condition, where the shell needs it and
    /// where a bare line feed inside `[ ]` does not continue the expression.
    pub(super) fn cond_spacing_checked(&mut self, single: bool, required: bool) -> String {
        let pos = self.pos();
        let space = self.cond_spacing();
        if required && space.is_empty() {
            self.problem_at(
                pos.clone(),
                pos.clone(),
                Severity::ErrorC,
                1035,
                "You are missing a required space here.",
            );
        }
        if single && space.contains('\n') {
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1080,
                "When breaking lines in [ ], you need \\ before the linefeed.",
            );
        }
        space
    }

    /// Spacing within a condition: `condSpacing`'s `space <- allspacing`, so a
    /// comment counts as spacing here as it does anywhere else -- `[ -x# ]`
    /// has no argument for the `-x` rather than a word beginning with `#`.
    pub(super) fn cond_spacing(&mut self) -> String {
        self.allspacing()
    }

    // contents = or-level (chained by && / -a → TC_And)
    pub(super) fn read_cond_contents(&mut self, single: bool) -> PResult<Token> {
        self.read_cond_or(single)
    }

    pub(super) fn read_cond_or(&mut self, single: bool) -> PResult<Token> {
        let mut left = self.read_cond_and(single)?;
        loop {
            let m = self.mark();
            let op_start = self.pos();
            if let Some(op) = self.read_cond_and_op() {
                let op_end = self.pos();
                // `readAndOrOp .. requiresSpacing`: only the word forms need it.
                self.cond_spacing_checked(single, op.starts_with('-'));
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

    pub(super) fn read_cond_and(&mut self, single: bool) -> PResult<Token> {
        let mut left = self.read_cond_term(single)?;
        loop {
            let m = self.mark();
            let op_start = self.pos();
            // `readCondOrOp` opens with `optional guardArithmetic`.
            self.guard_arithmetic(single);
            if let Some(op) = self.read_cond_or_op() {
                let op_end = self.pos();
                self.cond_spacing_checked(single, op.starts_with('-'));
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

    pub(super) fn cond_typ(&self, single: bool) -> ConditionType {
        if single {
            ConditionType::SingleBracket
        } else {
            ConditionType::DoubleBracket
        }
    }

    pub(super) fn read_cond_and_op(&mut self) -> Option<String> {
        // && (both) or -a (word-bounded)
        if self.peek() == Some('&') && self.peek_at(1) == Some('&') {
            self.bump();
            self.bump();
            return Some("&&".to_string());
        }
        // `readAndOrOp node "-a" True` is `try $ string op`: no word boundary
        // is asked for, since `condSpacing True` is what reports a missing one
        // (SC1035) once the operator has been read.
        if self.string("-a").is_ok() {
            return Some("-a".to_string());
        }
        None
    }

    pub(super) fn read_cond_or_op(&mut self) -> Option<String> {
        if self.peek() == Some('|') && self.peek_at(1) == Some('|') {
            self.bump();
            self.bump();
            return Some("||".to_string());
        }
        if self.string("-o").is_ok() {
            return Some("-o".to_string());
        }
        None
    }

    pub(super) fn read_cond_term(&mut self, single: bool) -> PResult<Token> {
        // `readCondNot <|> readCondExpr`: a `!` is a negation, whatever
        // follows it -- `[ != x ]` is `!` with a missing space and then the
        // word `=`, which is what upstream reports (SC1035, then SC1108).
        let t = if self.peek() == Some('!') {
            self.read_cond_not(single)?
        } else {
            self.read_cond_expr(single)?
        };
        self.cond_spacing_checked(single, false);
        Ok(t)
    }

    pub(super) fn read_cond_not(&mut self, single: bool) -> PResult<Token> {
        let start = self.pos();
        self.char('!')?;
        // `readCondNot`: the TC_Unary id spans the `!` alone (`endSpan start`
        // immediately after `char '!'`), not the whole negated expression.
        let id = self.next_id_between(start, self.pos());
        self.cond_spacing_checked(single, true);
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

    pub(super) fn read_cond_expr(&mut self, single: bool) -> PResult<Token> {
        // `readCondGroup <|> readCondUnaryExp <|> readCondNullaryOrBinary`:
        // bare alternations, so an alternative that consumed before failing
        // leaves the others out of reach.
        let m = self.mark();
        match self.read_cond_group(single) {
            Ok(g) => return Ok(g),
            Err(()) => {
                if self.idx != m.idx {
                    return Err(());
                }
            }
        }
        match self.read_cond_unary(single) {
            Ok(u) => return Ok(u),
            Err(()) => {
                if self.idx != m.idx {
                    return Err(());
                }
            }
        }
        self.read_cond_nullary_or_binary(single)
    }

    pub(super) fn read_cond_group(&mut self, single: bool) -> PResult<Token> {
        let m = self.mark();
        let start = self.pos();
        // `readRegularOrEscaped (string "(")`: `\(`, `'('` and `"("` all read as
        // an escaped paren -- the quotes are a way of writing one without
        // reading a whole shell word -- and the wrong form for this bracket
        // type is reported rather than rejected.
        let lparen = if let Some(s) = self.read_cond_escaped_lit("(") {
            s
        } else if self.char('(').is_ok() {
            "(".to_string()
        } else {
            self.reset(m);
            return Err(());
        };
        self.warn_cond_paren(single, lparen == "(", &start);
        // Only the opening paren is inside the `try`: past it the contents and
        // the closing paren have consumed, so `[ \( ]` is a group with nothing
        // in it rather than a word that happens to look like one.
        self.cond_spacing_checked(single, single);
        let inner = self.read_cond_contents(single)?;
        let cpos = self.pos();
        let rparen = if let Some(s) = self.read_cond_escaped_lit(")") {
            s
        } else if self.char(')').is_ok() {
            ")".to_string()
        } else {
            return Err(());
        };
        self.cond_spacing_checked(single, single);
        self.warn_cond_paren(single, rparen == ")", &cpos);
        let typ = self.cond_typ(single);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::TC_Group { typ, token: inner }))
    }

    /// `readEscaped (string lit)`: the literal behind a backslash or inside a
    /// pair of quotes, with the backslash put back by `escaped`.
    fn read_cond_escaped_lit(&mut self, lit: &str) -> Option<String> {
        let m = self.mark();
        // `readEscaped` is a `try`: when it fails, its error merges with the one
        // standing before it rather than replacing it, so the quote it read
        // on the way must not take that one down -- for `[(z "` the message
        // the operator attempt left at the same position is what upstream
        // reports.
        let saved = self.failure.clone();
        match self.peek() {
            Some('\\') => {
                self.bump();
                if self.string(lit).is_ok() {
                    return Some(Self::escape_cond_op(lit));
                }
            }
            Some(q @ ('\'' | '"')) => {
                self.bump();
                if self.string(lit).is_ok() {
                    if self.peek() == Some(q) {
                        self.bump();
                        return Some(Self::escape_cond_op(lit));
                    }
                    self.fail_implicitly();
                }
            }
            _ => return None,
        }
        self.reset(m);
        self.restore_failure(saved);
        None
    }

    /// `singleWarning` / `doubleWarning`: `[ ]` needs the parens escaped and
    /// `[[ ]]` needs them bare.
    fn warn_cond_paren(&mut self, single: bool, bare: bool, pos: &Position) {
        let (code, msg) = if single && bare {
            (
                1028,
                "In [..] you have to escape \\( \\) or preferably combine [..] expressions.",
            )
        } else if !single && !bare {
            (1029, "In [[..]] you shouldn't escape ( or ).")
        } else {
            return;
        };
        self.problem_at(pos.clone(), pos.clone(), Severity::ErrorC, code, msg);
    }

    pub(super) fn read_cond_unary(&mut self, single: bool) -> PResult<Token> {
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
        // must be followed by spacing then a word. `spacingOrLf` reports the
        // missing space; the `try` that rewinds the operator does not take the
        // problem back with it.
        // `spacingOrLf` reports the missing space and carries on, so `-v=` is
        // still a unary operator with a bad argument rather than one long word.
        self.cond_spacing_checked(single, true);
        // `pos` is taken before `readCondWord`, so a missing argument is
        // reported where it should have been -- not wherever the attempt to
        // read one gave up.
        let arg_pos = self.pos();
        // `orFail = try parser <|> ..`: the attempt runs inside a `try`, so an
        // argument that fails *after consuming* (`[ -n $(`) rewinds like any
        // other -- commitment included. Without that, the point of no return
        // set inside the argument would silence the SC1019 below.
        match self.try_parse(|p| p.read_cond_word(single)) {
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
                self.problem_at(
                    arg_pos.clone(),
                    arg_pos,
                    Severity::ErrorC,
                    1019,
                    "Expected this to be an argument to the unary condition.",
                );
                self.fail_with("Expected an argument for the unary operator")
            }
        }
    }

    /// Read a `-` followed by letters (test operator), word-bounded.
    pub(super) fn read_cond_op_flag(&mut self) -> Option<String> {
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
            // `many1 letter <|> fail "Expected a test operator"`, from past the
            // dash. `readOp` is a `try`, so the failure is caught -- only its
            // message and position carry.
            let _: PResult<()> = self.fail_recoverable("Expected a test operator");
            self.reset(m);
            return None;
        }
        Some(s)
    }

    pub(super) fn read_cond_nullary_or_binary(&mut self, single: bool) -> PResult<Token> {
        let start = self.pos();
        // `attempting`: the branch runs first, so a `[` where an operand
        // belongs is flagged as a grouping attempt with the wrong brackets
        // whether or not the word itself reads.
        if self.peek() == Some('[') {
            let pos = self.pos();
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1026,
                if single {
                    "If grouping expressions inside [..], use \\( ..\\)."
                } else {
                    "If grouping expressions inside [[..]], use ( .. )."
                },
            );
        }
        let x = self.read_cond_word(single)?;
        // try binary op
        let m = self.mark();
        let op_start = self.pos();
        // `regexOperatorAhead`: a lookahead (non-consuming) for `=~`/`~=`. When
        // true the RHS is read as a regex rather than a normal condition word.
        let is_regex = self.regex_operator_ahead();
        if let Some((op, op_end)) = self.read_cond_binary_op(single) {
            // TC_Binary inherits the operator token's span (ShellCheck's
            // `getOp`: `startSpan .. endSpan`), so checks emit on the operator.
            let ym = self.mark();
            let y = if is_regex {
                self.read_regex()
            } else {
                self.read_cond_word(single)
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
                    // The operand consumed before failing, so neither the
                    // `<|>` that reports SC1027 nor the one that would fall
                    // back to a nullary expression can recover.
                    if self.idx != ym.idx {
                        return Err(());
                    }
                    if !is_regex {
                        // The operator was there, so there is no falling back to
                        // a nullary expression: what is missing is its argument.
                        self.problem_at(
                            op_start.clone(),
                            op_start,
                            Severity::ErrorC,
                            1027,
                            "Expected another argument for this operator.",
                        );
                        return Err(());
                    }
                    self.reset(m);
                }
            }
        } else {
            self.reset(m);
        }
        // `checkTrailingOp`: a word ending in a test operator ran into it.
        if let Some(lit) = ast_lib::get_trailing_unquoted_literal(&x) {
            if let InnerToken::T_Literal(s) = lit.inner() {
                if let Some(op) = crate::data::BINARY_TEST_OPS
                    .iter()
                    .find(|o| s.ends_with(**o))
                {
                    let (ls, le) = self.span_for(lit.id());
                    self.problem_at(
                        ls,
                        le,
                        Severity::ErrorC,
                        1108,
                        &format!("You need a space before and after the {op} ."),
                    );
                }
            }
        }
        let typ = self.cond_typ(single);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::TC_Nullary { typ, token: x }))
    }

    /// `regexOperatorAhead`: lookahead for `=~` (or the quirky `~=`) without
    /// consuming input.
    pub(super) fn regex_operator_ahead(&self) -> bool {
        self.string_peek("=~") || self.string_peek("~=")
    }

    /// `guardArithmetic`: an arithmetic operator where a test operand belongs.
    /// A `lookAhead`, so it only reports.
    fn guard_arithmetic(&mut self, single: bool) {
        let ahead = match self.peek() {
            Some(c) if "+*/%".contains(c) => true,
            Some('-') => self.peek_at(1) == Some(' '),
            _ => false,
        };
        if !ahead {
            return;
        }
        let pos = self.pos();
        self.problem_at(
            pos.clone(),
            pos,
            Severity::ErrorC,
            1076,
            if single {
                "Trying to do math? Use e.g. [ $((i/2+7)) -ge 18 ]."
            } else {
                "Trying to do math? Use e.g. [[ $((i/2+7)) -ge 18 ]]."
            },
        );
    }

    /// `readCondBinaryOp`: `readRegularOrEscaped anyOp`, then trailing spacing.
    /// Returns the operator string (with a leading `\` re-added for
    /// escaped/quoted `<`/`>`/`(`/`)`, matching `escaped`) and the position just
    /// after the operator (before spacing), used for the TC_Binary span.
    pub(super) fn read_cond_binary_op(&mut self, single: bool) -> Option<(String, Position)> {
        let m = self.mark();
        // `optional guardArithmetic`
        self.guard_arithmetic(single);
        // readEscaped anyOp  (\op  or  'op' / "op")
        if let Some(op) = self.read_cond_escaped_op() {
            let end = self.pos();
            self.cond_spacing_checked(single, true);
            return Some((op, end));
        }
        self.reset(m);
        // plain anyOp
        if let Some(op) = self.read_cond_any_op() {
            let end = self.pos();
            self.cond_spacing_checked(single, true);
            return Some((op, end));
        }
        self.reset(m);
        None
    }

    /// `anyOp = flagOp <|> flaglessOp`. flagOp is a `-`+letters test operator
    /// that is not `-a`/`-o`; flaglessOp is one of the symbolic comparisons.
    pub(super) fn read_cond_any_op(&mut self) -> Option<String> {
        let m = self.mark();
        if let Some(o) = self.read_cond_op_flag() {
            if o != "-a" && o != "-o" {
                return Some(o);
            }
            // `when (s == "-a" || s == "-o") $ fail "Unexpected operator"`,
            // inside `flagOp`'s own `try`: the cursor comes back, but the
            // message stays where the operator ended.
            let _: PResult<()> = self.fail_recoverable("Unexpected operator");
        }
        self.reset(m);
        // flaglessOps, longest first
        for op in ["==", "!=", "<=", ">=", "=~", ">", "<", "="] {
            if self.string_peek(op) {
                self.string(op).ok();
                return Some(op.to_string());
            }
        }
        // `anyOp = flagOp <|> flaglessOp <|> fail ..`: the message is recorded
        // wherever the operator was expected -- inside the quotes of a
        // `readEscaped` attempt, that is past the opening quote.
        let _: PResult<()> =
            self.fail_recoverable("Expected comparison operator (don't wrap commands in []/[[]])");
        None
    }

    /// `readEscaped anyOp`: `\op` or a quote-wrapped `'op'` / `"op"`. Per
    /// ShellCheck's `escaped`, if the operator contains any of `<>()` a leading
    /// backslash is re-added to the returned string.
    pub(super) fn read_cond_escaped_op(&mut self) -> Option<String> {
        let m = self.mark();
        // A `try`, as `read_cond_escaped_lit` is: what stood before it merges
        // with what it leaves.
        let saved = self.failure.clone();
        match self.peek() {
            Some('\\') => {
                self.bump();
                if let Some(s) = self.read_cond_any_op() {
                    return Some(Self::escape_cond_op(&s));
                }
            }
            Some(q @ ('\'' | '"')) => {
                self.bump();
                if let Some(s) = self.read_cond_any_op() {
                    if self.peek() == Some(q) {
                        self.bump();
                        return Some(Self::escape_cond_op(&s));
                    }
                    // `char c` on something else: `readEscaped` is a `try`, so
                    // the cursor comes back, but the error was recorded past
                    // the operator -- for `[x '>` the end of the input, and
                    // the furthest the parse ever gets.
                    self.fail_implicitly();
                }
            }
            _ => return None,
        }
        self.reset(m);
        self.restore_failure(saved);
        None
    }

    pub(super) fn escape_cond_op(s: &str) -> String {
        if s.chars().any(|c| "<>()".contains(c)) {
            format!("\\{}", s)
        } else {
            s.to_string()
        }
    }

    pub(super) fn string_peek(&self, s: &str) -> bool {
        for (i, c) in s.chars().enumerate() {
            if self.peek_at(i) != Some(c) {
                return false;
            }
        }
        true
    }

    /// A condition word: a normal word, not the closing bracket. Stops at
    /// whitespace/operators/brackets like the normal word reader.
    pub(super) fn read_cond_word(&mut self, single: bool) -> PResult<Token> {
        // `notFollowedBy2 (try (spacing >> string "]"))`: the closing bracket is
        // not a word. The error is recorded from past it, where the `fail`
        // inside the lookahead happens.
        {
            let m = self.mark();
            self.spacing();
            if self.char(']').is_ok() {
                let r = self.fail_recoverable("Unexpected ");
                self.reset(m);
                return r;
            }
            self.reset(m);
        }
        let w = self.read_normal_word()?;
        let pos = self.pos();
        // A word ending in the closing bracket swallowed it, unless it is an
        // array index (`$x[1]`) — which starts with a literal `[`.
        let tail = match w.inner() {
            InnerToken::T_NormalWord(parts) => match parts.last().map(Token::inner) {
                Some(InnerToken::T_Literal(s)) => s.clone(),
                _ => String::new(),
            },
            _ => String::new(),
        };
        let is_array_index = match w.inner() {
            InnerToken::T_NormalWord(parts) => {
                matches!(parts.get(1).map(Token::inner), Some(InnerToken::T_Literal(t)) if t == "[")
            }
            _ => false,
        };
        let contains_open_bracket = match w.inner() {
            InnerToken::T_NormalWord(parts) => parts
                .iter()
                .any(|p| matches!(p.inner(), InnerToken::T_Literal(s) if s.contains('['))),
            _ => false,
        };
        if !is_array_index && tail.ends_with(']') && !contains_open_bracket {
            let bracket = if single { "]" } else { "]]" };
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1020,
                &format!("You need a space before the {bracket}."),
            );
            return self.fail_with("Missing space before ]");
        }
        if single && tail.ends_with(')') {
            self.problem_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1021,
                "You need a space before the \\)",
            );
            return self.fail_with("Missing space before )");
        }
        self.cond_spacing_line();
        Ok(w)
    }

    /// Line-spacing only (used after a cond word so we don't cross newlines
    /// unexpectedly in `[ ]`).
    pub(super) fn cond_spacing_line(&mut self) {
        while self.line_whitespace().is_ok() {}
    }

    /// `readRegex`: the RHS of `=~`. `many1 readPart`, then trailing spacing.
    /// The parts absorb regex syntax (groups, glob chars, `|`) so that an
    /// unquoted `]]`/`)` inside a `( .. )` group does not terminate the
    /// condition, while unquoted whitespace outside a group ends the regex.
    pub(super) fn read_regex(&mut self) -> PResult<Token> {
        self.called("regex", |p| p.read_regex_body())
    }

    fn read_regex_body(&mut self) -> PResult<Token> {
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
                // `many1 readPart`: a part that failed having consumed takes
                // the whole regex down, so an unterminated group or quote
                // inside it is the failure reported rather than the condition
                // complaining that the test did not end here.
                Err(()) if self.idx != before => return Err(()),
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
    pub(super) fn read_regex_part(&mut self) -> PResult<Token> {
        match self.peek() {
            Some('(') => return self.read_regex_group(),
            Some('\'') => return self.read_single_quoted(),
            Some('"') => return self.read_double_quoted(),
            Some('$') => {
                // `readDollarExpression`, not `readNormalDollar`: there is no
                // `$'..'`, `$".."` or lone `$` among its alternatives, so in a
                // regex `$"e"` is the glob literal `$` and then a double quoted
                // string, with the diagnostics a double quoted string gets.
                let m = self.mark();
                match self.read_dollar_exp() {
                    Ok(t) => return Ok(t),
                    Err(()) if self.idx != m.idx => return Err(()),
                    Err(()) => self.reset(m),
                }
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
    pub(super) fn read_literal_for_parser_normal(&mut self, custom_end: &str) -> PResult<Token> {
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
    pub(super) fn read_regex_group(&mut self) -> PResult<Token> {
        self.called("regex grouping", |p| p.read_regex_group_body())
    }

    fn read_regex_group_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        let p1_start = self.pos();
        self.char('(')?;
        let p1 = Token::new(
            self.next_id_between(p1_start, self.pos()),
            InnerToken::T_Literal("(".to_string()),
        );
        let mut parts = vec![p1];
        // `many (readPart <|> readRegexLiteral)`: neither `<|>` nor `many`
        // recovers from an alternative that consumed before failing.
        loop {
            let m = self.mark();
            let before = self.idx;
            match self.read_regex_part() {
                Ok(p) if self.idx != before => {
                    parts.push(p);
                    continue;
                }
                Ok(_) => self.reset(m),
                Err(()) if self.idx != before => return Err(()),
                Err(()) => self.reset(m),
            }
            match self.read_regex_literal() {
                Ok(p) => {
                    parts.push(p);
                    continue;
                }
                Err(()) if self.idx != before => return Err(()),
                Err(()) => break,
            }
        }
        if self.peek() != Some(')') {
            // `p2 <- readLiteralString ")"`: a `string` that does not match
            // records an error where it stood, and here that is the furthest
            // the regex ever reached.
            self.fail_implicitly();
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

    /// `readRegexLiteral = readGenericLiteral1 (singleQuote <|> doubleQuotable
    /// <|> oneOf "()")`, and `doubleQuotable` is one of `\"$` and the
    /// backtick -- the backslash included, so `readGenericEscaped` is never
    /// reached and an escape is left for `readPart`'s normal literal.
    pub(super) fn read_regex_literal(&mut self) -> PResult<Token> {
        const END: &str = "'\\\"$`()";
        let start = self.pos();
        // `reluctantlyTill1` begins with `notFollowedBy2 end`, and `unexpecting`
        // runs `try end` -- which reads the character it matches -- before it
        // fails, all inside another `try`: on one of its own terminators the
        // literal fails one past it, with "Unexpected " as the message, and
        // the cursor comes back so the group can go on to its `)`.
        if let Some(c) = self.peek() {
            if END.contains(c) {
                self.fail_past(1, "Unexpected ");
                return Err(());
            }
        }
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if END.contains(c) {
                break;
            }
            self.bump();
            s.push(c);
        }
        if s.is_empty() {
            // `anyChar` at the end of the input.
            self.fail_implicitly();
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }
}
