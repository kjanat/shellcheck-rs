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
    pub(super) fn cond_spacing(&mut self) -> String {
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

    pub(super) fn read_cond_and(&mut self, single: bool) -> PResult<Token> {
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
        if self.keyword_dash("-a") {
            self.string("-a").ok();
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
        if self.keyword_dash("-o") {
            self.string("-o").ok();
            return Some("-o".to_string());
        }
        None
    }

    /// A `-x` operator token that is word-bounded (followed by whitespace).
    pub(super) fn keyword_dash(&self, s: &str) -> bool {
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

    pub(super) fn read_cond_term(&mut self, single: bool) -> PResult<Token> {
        let t = if self.peek() == Some('!') && self.peek_at(1) != Some('=') {
            self.read_cond_not(single)?
        } else {
            self.read_cond_expr(single)?
        };
        self.cond_spacing();
        Ok(t)
    }

    pub(super) fn read_cond_not(&mut self, single: bool) -> PResult<Token> {
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

    pub(super) fn read_cond_expr(&mut self, single: bool) -> PResult<Token> {
        if let Ok(g) = self.read_cond_group(single) {
            return Ok(g);
        }
        if let Ok(u) = self.read_cond_unary(single) {
            return Ok(u);
        }
        self.read_cond_nullary_or_binary(single)
    }

    pub(super) fn read_cond_group(&mut self, single: bool) -> PResult<Token> {
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
            self.reset(m);
            return None;
        }
        Some(s)
    }

    pub(super) fn read_cond_nullary_or_binary(&mut self, single: bool) -> PResult<Token> {
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
    pub(super) fn regex_operator_ahead(&self) -> bool {
        self.string_peek("=~") || self.string_peek("~=")
    }

    /// `readCondBinaryOp`: `readRegularOrEscaped anyOp`, then trailing spacing.
    /// Returns the operator string (with a leading `\` re-added for escaped/quoted
    /// `<`/`>`/`(`/`)`, matching `escaped`) and the position just after the
    /// operator (before spacing), used for the TC_Binary span.
    pub(super) fn read_cond_binary_op(&mut self) -> Option<(String, Position)> {
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
    pub(super) fn read_cond_any_op(&mut self) -> Option<String> {
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
    pub(super) fn read_cond_escaped_op(&mut self) -> Option<String> {
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
    pub(super) fn read_cond_word(&mut self) -> PResult<Token> {
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
    pub(super) fn read_regex_literal(&mut self) -> PResult<Token> {
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
