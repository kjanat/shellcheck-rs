//! Words: literals, quotes, globs, brace expansion and `$`-expansions (`ShellCheck.Parser` readNormalWord family).
use super::*;

impl Parser {
    // ---- words -------------------------------------------------------------

    /// `readNormalWord` = many1 word parts -> T_NormalWord
    pub(super) fn read_normal_word(&mut self) -> PResult<Token> {
        self.read_normalish_word(&["do", "done", "then", "fi", "esac"])
    }

    pub(super) fn read_normalish_word(&mut self, _terms: &[&str]) -> PResult<Token> {
        let start = self.pos();
        let mut parts = Vec::new();
        loop {
            let before = self.idx;
            match self.read_normal_word_part() {
                Ok(p) => parts.push(p),
                Err(()) => {
                    // `many1`: a part that failed after consuming input fails
                    // the whole word, so a trailing `\` is a parse error rather
                    // than a word that quietly ends early.
                    if self.idx != before {
                        return Err(());
                    }
                    break;
                }
            }
        }
        if parts.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_NormalWord(parts)))
    }

    pub(super) fn read_normal_word_part(&mut self) -> PResult<Token> {
        // Not ported: `checkForParenthesis`, which reports SC1036 for a `(`
        // that cannot start a word part. Haskell reaches it only after
        // `notFollowedBy2 (oneOf end)`, and this parser has no `end` set here,
        // so emitting it unconditionally fires on the `(` of a process
        // substitution — `read -ra arr <(ls)` and `ls >(cat)` — which the
        // oracle accepts. Needs the terminator set threaded through first.
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

    pub(super) fn read_single_quoted(&mut self) -> PResult<Token> {
        self.called("single quoted string", |p| p.read_single_quoted_body())
    }

    fn read_single_quoted_body(&mut self) -> PResult<Token> {
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
        let end = self.pos();
        if self.char('\'').is_err() {
            return self.fail_with("Expected end of single quoted string");
        }
        // A letter (or another quote) right after the closing quote: either the
        // apostrophe in `it's` ended the string, or a quote was left open.
        if let Some(c) = self.suspect_char_after_quotes().or(match self.peek() {
            Some('\'') => Some('\''),
            _ => None,
        }) {
            if s.chars().next_back().is_some_and(|l| l.is_alphabetic()) && c.is_alphabetic() {
                self.problem_at(
                    end.clone(),
                    end,
                    Severity::WarningC,
                    1011,
                    "This apostrophe terminated the single quoted string!",
                );
            } else if s.contains('\n') && !s.starts_with('\n') {
                self.suggest_forgot_closing_quote(&start, &end, "single quoted string");
            }
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_SingleQuoted(s)))
    }

    pub(super) fn read_double_quoted(&mut self) -> PResult<Token> {
        self.called("double quoted string", |p| p.read_double_quoted_body())
    }

    fn read_double_quoted_body(&mut self) -> PResult<Token> {
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
        let end = self.pos();
        if self.char('"').is_err() {
            return self.fail_with("Expected end of double quoted string");
        }
        if self.suspect_char_after_quotes().is_some() || matches!(self.peek(), Some('$' | '"')) {
            let literal = |t: &Token| match t.inner() {
                InnerToken::T_Literal(s) => Some(s.clone()),
                _ => None,
            };
            let has_line_feed = parts.iter().filter_map(literal).any(|s| s.contains('\n'));
            let starts_with_line_feed = parts
                .first()
                .and_then(literal)
                .is_some_and(|s| s.starts_with('\n'));
            if has_line_feed && !starts_with_line_feed {
                self.suggest_forgot_closing_quote(&start, &end, "double quoted string");
            }
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DoubleQuoted(parts)))
    }

    pub(super) fn read_double_literal_run(&mut self) -> PResult<Token> {
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

    pub(super) fn read_normal_literal(&mut self, custom_end: &str) -> PResult<Token> {
        let start = self.pos();
        let mut s = String::new();
        // standard end: "[{}" ++ quotableChars ++ extglobStartChars ++ unicode quotes.
        // Must include `'` so a mid-word single quote starts a T_SingleQuoted part
        // rather than being swallowed into the literal.
        let standard_end = "[{}|&;<>()\\ \t\n\r\u{A0}\"'$`?*@!+";
        let from = self.idx;
        loop {
            match self.peek() {
                Some('\\') => s.push_str(&self.read_normal_escaped()?),
                Some(c) if !custom_end.contains(c) && !standard_end.contains(c) => {
                    self.bump();
                    s.push(c);
                }
                _ => break,
            }
        }
        // `many1`, so what matters is that a part was read — a line
        // continuation is a part that stands for no text at all.
        if self.idx == from {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }

    /// `readNormalEscaped`: a backslash escape outside of quotes. Yields the
    /// literal text it stands for — empty for a line continuation, since the
    /// shell splices the lines together.
    pub(super) fn read_normal_escaped(&mut self) -> PResult<String> {
        self.called("escaped char", |p| p.read_normal_escaped_body())
    }

    fn read_normal_escaped_body(&mut self) -> PResult<String> {
        let pos = self.pos();
        self.char('\\')?;
        // `quotable <|> oneOf "?*@!+[]{}.,~#"`: escaping these is meaningful,
        // so there is nothing to report.
        if let Ok(c) = self.almost_space() {
            self.check_trailing_spaces(&pos);
            return Ok(c.to_string());
        }
        let next = self.peek().ok_or(())?;
        if QUOTABLE_CHARS.contains(next) || "?*@!+[]{}.,~#".contains(next) {
            self.bump();
            if next == ' ' {
                self.check_trailing_spaces(&pos);
            }
            return Ok(if next == '\n' {
                String::new()
            } else {
                next.to_string()
            });
        }
        // Anything else: the backslash is dropped and the character stands for
        // itself, which is rarely what was meant.
        self.bump();
        let (code, message) = match next {
            'n' | 't' | 'r' => {
                let name = match next {
                    'n' => "line feed",
                    't' => "tab",
                    _ => "carriage return",
                };
                let alternative = if next == 'n' {
                    "a quoted, literal line feed".to_string()
                } else {
                    format!("\"$(printf '\\{next}')\"")
                };
                (
                    1012,
                    format!(
                        "\\{next} is just literal '{next}' here. For {name}, use {alternative} instead."
                    ),
                )
            }
            _ => (
                1001,
                format!("This \\{next} will be a regular '{next}' in this context."),
            ),
        };
        let severity = if code == 1012 {
            Severity::WarningC
        } else {
            Severity::InfoC
        };
        self.note_at(pos.clone(), pos, severity, code, &message);
        Ok(next.to_string())
    }

    /// `checkTrailingSpaces`: `\` followed by nothing but blanks to the end of
    /// the line looks like a line continuation but is a literal space.
    fn check_trailing_spaces(&mut self, pos: &Position) {
        // Scanned by hand rather than through `line_whitespace`: Haskell does
        // this inside `lookAhead . try`, which rolls back the SC1018 notes a
        // unicode space would otherwise leave behind.
        let mut i = 0;
        while matches!(self.peek_at(i), Some(c) if c == ' ' || c == '\t' || ALMOST_SPACE_CHARS.contains(c))
        {
            i += 1;
        }
        let at_end = matches!(self.peek_at(i), None | Some('\n'));
        if at_end {
            self.problem_at(
                pos.clone(),
                pos.clone(),
                Severity::ErrorC,
                1101,
                "Delete trailing spaces after \\ to break line (or use quotes for literal space).",
            );
        }
    }

    pub(super) fn read_glob(&mut self) -> PResult<Token> {
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

    pub(super) fn read_glob_class(&mut self, start: Position) -> PResult<Token> {
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

    pub(super) fn read_brace_or_literal(&mut self) -> PResult<Token> {
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
            // `findParam`: `{}` is the find -exec placeholder and passes
            // without comment; a lone brace is flagged by `literalBraces`.
            if self.peek_at(1) == Some('}') {
                self.bump();
                self.bump();
                let id = self.next_id_between(start, self.pos());
                return Ok(Token::new(id, InnerToken::T_Literal("{}".to_string())));
            }
            self.literal_brace_problem('{', start.clone());
            self.bump();
            let id = self.next_id_between(start, self.pos());
            return Ok(Token::new(id, InnerToken::T_Literal("{".to_string())));
        }
        // bare '}'
        if self.peek() != Some('}') {
            return Err(());
        }
        self.literal_brace_problem('}', start.clone());
        self.bump();
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal("}".to_string())))
    }

    /// `literalBraces`: a curly brace that is not part of an expansion is
    /// taken literally, which is usually a missing `;` or a forgotten quote.
    fn literal_brace_problem(&mut self, c: char, pos: Position) {
        self.problem_at(
            pos.clone(),
            pos,
            Severity::WarningC,
            1083,
            &format!("This {c} is literal. Check expression (missing ;/\\n?) or quote it."),
        );
    }

    /// `readBraced = try braceExpansion` (Parser.hs). A brace expansion is
    /// `'{' (bracedElement `sepBy1` ',') '}'` guarded so it needs either >=2
    /// elements, or a single element whose literal string contains "..".
    /// Returns `Err` (leaving the input untouched) when it is not one.
    pub(super) fn read_braced(&mut self) -> PResult<Token> {
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
            1 => ast_lib::only_literal_string(&elements[0]).contains(".."),
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
    pub(super) fn read_braced_element(&mut self) -> Token {
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
    pub(super) fn read_brace_literal(&mut self) -> PResult<Token> {
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

    pub(super) fn read_proc_sub(&mut self) -> PResult<Token> {
        self.called("process substitution", |p| p.read_proc_sub_body())
    }

    fn read_proc_sub_body(&mut self) -> PResult<Token> {
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

    pub(super) fn read_extglob(&mut self) -> PResult<Token> {
        self.called("extglob", |p| p.read_extglob_body())
    }

    fn read_extglob_body(&mut self) -> PResult<Token> {
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

    pub(super) fn read_backticked(&mut self, quoted: bool) -> PResult<Token> {
        self.called("backtick expansion", |p| p.read_backticked_body(quoted))
    }

    fn read_backticked_body(&mut self, quoted: bool) -> PResult<Token> {
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
        let end = self.pos();
        if self.char('`').is_err() {
            // Haskell has no message here, but the failure is still a real one
            // rather than a backtracking point: `parsecBracket` re-fails a
            // `called` production with `fail ""`.
            return self.fail_with("");
        }
        if self.suspect_char_after_quotes().is_some()
            && raw.contains('\n')
            && !raw.starts_with('\n')
        {
            self.suggest_forgot_closing_quote(&start, &end, "backtick expansion");
        }
        // `unEscape`: process backtick escapes (`\$` `` \` `` `\\`, line splices,
        // and `\"`->`"` when inside double quotes) before sub-parsing.
        let unescaped = unescape_backtick(&raw, quoted);
        let cmds = self.subparse_commands(&unescaped, sub_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Backticked(cmds)))
    }

    // ---- dollar expansions -------------------------------------------------

    pub(super) fn read_normal_dollar(&mut self) -> PResult<Token> {
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

    pub(super) fn read_double_quoted_dollar(&mut self) -> PResult<Token> {
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

    pub(super) fn read_dollar_exp(&mut self) -> PResult<Token> {
        // arithmetic $((, expansion $(, bracket $[, braced ${, variable $x
        let m = self.mark();
        if self.string_peek("$((") {
            // `readAmbiguous "$((" readDollarArithmetic readDollarExpansion`.
            // Its last attempt consumes, so `readNormalDollar`'s bare `<|>` can
            // no longer fall back to a literal `$`.
            let r = self.read_ambiguous(
                |p| p.read_dollar_arithmetic(),
                |p| p.read_dollar_expansion(),
                |p, pos| {
                    p.note_at(
                        pos.clone(),
                        pos,
                        Severity::ErrorC,
                        1102,
                        "Shells disambiguate $(( differently or not at all. For $(command substitution), add space after $( . For $((arithmetics)), fix parsing errors.",
                    );
                },
            );
            if r.is_err() {
                self.committed = true;
            }
            return r;
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
            // Past `try (string "${")` there is no alternative left: a failure
            // here is the parse error, not a literal `$` and a stray brace.
            let r = self.read_dollar_braced();
            if r.is_err() {
                self.committed = true;
            }
            return r;
        }
        self.read_dollar_variable()
    }

    pub(super) fn read_dollar_arithmetic(&mut self) -> PResult<Token> {
        self.called("$((..)) expression", |p| p.read_dollar_arithmetic_body())
    }

    fn read_dollar_arithmetic_body(&mut self) -> PResult<Token> {
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

    pub(super) fn read_dollar_brace_command_expansion(&mut self) -> PResult<Token> {
        self.called("ksh-style ${ ..; } command expansion", |p| {
            p.read_dollar_brace_command_expansion_body()
        })
    }

    fn read_dollar_brace_command_expansion_body(&mut self) -> PResult<Token> {
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

    pub(super) fn read_dollar_bracket(&mut self) -> PResult<Token> {
        self.called("$[..] expression", |p| p.read_dollar_bracket_body())
    }

    fn read_dollar_bracket_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$[")?;
        let c = self.read_arithmetic_contents()?;
        self.string("]")?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarBracket(c)))
    }

    pub(super) fn read_dollar_expansion(&mut self) -> PResult<Token> {
        self.called("command expansion", |p| p.read_dollar_expansion_body())
    }

    fn read_dollar_expansion_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("$(")?;
        let sub_start = self.pos();
        let Ok(raw) = self.read_balanced_parens_until_close() else {
            return self.fail_with("Expected end of $(..) expression");
        };
        let cmds = self.subparse_commands(&raw, sub_start);
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarExpansion(cmds)))
    }

    pub(super) fn read_dollar_braced(&mut self) -> PResult<Token> {
        self.called("parameter expansion", |p| p.read_dollar_braced_body())
    }

    fn read_dollar_braced_body(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.string("${")?;
        // `readDollarBracedWord`: the contents are read as parts rather than
        // scanned for a matching brace, so an unterminated quote inside is the
        // parse error it is in the shell. A bare `{` is an ordinary literal
        // here (`readDollarBracedLiteral` stops only at `bracedQuotable`,
        // `}"$'` + backtick), and nesting comes only from a `${` part.
        let word_start = self.pos();
        let parts = self.read_braced_parts()?;
        let wid = self.next_id_between(word_start, self.pos());
        let inner = Token::new(wid, InnerToken::T_NormalWord(parts));
        self.char('}')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_DollarBraced {
                braced: true,
                op: inner,
            },
        ))
    }

    pub(super) fn read_dollar_variable(&mut self) -> PResult<Token> {
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

    pub(super) fn read_variable_name(&mut self) -> PResult<String> {
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

    pub(super) fn read_dollar_lonely(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('$')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal("$".to_string())))
    }

    pub(super) fn read_dollar_single_quote(&mut self) -> PResult<Token> {
        self.called("$'..' expression", |p| p.read_dollar_single_quote_body())
    }

    fn read_dollar_single_quote_body(&mut self) -> PResult<Token> {
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

    pub(super) fn read_dollar_double_quote(&mut self) -> PResult<Token> {
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
        if self.char('"').is_err() {
            return self.fail_with("Expected end of translated double quoted string");
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_DollarDoubleQuoted(parts)))
    }

    // ---- helpers for subexpressions ---------------------------------------

    pub(super) fn mark_at_start(&self, p: Position) -> Mark {
        // Reconstruct a Mark from a Position by scanning is expensive; instead we
        // never actually use this to move backward past consumed chars in a way
        // that matters. Return current mark (no-op safety).
        let _ = p;
        self.mark()
    }

    /// Parse the raw content of a `${...}` into a word whose parts include any
    /// nested expansions, single/double quotes and literal runs.
    /// `readDollarBracedWord`'s `many readDollarBracedPart`, read inline. Stops
    /// at the closing brace; a part that fails after consuming input (an
    /// unterminated quote, say) fails the whole expansion.
    pub(super) fn read_braced_parts(&mut self) -> PResult<Vec<Token>> {
        let mut parts = Vec::new();
        loop {
            let before = self.idx;
            let r = match self.peek() {
                None | Some('}') => break,
                Some('\'') => self.read_single_quoted(),
                Some('"') => self.read_double_quoted(),
                Some('`') => self.read_backticked(false),
                Some('$') => self.read_normal_dollar(),
                Some(_) => self.read_braced_literal(),
            };
            match r {
                Ok(t) => parts.push(t),
                Err(()) => {
                    if self.idx != before {
                        return Err(());
                    }
                    break;
                }
            }
        }
        Ok(parts)
    }

    /// `readDollarBracedLiteral`: a run of anything but `bracedQuotable`.
    fn read_braced_literal(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if "}$`'\"".contains(c) {
                break;
            }
            s.push(c);
            self.bump();
        }
        if s.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::T_Literal(s)))
    }

    pub(super) fn make_literal_word(&mut self, s: &str, start: Position) -> Token {
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

    pub(super) fn read_balanced_parens_until_close(&mut self) -> PResult<String> {
        // Consumes up to and including the matching ')', returning the raw
        // text between. Haskell instead parses the contents as commands and
        // then expects the ')', which means a quote inside swallows any ')'
        // it contains: `$(")` has no closing paren at all, because the `"`
        // runs to end of input. Counting parens has to respect quoting for
        // the same reason, or it stops at a ')' that is really quoted text.
        let mut raw = String::new();
        let mut depth = 1;
        let mut quote: Option<char> = None;
        while let Some(c) = self.peek() {
            match quote {
                // Inside '..' nothing is special but the closing quote.
                Some('\'') => {
                    if c == '\'' {
                        quote = None;
                    }
                }
                // Inside ".." a backslash still escapes the next character.
                Some('"') => {
                    if c == '\\' {
                        self.bump();
                        raw.push(c);
                        if let Some(n) = self.bump() {
                            raw.push(n);
                        }
                        continue;
                    }
                    if c == '"' {
                        quote = None;
                    }
                }
                _ => match c {
                    '\\' => {
                        self.bump();
                        raw.push(c);
                        if let Some(n) = self.bump() {
                            raw.push(n);
                        }
                        continue;
                    }
                    '\'' | '"' => quote = Some(c),
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                },
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
    pub(super) fn subparse_commands(&mut self, raw: &str, start: Position) -> Vec<Token> {
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
