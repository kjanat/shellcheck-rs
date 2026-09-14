//! ShellCheck directive annotations (`# shellcheck ...`).
use super::*;

impl Parser {
    /// `readAnnotations`: zero or more `# shellcheck ...` directive lines.
    pub(super) fn read_annotations(&mut self) -> Vec<Annotation> {
        let mut out = Vec::new();
        loop {
            let m = self.mark();
            match self.read_annotation() {
                Ok(mut anns) => {
                    out.append(&mut anns);
                    self.allspacing();
                }
                Err(()) => {
                    // `many` stops on a failure that consumed nothing; a
                    // malformed directive has consumed its prefix, and nothing
                    // above can recover from that.
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

    /// A single `# shellcheck <keys>` directive. A line that is not one fails
    /// without consuming; one that is, but is malformed, is a parse error.
    pub(super) fn read_annotation(&mut self) -> PResult<Vec<Annotation>> {
        self.called("shellcheck directive", |p| p.read_annotation_body())
    }

    fn read_annotation_body(&mut self) -> PResult<Vec<Annotation>> {
        // `try readAnnotationPrefix`
        let m = self.mark();
        if self.char('#').is_err() {
            self.reset(m);
            return Err(());
        }
        while self.line_whitespace().is_ok() {}
        if self.string("shellcheck").is_err() {
            self.reset(m);
            return Err(());
        }
        // `many1 linewhitespace`, outside the `try`: past the prefix this is a
        // directive, so `# shellcheckfoo` is a broken one rather than a comment.
        self.line_whitespace()?;
        while self.line_whitespace().is_ok() {}
        self.read_annotation_keys()
    }

    fn read_annotation_keys(&mut self) -> PResult<Vec<Annotation>> {
        let mut out = Vec::new();
        // `many1 readKey` counts keys, not annotations: a key whose value
        // parses to nothing (`disable=`) is still a key.
        let mut keys = 0;
        // `many1 readKey`
        loop {
            if matches!(self.peek(), None | Some('\n') | Some('\r')) {
                break;
            }
            let key_pos = self.pos();
            let key = self.read_annotation_key_name();
            if key.is_empty() {
                break;
            }
            if self.char('=').is_err() {
                return self.fail_with("Expected '=' after directive key");
            }
            let mut anns = self.read_annotation_value(&key, key_pos)?;
            keys += 1;
            out.append(&mut anns);
            while self.line_whitespace().is_ok() {}
        }
        if keys == 0 {
            // `many1` needs one key; `# shellcheck` alone has none.
            return self.fail_with("");
        }
        // `optional readAnyComment`, which comes *after* `many1 readKey`: a
        // directive with no keys at all fails where the comment starts, not
        // past it.
        let _ = self.read_any_comment();
        // `void linefeed <|> eof <|> do { SC1125; many (noneOf "\n"); .. }`:
        // anything left on the line was not a key=value pair.
        if !self.eof() && self.peek() != Some('\n') && self.peek() != Some('\r') {
            let pos = self.pos();
            self.note_at(
                pos.clone(),
                pos,
                Severity::ErrorC,
                1125,
                "Invalid key=value pair? Ignoring the rest of this directive starting here.",
            );
            while matches!(self.peek(), Some(c) if c != '\n') {
                self.bump();
            }
        }
        // consume trailing newline
        let _ = self.carriage_return();
        let _ = self.char('\n');
        while self.line_whitespace().is_ok() {}
        Ok(out)
    }

    /// `many1 (letter <|> char '-')`, and Parsec's `letter` is `isAlpha`.
    pub(super) fn read_annotation_key_name(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphabetic() || c == '-' {
                self.bump();
                s.push(c);
            } else {
                break;
            }
        }
        s
    }

    /// `quoted (many1 anyChar) <|> (many1 $ noneOf " \n")`: the value of
    /// `source=`, `source-path=` and `shell=`. Past an opening quote both of
    /// `quoted`'s failures have consumed; unquoted, an empty value is a
    /// failure at the character that ended it, and the key it belongs to has
    /// consumed -- `shell= d` is a broken directive, not a `shell=` and a `d`.
    fn read_directive_word(&mut self) -> PResult<String> {
        if let Some(q) = self.peek() {
            if q == '\'' || q == '"' {
                self.bump();
                let mut s = String::new();
                while let Some(c) = self.peek() {
                    if c == q || c == '\n' {
                        break;
                    }
                    s.push(c);
                    self.bump();
                }
                if s.is_empty() {
                    // `many1 $ noneOf (c:"\n")` with nothing to take.
                    self.fail_implicitly();
                    return Err(());
                }
                if self.char(q).is_err() {
                    return self.fail_with("Missing terminating quote for directive.");
                }
                return Ok(s);
            }
        }
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == ' ' || c == '\n' {
                break;
            }
            s.push(c);
            self.bump();
        }
        if s.is_empty() {
            self.fail_implicitly();
            return Err(());
        }
        Ok(s)
    }

    /// `many1 letter`.
    fn read_letters1(&mut self) -> PResult<String> {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if !c.is_alphabetic() {
                break;
            }
            s.push(c);
            self.bump();
        }
        if s.is_empty() {
            self.fail_implicitly();
            return Err(());
        }
        Ok(s)
    }

    /// `"enable" -> plainOrQuoted $ readName `sepBy` char ','` with `readName =
    /// EnableComment <$> many1 (letter <|> char '-')`: `sepBy` takes none at
    /// all, but once a comma has been read the name after it is required.
    fn read_enable_names(&mut self) -> PResult<Vec<Annotation>> {
        let mut out = Vec::new();
        let Ok(first) = self.read_enable_name() else {
            return Ok(out);
        };
        out.push(Annotation::EnableComment(first));
        while self.char(',').is_ok() {
            out.push(Annotation::EnableComment(self.read_enable_name()?));
        }
        Ok(out)
    }

    fn read_enable_name(&mut self) -> PResult<String> {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if !(c.is_alphabetic() || c == '-') {
                break;
            }
            s.push(c);
            self.bump();
        }
        if s.is_empty() {
            self.fail_implicitly();
            return Err(());
        }
        Ok(s)
    }

    /// `"disable" -> plainOrQuoted $ readElement `sepBy` char ','`, parsed
    /// rather than split: a malformed element is a parse failure at a precise
    /// position, and what it leaves unread is what SC1125 reports.
    fn read_disable_value(&mut self) -> PResult<Vec<Annotation>> {
        self.plain_or_quoted(|p| p.read_disable_elements())
    }

    fn read_disable_elements(&mut self) -> PResult<Vec<Annotation>> {
        let mut out = Vec::new();
        let m = self.mark();
        match self.read_disable_element() {
            Ok(a) => out.push(a),
            Err(()) => {
                // `sepBy` allows none at all, but only if the first attempt
                // consumed nothing.
                if self.idx != m.idx {
                    return Err(());
                }
                self.reset(m);
                return Ok(out);
            }
        }
        while self.char(',').is_ok() {
            out.push(self.read_disable_element()?);
        }
        Ok(out)
    }

    /// `readElement = readRange <|> readAll`
    fn read_disable_element(&mut self) -> PResult<Annotation> {
        let m = self.mark();
        match self.read_disable_range() {
            Ok(a) => return Ok(a),
            Err(()) => {
                if self.idx != m.idx {
                    return Err(());
                }
            }
        }
        // `readAll = do { string "all"; .. }`, a bare `string`: a partial match
        // has consumed and `readRange <|> readAll` cannot recover from it.
        self.string_tokens("all")?;
        Ok(Annotation::DisableComment(0, 1_000_000))
    }

    /// `readRange`: a code, optionally `-` and another; a lone code covers
    /// itself alone.
    fn read_disable_range(&mut self) -> PResult<Annotation> {
        let from = self.read_disable_code()?;
        let m = self.mark();
        let to = if self.char('-').is_ok() {
            self.read_disable_code()?
        } else {
            self.reset(m);
            from + 1
        };
        Ok(Annotation::DisableComment(from, to))
    }

    /// `readCode = optional (string "SC") >> many1 digit`. Parsec's `string`
    /// consumes what matched before failing, so a lone `S` takes the whole
    /// directive down -- while reporting at the `S`, where the string began.
    fn read_disable_code(&mut self) -> PResult<i64> {
        if self.peek() == Some('S') {
            let start = self.mark();
            self.bump();
            if self.peek() != Some('C') {
                let consumed = self.mark();
                self.reset(start);
                self.fail_implicitly();
                self.reset(consumed);
                return Err(());
            }
            self.bump();
        }
        let m = self.mark();
        let mut s = String::new();
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            s.push(self.bump().unwrap());
        }
        if s.is_empty() {
            self.reset(m);
            self.fail_implicitly();
            return Err(());
        }
        s.parse().map_err(|_| ())
    }

    /// `plainOrQuoted p = quoted p <|> p`: the value may be wrapped in quotes,
    /// in which case `p` runs on what is inside them.
    fn plain_or_quoted<T>(&mut self, p: impl Fn(&mut Self) -> PResult<T>) -> PResult<T> {
        if let Some(q) = self.peek() {
            if q == '\'' || q == '"' {
                self.bump();
                let start = self.pos();
                let mut inner = String::new();
                while let Some(c) = self.peek() {
                    if c == q || c == '\n' {
                        break;
                    }
                    inner.push(c);
                    self.bump();
                }
                // Past the opening quote both of these have consumed, so the
                // `<|>` in `plainOrQuoted` cannot fall back to the unquoted
                // reading: an unterminated quote is a parse error, which is
                // what the wiki's SC1072 page describes for an incomplete
                // directive.
                if inner.is_empty() {
                    // `many1 $ noneOf (c:"\n")` with nothing to take.
                    self.fail_implicitly();
                    return Err(());
                }
                if self.char(q).is_err() {
                    return self.fail_with("Missing terminating quote for directive.");
                }
                {
                    let mut sub = self.sub_parser(&inner, &start);
                    let r = p(&mut sub);
                    let (contexts, failure) = (sub.contexts.clone(), sub.failure.clone());
                    self.merge_sub(sub);
                    if r.is_err() {
                        self.contexts = contexts;
                        self.failure = failure;
                    }
                    return r;
                }
            }
        }
        p(self)
    }

    pub(super) fn read_annotation_value(
        &mut self,
        key: &str,
        key_pos: Position,
    ) -> PResult<Vec<Annotation>> {
        Ok(match key {
            "disable" => return self.read_disable_value(),
            "enable" => self.plain_or_quoted(|p| p.read_enable_names())?,
            "source" => vec![Annotation::SourceOverride(self.read_directive_word()?)],
            "source-path" => vec![Annotation::SourcePath(self.read_directive_word()?)],
            "shell" => {
                let pos = self.pos();
                let v = self.read_directive_word()?;
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
                let pos = self.pos();
                let v = self.plain_or_quoted(|p| p.read_letters1())?;
                match v.as_str() {
                    "true" => vec![Annotation::ExtendedAnalysis(true)],
                    "false" => vec![Annotation::ExtendedAnalysis(false)],
                    _ => {
                        self.note_at(
                            pos.clone(),
                            pos,
                            Severity::ErrorC,
                            1146,
                            "Unknown extended-analysis value. Expected true/false.",
                        );
                        Vec::new()
                    }
                }
            }
            "external-sources" => {
                let pos = self.pos();
                let v = self.plain_or_quoted(|p| p.read_letters1())?;
                match v.as_str() {
                    // `readAnnotationWithoutPrefix sandboxed`: this path is the
                    // sandboxed one (a script), where enabling external sources
                    // is refused. The rc-file parser (`shellcheck_cli::rc`) is
                    // the unsandboxed caller and allows it.
                    "true" => {
                        self.note_at(
                            pos.clone(),
                            pos,
                            Severity::ErrorC,
                            1144,
                            "external-sources can only be enabled in .shellcheckrc, not in individual files.",
                        );
                        Vec::new()
                    }
                    "false" => vec![Annotation::ExternalSources(false)],
                    _ => {
                        self.note_at(
                            pos.clone(),
                            pos,
                            Severity::ErrorC,
                            1145,
                            "Unknown external-sources value. Expected true/false.",
                        );
                        Vec::new()
                    }
                }
            }
            _ => {
                self.note_at(
                    key_pos.clone(),
                    key_pos,
                    Severity::WarningC,
                    1107,
                    "This directive is unknown. It will be ignored.",
                );
                // `anyChar `reluctantlyTill` whitespace`
                while let Some(c) = self.peek() {
                    if c == ' '
                        || c == '\t'
                        || c == '\r'
                        || c == '\n'
                        || ALMOST_SPACE_CHARS.contains(c)
                    {
                        break;
                    }
                    self.bump();
                }
                Vec::new()
            }
        })
    }
}
