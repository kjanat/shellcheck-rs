//! ShellCheck directive annotations (`# shellcheck ...`).
use super::*;

impl Parser {
    /// `readAnnotations`: zero or more `# shellcheck ...` directive lines.
    pub(super) fn read_annotations(&mut self) -> Vec<Annotation> {
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
    pub(super) fn read_annotation(&mut self) -> Option<Vec<Annotation>> {
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

    pub(super) fn read_annotation_keys(&mut self) -> Vec<Annotation> {
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
            let key_pos = self.pos();
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
            let mut anns = self.read_annotation_value(&key, key_pos);
            out.append(&mut anns);
            while self.line_whitespace().is_ok() {}
        }
        // consume trailing newline
        let _ = self.char('\r');
        let _ = self.char('\n');
        out
    }

    pub(super) fn read_annotation_key_name(&mut self) -> String {
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
    pub(super) fn read_annotation_raw_value(&mut self) -> String {
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

    pub(super) fn read_annotation_value(
        &mut self,
        key: &str,
        key_pos: Position,
    ) -> Vec<Annotation> {
        match key {
            "disable" => {
                let raw = self.read_annotation_raw_value();
                raw.split(',').filter_map(parse_disable_element).collect()
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
                let _ = self.read_annotation_raw_value();
                self.note_at(
                    key_pos.clone(),
                    key_pos,
                    Severity::WarningC,
                    1107,
                    "This directive is unknown. It will be ignored.",
                );
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
