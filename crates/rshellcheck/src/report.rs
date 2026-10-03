use std::io::Write;

use clap::ValueEnum;

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Format {
    Checkstyle,
    Diff,
    Gcc,
    Json,
    Json1,
    Tty,
    Quiet,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    Error,
    Warning,
    Info,
    Style,
}

impl Level {
    pub fn from_index(index: i64) -> Self {
        match index {
            0 => Level::Error,
            1 => Level::Warning,
            2 => Level::Info,
            _ => Level::Style,
        }
    }

    fn text(self) -> &'static str {
        match self {
            Level::Error => "error",
            Level::Warning => "warning",
            Level::Info => "info",
            Level::Style => "style",
        }
    }
}

pub struct Span {
    pub line: i64,
    pub column: i64,
    pub end_line: i64,
    pub end_column: i64,
}

pub struct Edit {
    pub span: Span,
    pub after_end: bool,
    pub precedence: i64,
    pub replacement: String,
}

pub struct Comment {
    pub level: Level,
    pub code: i64,
    pub message: String,
    pub expanded: Span,
    pub real: Span,
    pub expanded_fix: Option<Vec<Edit>>,
    pub real_fix: Option<Vec<Edit>>,
}

pub struct Line {
    pub number: i64,
    pub source: String,
    pub fixed: Option<Vec<String>>,
    pub comments: Vec<Comment>,
}

pub struct FileComments {
    pub name: String,
    pub lines: Vec<Line>,
}

pub struct Checked {
    pub file: String,
    pub groups: Vec<FileComments>,
    pub diffs: Vec<Result<String, (String, String)>>,
}

impl Checked {
    fn comments(&self) -> impl Iterator<Item = (&str, &Comment)> {
        self.groups.iter().flat_map(|group| {
            group
                .lines
                .iter()
                .flat_map(|line| &line.comments)
                .map(|comment| (group.name.as_str(), comment))
        })
    }

    pub fn has_comments(&self) -> bool {
        !self.groups.is_empty()
    }
}

pub enum Outcome {
    Checked(Checked),
    Unreadable { file: String, error: String },
}

pub struct Report {
    format: Format,
    color: bool,
    wiki_links: usize,
    wiki: Vec<(char, Level, i64, String)>,
    json: Vec<Vec<String>>,
    found: bool,
    reported: bool,
}

const UNINTERESTING: [i64; 10] = [1009, 1019, 1036, 1047, 1062, 1070, 1072, 1073, 1088, 1089];

impl Report {
    pub fn new(format: Format, color: bool, wiki_links: usize) -> Self {
        Report {
            format,
            color,
            wiki_links,
            wiki: Vec::new(),
            json: Vec::new(),
            found: false,
            reported: false,
        }
    }

    fn paint(&self, level: &str, text: &str) -> String {
        if !self.color {
            return text.to_string();
        }
        let code = match level {
            "error" => 31,
            "warning" => 33,
            "info" | "style" | "verbose" => 32,
            "message" => 1,
            _ => 0,
        };
        format!("\x1B[{code}m{text}\x1B[0m")
    }

    fn alarm(&self, text: &str) -> String {
        if self.color {
            format!("\x1B[1m\x1B[31m{text}\x1B[0m\x1B[0m")
        } else {
            text.to_string()
        }
    }

    pub fn header(&self, out: &mut impl Write) -> std::io::Result<()> {
        if self.format == Format::Checkstyle {
            writeln!(out, "<?xml version='1.0' encoding='UTF-8'?>")?;
            writeln!(out, "<checkstyle version='4.3'>")?;
        }
        Ok(())
    }

    pub fn file(&mut self, out: &mut impl Write, outcome: &Outcome) -> std::io::Result<()> {
        match outcome {
            Outcome::Unreadable { file, error } => self.unreadable(out, file, error),
            Outcome::Checked(checked) => match self.format {
                Format::Tty => self.tty(out, checked),
                Format::Gcc => gcc(out, checked),
                Format::Json1 => {
                    for group in &checked.groups {
                        self.json.push(
                            group
                                .lines
                                .iter()
                                .flat_map(|line| &line.comments)
                                .map(|comment| {
                                    json(&group.name, comment, &comment.real, &comment.real_fix)
                                })
                                .collect(),
                        );
                    }
                    Ok(())
                }
                Format::Json => {
                    let mut files: Vec<&str> = checked
                        .groups
                        .iter()
                        .map(|group| group.name.as_str())
                        .collect();
                    files.sort_unstable();
                    files.dedup();
                    let all: Vec<String> = checked
                        .comments()
                        .map(|(file, comment)| {
                            json(file, comment, &comment.expanded, &comment.expanded_fix)
                        })
                        .collect();
                    self.json.extend(files.iter().map(|_| all.clone()));
                    Ok(())
                }
                Format::Checkstyle => checkstyle(out, checked),
                Format::Diff => self.diff(out, checked),
                Format::Quiet => Ok(()),
            },
        }
    }

    fn unreadable(&self, out: &mut impl Write, file: &str, error: &str) -> std::io::Result<()> {
        let message = format!("{file}: {error}");
        match self.format {
            Format::Checkstyle => writeln!(
                out,
                "<file {}>\n<error {}{}{}{}{}/>\n</file>",
                attribute("name", file),
                attribute("line", "1"),
                attribute("column", "1"),
                attribute("severity", "error"),
                attribute("message", error),
                attribute("source", "ShellCheck")
            ),
            Format::Tty => {
                out.flush()?;
                eprintln!("{}", self.paint("error", &message));
                Ok(())
            }
            Format::Diff => {
                out.flush()?;
                eprintln!("{}", self.alarm(&message));
                Ok(())
            }
            _ => {
                out.flush()?;
                eprintln!("{message}");
                Ok(())
            }
        }
    }

    fn tty(&mut self, out: &mut impl Write, checked: &Checked) -> std::io::Result<()> {
        for (_, comment) in checked.comments() {
            let rank = if UNINTERESTING.contains(&comment.code) {
                'Z'
            } else {
                'A'
            };
            self.wiki
                .push((rank, comment.level, comment.code, comment.message.clone()));
        }
        self.wiki.sort();
        self.wiki.dedup_by(|later, earlier| {
            (later.0, later.1, later.2) == (earlier.0, earlier.1, earlier.2)
        });
        self.wiki.truncate(self.wiki_links);
        for group in &checked.groups {
            for line in &group.lines {
                writeln!(out)?;
                writeln!(
                    out,
                    "{}",
                    self.paint(
                        "message",
                        &format!("In {} line {}:", group.name, line.number)
                    )
                )?;
                writeln!(out, "{}", self.paint("source", &line.source))?;
                for comment in &line.comments {
                    writeln!(
                        out,
                        "{}",
                        self.paint(comment.level.text(), &cute_indent(comment))
                    )?;
                }
                writeln!(out)?;
                if let Some(fixed) = &line.fixed {
                    writeln!(out, "{}", self.paint("message", "Did you mean:"))?;
                    for text in fixed {
                        writeln!(out, "{text}")?;
                    }
                    writeln!(out)?;
                }
            }
        }
        Ok(())
    }

    fn diff(&mut self, out: &mut impl Write, checked: &Checked) -> std::io::Result<()> {
        self.found |= checked.has_comments();
        for diff in &checked.diffs {
            match diff {
                Ok(document) => {
                    writeln!(out, "{document}")?;
                    self.reported = true;
                }
                Err((file, error)) => {
                    out.flush()?;
                    eprintln!("{}", self.alarm(&format!("{file}: {error}")));
                }
            }
        }
        Ok(())
    }

    pub fn footer(&mut self, out: &mut impl Write) -> std::io::Result<()> {
        match self.format {
            Format::Tty if !self.wiki.is_empty() => {
                writeln!(out, "For more information:")?;
                for (_, _, code, message) in &self.wiki {
                    writeln!(
                        out,
                        "  https://www.shellcheck.net/wiki/SC{code} -- {}",
                        shorten(message)
                    )?;
                }
                Ok(())
            }
            Format::Json1 => writeln!(
                out,
                "{{\"comments\":[{}]}}",
                self.json
                    .iter()
                    .rev()
                    .flatten()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Format::Json => writeln!(
                out,
                "[{}]",
                self.json
                    .iter()
                    .rev()
                    .flatten()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Format::Checkstyle => writeln!(out, "</checkstyle>"),
            Format::Diff if self.found && !self.reported => {
                out.flush()?;
                eprintln!(
                    "{}",
                    self.alarm(
                        "Issues were detected, but none were auto-fixable. Use another format to see them."
                    )
                );
                Ok(())
            }
            _ => Ok(()),
        }
    }
}

fn shorten(message: &str) -> String {
    if message.chars().count() < 36 {
        message.to_string()
    } else {
        format!("{}...", message.chars().take(33).collect::<String>())
    }
}

fn cute_indent(comment: &Comment) -> String {
    let span = &comment.expanded;
    let delta = span.end_column - span.column;
    let arrow = if span.line == span.end_line && delta > 2 && delta < 32 {
        format!("^{}^", "-".repeat(usize::try_from(delta - 2).unwrap_or(0)))
    } else {
        "^--".to_string()
    };
    format!(
        "{}{arrow} SC{} ({}): {}",
        " ".repeat(usize::try_from(span.column - 1).unwrap_or(0)),
        comment.code,
        comment.level.text(),
        comment.message
    )
}

fn gcc(out: &mut impl Write, checked: &Checked) -> std::io::Result<()> {
    for (file, comment) in checked.comments() {
        let level = match comment.level {
            Level::Error | Level::Warning => comment.level.text(),
            Level::Info | Level::Style => "note",
        };
        writeln!(
            out,
            "{file}:{}:{}: {level}: {} [SC{}]",
            comment.real.line,
            comment.real.column,
            comment.message.replace('\n', ""),
            comment.code
        )?;
    }
    Ok(())
}

fn json_string(text: &str) -> String {
    let mut quoted = String::with_capacity(text.len() + 2);
    quoted.push('"');
    for c in text.chars() {
        match c {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            c if u32::from(c) < 0x20 => quoted.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => quoted.push(c),
        }
    }
    quoted.push('"');
    quoted
}

fn json(file: &str, comment: &Comment, span: &Span, fix: &Option<Vec<Edit>>) -> String {
    let fix = match fix {
        None => "null".to_string(),
        Some(edits) => format!(
            "{{\"replacements\":[{}]}}",
            edits
                .iter()
                .map(|edit| format!(
                    "{{\"column\":{},\"endColumn\":{},\"endLine\":{},\"insertionPoint\":{},\"line\":{},\"precedence\":{},\"replacement\":{}}}",
                    edit.span.column,
                    edit.span.end_column,
                    edit.span.end_line,
                    json_string(if edit.after_end { "afterEnd" } else { "beforeStart" }),
                    edit.span.line,
                    edit.precedence,
                    json_string(&edit.replacement)
                ))
                .collect::<Vec<_>>()
                .join(",")
        ),
    };
    format!(
        "{{\"file\":{},\"line\":{},\"endLine\":{},\"column\":{},\"endColumn\":{},\"level\":{},\"code\":{},\"message\":{},\"fix\":{fix}}}",
        json_string(file),
        span.line,
        span.end_line,
        span.column,
        span.end_column,
        json_string(comment.level.text()),
        comment.code,
        json_string(&comment.message)
    )
}

fn attribute(name: &str, value: &str) -> String {
    let escaped: String = value
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || " ./".contains(c) {
                c.to_string()
            } else {
                format!("&#{};", u32::from(c))
            }
        })
        .collect();
    format!("{name}='{escaped}' ")
}

fn checkstyle(out: &mut impl Write, checked: &Checked) -> std::io::Result<()> {
    if checked.groups.is_empty() {
        return writeln!(out, "<file {}>\n</file>", attribute("name", &checked.file));
    }
    for group in &checked.groups {
        let mut text = format!("<file {}>\n", attribute("name", &group.name));
        for comment in group.lines.iter().flat_map(|line| &line.comments) {
            let severity = match comment.level {
                Level::Error | Level::Warning => comment.level.text(),
                Level::Info | Level::Style => "info",
            };
            text.push_str(&format!(
                "<error {}{}{}{}{}/>\n",
                attribute("line", &comment.real.line.to_string()),
                attribute("column", &comment.real.column.to_string()),
                attribute("severity", severity),
                attribute("message", &comment.message),
                attribute("source", &format!("ShellCheck.SC{}", comment.code))
            ));
        }
        text.push_str("</file>");
        writeln!(out, "{text}")?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::json_string;

    #[test]
    fn escapes_strings_like_aeson() {
        assert_eq!(
            json_string("n\u{8}\u{c}\t\u{1b}\u{7f}\"\\é\u{2028}\n\r"),
            "\"n\\u0008\\u000c\\t\\u001b\u{7f}\\\"\\\\é\u{2028}\\n\\r\""
        );
    }
}
