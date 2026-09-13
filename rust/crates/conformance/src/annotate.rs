//! GitHub Actions annotations for whatever a run finds.
//!
//! A conformance failure in CI is a wall of text in a log nobody opens. The
//! same finding as a *workflow command* becomes an annotation on the run
//! summary, and -- when it can be tied to a line of the repository -- a marker
//! in the Files-changed view of the pull request.
//!
//! These are emitted directly rather than through a third-party action:
//! `actions-rs/*` is archived and unmaintained, and all it ever did for this
//! was print the same `::error ...::` lines that any process can print. The
//! format is documented by GitHub under "workflow commands"; nothing needs to
//! be installed for it to work, and outside Actions the lines are inert.
//!
//! Severity is chosen to match what the finding means for the gate:
//!
//! * `error`  -- a divergence. The gate fails on these, so they fail the run.
//! * `warning` -- an input the oracle crashed on. Not our defect, but the
//!   comparison lost an input, so it must not be silent.
//! * `notice` -- a sanctioned deviation, and the corpus-coverage summary: the
//!   run is still green, but the reader should know the number.

use std::sync::OnceLock;

/// Whether to emit annotations at all: `--annotate`, or `GITHUB_ACTIONS=true`
/// as the runner sets it.
static ENABLED: OnceLock<bool> = OnceLock::new();

pub fn set_enabled(flag: bool) {
    let on = flag
        || std::env::var("GITHUB_ACTIONS")
            .map(|v| v == "true")
            .unwrap_or(false);
    let _ = ENABLED.set(on);
}

fn enabled() -> bool {
    *ENABLED.get().unwrap_or(&false)
}

/// Escape a property *value* (`file=`, `title=`) per the workflow-command
/// rules: a raw `%`, CR, LF, `:` or `,` would end the property or the command.
fn escape_property(s: &str) -> String {
    s.replace('%', "%25")
        .replace('\r', "%0D")
        .replace('\n', "%0A")
        .replace(':', "%3A")
        .replace(',', "%2C")
}

/// Escape the message body, where only `%`, CR and LF are special. A multi-line
/// message is legal and renders as multiple lines in the annotation.
fn escape_message(s: &str) -> String {
    s.replace('%', "%25")
        .replace('\r', "%0D")
        .replace('\n', "%0A")
}

/// Where in the repository a finding lives, when it lives anywhere.
///
/// A gate divergence comes from a `prop_` in the Haskell sources and can point
/// at that line. A fuzz divergence comes from a generated script that exists
/// nowhere, so it carries no location and renders against the workflow file.
pub struct Where {
    pub file: String,
    pub line: Option<usize>,
}

impl Where {
    pub fn at(file: &str, line: usize) -> Where {
        Where {
            file: file.to_string(),
            line: Some(line),
        }
    }
}

fn emit(level: &str, title: &str, place: Option<&Where>, message: &str) {
    if !enabled() {
        return;
    }
    let mut props = format!("title={}", escape_property(title));
    if let Some(w) = place {
        props.push_str(&format!(",file={}", escape_property(&w.file)));
        if let Some(l) = w.line {
            props.push_str(&format!(",line={l}"));
        }
    }
    // Straight to stdout, interleaved with the human-readable report: the
    // runner reads the log stream, so the two cannot get out of order.
    println!("::{level} {props}::{}", escape_message(message));
}

/// A divergence: the port and the oracle disagree. Fails the run.
pub fn divergence(id: &str, place: Option<&Where>, oracle: &str, port: &str) {
    emit(
        "error",
        &format!("Conformance divergence: {id}"),
        place,
        &format!("oracle: {oracle}\nport:   {port}"),
    );
}

/// An input the oracle could not answer for. Reported, never fatal.
pub fn oracle_crash(script: &str, reason: &str) {
    emit(
        "warning",
        "Oracle crashed on this input (upstream defect)",
        None,
        &format!("{reason}\nscript: {script:?}"),
    );
}

/// A difference the port is entitled to, as classified by `deviations`.
pub fn deviation(id: &str, what: &str) {
    emit("notice", &format!("Sanctioned deviation: {id}"), None, what);
}

/// A plain summary line, so the run's numbers are visible without opening the
/// log: how many were compared, how many diverged.
pub fn summary(text: &str) {
    emit("notice", "Conformance summary", None, text);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn property_escaping_covers_every_terminator() {
        // `:` and `,` end a property, `%` starts an escape, CR/LF end the
        // command -- all four have to survive a round trip.
        assert_eq!(escape_property("a:b,c%d\ne\rf"), "a%3Ab%2Cc%25d%0Ae%0Df");
    }

    #[test]
    fn message_escaping_leaves_colons_alone() {
        // A message keeps `:` and `,` -- escaping them would mangle every
        // diagnostic, which is mostly colons.
        assert_eq!(escape_message("SC2086 at 1:5, fix"), "SC2086 at 1:5, fix");
        assert_eq!(escape_message("100%\nnext"), "100%25%0Anext");
    }

    #[test]
    fn nothing_is_emitted_when_disabled() {
        // `enabled()` is the only gate; the emit helpers must not panic or
        // print when it is false. Covered here because the default in a unit
        // test run is exactly that.
        assert!(!enabled());
        divergence("x", None, "a", "b");
        oracle_crash("s", "r");
        deviation("d", "w");
        summary("s");
    }
}
