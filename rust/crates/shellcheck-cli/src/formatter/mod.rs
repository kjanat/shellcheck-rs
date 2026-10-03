//! Output formatters (consumers of the core `PositionedComment` results).

pub mod checkstyle;
pub mod diff;
pub mod fixer;
pub mod gcc;
pub mod json;
pub mod json1;
pub mod tty;

use shellcheck_rs::interface::ColorOption;

/// A TTY color function: `(level, text) -> rendered`.
///
/// Mirrors the Haskell `ColorFunc = String -> String -> String`.
pub type ColorFunc = Box<dyn Fn(&str, &str) -> String>;

fn color_for_level(level: &str) -> i32 {
    match level {
        "error" => 31,                      // red
        "warning" => 33,                    // yellow
        "info" | "style" | "verbose" => 32, // green
        "message" => 1,                     // bold
        _ => 0,                             // "source" and the rest: none
    }
}

/// Builds the TTY color function matching upstream `colorComment`.
///
/// Wraps all severity levels (including `source`, code 0) in ANSI escape sequences
/// when `use_color` is `true`. Passes text through unchanged when `false`.
pub fn tty_color_func(use_color: bool) -> ColorFunc {
    if use_color {
        Box::new(|level: &str, text: &str| {
            format!("\x1B[{}m{}\x1B[0m", color_for_level(level), text)
        })
    } else {
        Box::new(|_level: &str, text: &str| text.to_string())
    }
}

/// Resolves a [`ColorOption`] against terminal state matching upstream `shouldOutputColor`.
///
/// > **TODO:** Add Windows terminal support.
#[must_use]
pub fn should_output_color(opt: ColorOption, is_tty: bool) -> bool {
    match opt {
        ColorOption::ColorAlways => true,
        ColorOption::ColorNever => false,
        ColorOption::ColorAuto => {
            let term = std::env::var("TERM").ok();
            let dumb = matches!(term.as_deref(), Some("dumb" | "") | None);
            is_tty && !dumb
        }
    }
}
