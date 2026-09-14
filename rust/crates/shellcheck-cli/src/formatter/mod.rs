//! Output formatters (consumers of the core `PositionedComment` results).

pub mod checkstyle;
pub mod diff;
pub mod fixer;
pub mod gcc;
pub mod json;
pub mod json1;
pub mod tty;

use shellcheck_rs::interface::ColorOption;

/// A TTY color function: `(level, text) -> rendered`. Mirrors the Haskell
/// `ColorFunc = String -> String -> String`.
pub type ColorFunc = Box<dyn Fn(&str, &str) -> String>;

fn color_for_level(level: &str) -> i32 {
    match level {
        "error" => 31,
        "warning" => 33,
        "info" => 32,
        "style" => 32,
        "verbose" => 32,
        "message" => 1,
        "source" => 0,
        _ => 0,
    }
}

/// Build the TTY color function. When `use_color` is false, text passes through
/// unchanged (`const id`); otherwise every level (including `source`, code 0) is
/// wrapped in the ANSI escape and cleared, matching `colorComment`.
pub fn tty_color_func(use_color: bool) -> ColorFunc {
    if use_color {
        Box::new(|level: &str, text: &str| {
            format!("\x1B[{}m{}\x1B[0m", color_for_level(level), text)
        })
    } else {
        Box::new(|_level: &str, text: &str| text.to_string())
    }
}

/// `shouldOutputColor`: resolve a `ColorOption` against the terminal state.
/// (No Windows handling: this port targets non-mingw platforms.)
pub fn should_output_color(opt: ColorOption, is_tty: bool) -> bool {
    match opt {
        ColorOption::ColorAlways => true,
        ColorOption::ColorNever => false,
        ColorOption::ColorAuto => {
            let term = std::env::var("TERM").ok();
            let dumb = matches!(term.as_deref(), Some("dumb") | Some("") | None);
            is_tty && !dumb
        }
    }
}
