//! ShellCheck CLI support library: output formatters and option parsing.

#![doc(
    html_logo_url = "https://cdn.jsdelivr.net/gh/kjanat/shellcheck-rs@f666e756494d37a132ae6a37c44dc6b3fe01a57e/doc/shellcheck_logo.svg",
    html_favicon_url = "https://cdn.jsdelivr.net/gh/kjanat/shellcheck-rs@f666e756494d37a132ae6a37c44dc6b3fe01a57e/doc/shellcheck_logo.svg"
)]

#[cfg(all(test, feature = "completions"))]
mod completion_generator;
#[cfg(feature = "completions")]
pub mod completions;
pub mod formatter;
mod option_table;
pub mod options;
pub mod oracle;
pub mod paths;
pub mod rc;
