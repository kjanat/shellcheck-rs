fn main() -> std::process::ExitCode {
    h2r_build::build_script(&[
        "$h2r-entry$ShellCheckEntry$lint",
        "$h2r-entry$ShellCheckEntry$optional",
        "$h2r-entry$ShellCheckEntry$version",
    ])
}
