//! Binary-to-binary conformance infrastructure; no dependency on either compiler.
pub mod corpus;
pub mod generator;
pub mod runner;

#[cfg(test)]
fn checkout() -> Option<&'static std::path::Path> {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .find(|dir| dir.join("ShellCheck.cabal").is_file())
}
