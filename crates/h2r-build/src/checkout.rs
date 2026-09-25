use std::path::{Path, PathBuf};

#[derive(Clone, Debug)]
pub struct Checkout {
    root: PathBuf,
}

impl Checkout {
    pub fn locate() -> Checkout {
        Checkout {
            root: Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."),
        }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn plugin(&self) -> PathBuf {
        self.root.join("compiler/h2r-plugin")
    }

    pub fn plugin_project(&self) -> PathBuf {
        self.root.join("compiler/canary")
    }

    pub fn entry_source(&self) -> PathBuf {
        self.root.join("crates/hs-entry/ShellCheckEntry.hs")
    }
}

#[cfg(test)]
mod tests {
    use super::Checkout;

    #[test]
    fn this_crate_sits_in_the_checkout() {
        let checkout = Checkout::locate();
        assert!(checkout.root().join("ShellCheck.cabal").is_file());
        assert!(checkout.plugin().join("h2r-plugin.cabal").is_file());
        assert!(checkout.plugin_project().join("cabal.project").is_file());
    }
}
