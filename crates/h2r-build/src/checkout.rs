use std::fs::{self, File};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

use crate::extract::LAYOUTS;

#[derive(Clone, Debug)]
pub struct Checkout {
    root: PathBuf,
}

impl Checkout {
    pub fn locate() -> Result<Checkout> {
        Checkout::containing(Path::new(env!("CARGO_MANIFEST_DIR")))
    }

    pub fn containing(path: &Path) -> Result<Checkout> {
        path.ancestors()
            .find(|dir| dir.join("ShellCheck.cabal").is_file())
            .map(|root| Checkout {
                root: root.to_path_buf(),
            })
            .with_context(|| format!("no ShellCheck checkout contains {}", path.display()))
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn build(&self) -> PathBuf {
        self.root.join("compiler/build")
    }

    pub fn core_json(&self) -> PathBuf {
        self.root.join("compiler/core-json")
    }

    pub fn library_json(&self, package: &str) -> PathBuf {
        self.root.join("compiler/library-json").join(package)
    }

    pub fn plugin(&self) -> PathBuf {
        self.root.join("compiler/h2r-plugin")
    }

    pub fn entry_source(&self) -> PathBuf {
        self.root
            .join("crates/rshellcheck/entry/ShellCheckEntry.hs")
    }

    pub fn entry_json(&self) -> PathBuf {
        self.build().join("entry/core-json")
    }

    pub fn world(&self) -> (PathBuf, Vec<PathBuf>) {
        let with = LAYOUTS
            .iter()
            .map(|layout| self.library_json(layout.package))
            .chain([self.entry_json()])
            .collect();
        (self.core_json(), with)
    }

    pub fn lock(&self) -> Result<File> {
        let build = self.build();
        fs::create_dir_all(&build).with_context(|| format!("creating {}", build.display()))?;
        let path = build.join("h2r.lock");
        let file = File::options()
            .create(true)
            .truncate(false)
            .write(true)
            .open(&path)
            .with_context(|| format!("opening {}", path.display()))?;
        file.lock()
            .with_context(|| format!("locking {}", path.display()))?;
        Ok(file)
    }
}

#[cfg(test)]
mod tests {
    use super::Checkout;

    #[test]
    fn this_crate_sits_in_the_checkout() {
        let checkout = Checkout::locate().expect("the checkout");
        assert!(checkout.plugin().join("h2r-plugin.cabal").is_file());
        assert!(checkout.entry_source().is_file());
    }
}
