//! Plans validity image builds from changed inputs and registry availability.
//!
//! The selector works from the checked-in matrix and the matrix at the merge
//! base. This keeps a matrix refresh from dropping an old cell from the build,
//! while the output itself always contains current cells (deleted cells
//! therefore disappear). Cells without a resolved OCI digest are always
//! selected.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use toml::{Table, Value};

/// Fields which change the image build; the digest and runtime metadata do
/// not.
const BUILD_INPUTS: [&str; 6] = ["shell", "version", "image", "base", "dockerfile", "source"];

struct Cell {
    id: String,
    shell: String,
    dockerfile: String,
    vm: bool,
    pushed: bool,
    inputs: Vec<Value>,
}

fn git(dir: &Path, args: &[&str]) -> Result<String, String> {
    let output = Command::new("git")
        .args(args)
        .current_dir(dir)
        // `missing` matches git's English wording.
        .env("LC_ALL", "C")
        .output()
        .map_err(|e| format!("git {}: {e}", args.join(" ")))?;
    if output.status.success() {
        return String::from_utf8(output.stdout).map_err(|e| e.to_string());
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    Err(match stderr.trim() {
        "" => format!("git {} failed", args.join(" ")),
        message => message.to_string(),
    })
}

/// Whether `error` reports a path a valid commit does not hold.
fn missing(error: &str) -> bool {
    error.contains("exists on disk, but not in") || error.contains("does not exist in")
}

fn load_matrix(text: &str, label: &str) -> Result<Vec<Cell>, String> {
    let data: Table = toml::from_str(text).map_err(|e| format!("{label}: invalid TOML: {e}"))?;
    let Some(Value::Array(rows)) = data.get("cell") else {
        return Err(format!("{label}: expected a [[cell]] array"));
    };
    let mut cells = Vec::new();
    let mut seen = BTreeSet::new();
    for (n, row) in rows.iter().enumerate() {
        let inputs: Option<Vec<Value>> = BUILD_INPUTS
            .iter()
            .map(|key| row.get(key).cloned())
            .collect();
        let Some(inputs) = inputs.filter(|_| row.is_table()) else {
            return Err(format!("{label}: cell {n} is missing required fields"));
        };
        let field = |key: &str| row.get(key).and_then(Value::as_str);
        let (Some(shell), Some(version)) = (field("shell"), field("version")) else {
            return Err(format!("{label}: cell {n} has a non-string id"));
        };
        let (Some(_), Some(_), Some(dockerfile)) =
            (field("image"), field("base"), field("dockerfile"))
        else {
            return Err(format!("{label}: cell {n} has invalid build fields"));
        };
        let id = format!("{shell}:{version}");
        if !seen.insert(id.clone()) {
            return Err(format!("{label}: duplicate cell {id}"));
        }
        cells.push(Cell {
            id,
            shell: shell.to_string(),
            dockerfile: dockerfile.to_string(),
            vm: row.get("vm").and_then(Value::as_bool).unwrap_or(false),
            pushed: field("digest").is_some_and(|digest| !digest.trim().is_empty()),
            inputs,
        });
    }
    Ok(cells)
}

/// The shell sections of `sources.toml` that differ from `base`, or `None`
/// when the whole file is affected.
fn changed_source_shells(base: &str, dir: &Path) -> Result<Option<BTreeSet<String>>, String> {
    let current = match std::fs::read_to_string(dir.join(super::SOURCES)) {
        Ok(text) => text,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(format!("{}: {e}", super::SOURCES)),
    };
    let old = match git(dir, &["show", &format!("{base}:{}", super::SOURCES)]) {
        Ok(text) => text,
        Err(e) if missing(&e) => return Ok(None),
        Err(e) => return Err(e),
    };
    let parse = |text: &str| -> Result<Table, String> {
        toml::from_str(text).map_err(|e| format!("{}: invalid TOML: {e}", super::SOURCES))
    };
    let (current, old) = (parse(&current)?, parse(&old)?);
    let (Some(Value::Table(current_shells)), Some(Value::Table(old_shells))) =
        (current.get("shell"), old.get("shell"))
    else {
        return Err(format!("{}: expected [shell.NAME] tables", super::SOURCES));
    };
    if current.get("defaults") != old.get("defaults") {
        return Ok(None);
    }
    Ok(Some(
        current_shells
            .keys()
            .chain(old_shells.keys())
            .filter(|shell| current_shells.get(*shell) != old_shells.get(*shell))
            .cloned()
            .collect(),
    ))
}

/// The ids of the cells in `dir`'s matrix whose image must be built, in
/// matrix order. Without `base`, those are the cells without a digest.
pub fn affected(base: Option<&str>, dir: &Path) -> Result<Vec<String>, String> {
    let text = std::fs::read_to_string(dir.join(super::MATRIX))
        .map_err(|e| format!("{}: {e}", super::MATRIX))?;
    let current = load_matrix(&text, super::MATRIX)?;
    let mut selected: BTreeSet<&str> = current
        .iter()
        .filter(|cell| !cell.pushed)
        .map(|cell| cell.id.as_str())
        .collect();
    if let Some(base) = base {
        let ancestor = git(dir, &["merge-base", base, "HEAD"])?;
        let ancestor = ancestor.trim();
        // A matrix the merge base lacks is a new matrix. Any other git
        // failure, an invalid base among them, is an error.
        let old = match git(dir, &["show", &format!("{ancestor}:{}", super::MATRIX)]) {
            Ok(text) => load_matrix(&text, &format!("{ancestor}:{}", super::MATRIX))?,
            Err(e) if missing(&e) => Vec::new(),
            Err(e) => return Err(e),
        };
        let old: BTreeMap<&str, &Cell> = old.iter().map(|cell| (cell.id.as_str(), cell)).collect();
        let mut select = |wanted: &dyn Fn(&Cell) -> bool| {
            selected.extend(
                current
                    .iter()
                    .filter(|cell| wanted(cell))
                    .map(|cell| cell.id.as_str()),
            );
        };
        select(&|cell| {
            old.get(cell.id.as_str())
                .is_none_or(|old| old.inputs != cell.inputs)
        });
        let paths = git(
            dir,
            &["diff", "--name-only", "-z", &format!("{ancestor}...HEAD")],
        )?;
        for path in paths.split('\0').filter(|path| !path.is_empty()) {
            if path == super::MATRIX {
                continue;
            }
            if path == super::SOURCES {
                match changed_source_shells(ancestor, dir)? {
                    None => select(&|_| true),
                    Some(shells) => select(&|cell| shells.contains(&cell.shell)),
                }
            } else if path == "docker/shells/fetch.sh" {
                select(&|_| true);
            } else if path.starts_with("docker/shells/vm/") {
                select(&|cell| cell.vm);
            } else if let Some(rest) = path.strip_prefix("docker/shells/") {
                let dockerfile = rest.split('/').next().unwrap_or_default();
                select(&|cell| cell.dockerfile == dockerfile);
            } else if path == "crates/conformance/src/validity/docker.rs" {
                select(&|_| true);
            }
        }
    }
    Ok(current
        .iter()
        .filter(|cell| selected.contains(cell.id.as_str()))
        .map(|cell| cell.id.clone())
        .collect())
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

    const MATRIX: &str = r#"[[cell]]
shell = "bash"
version = "5"
image = "shell-bash:5"
digest = "sha256:bash"
base = "debian@sha256:a"
dockerfile = "bash"
source = { kind = "tarball" }

[[cell]]
shell = "zsh"
version = "5.9"
image = "shell-zsh:5.9"
digest = "sha256:zsh"
base = "debian@sha256:a"
dockerfile = "zsh"
source = { kind = "tarball" }

[[cell]]
shell = "zsh-sh"
version = "5.9"
image = "shell-zsh-sh:5.9"
digest = "sha256:zsh-sh"
base = "debian@sha256:a"
dockerfile = "zsh"
source = { kind = "tarball" }

[[cell]]
shell = "netbsd-sh"
version = "11"
image = "shell-netbsd-sh:11"
digest = "sha256:netbsd"
base = "debian@sha256:a"
dockerfile = "netbsd-sh"
vm = true
source = { kind = "image" }
"#;
    const SOURCES: &str = "[defaults]\nbase = 'debian'\n\n[shell.bash]\nversions=['5']\n\n[shell.zsh]\nversions=['5.9']\n";
    const ALL: [&str; 4] = ["bash:5", "zsh:5.9", "zsh-sh:5.9", "netbsd-sh:11"];

    static NEXT: AtomicU64 = AtomicU64::new(0);

    /// A git repository holding the matrix and the sources, committed once.
    struct Repo {
        root: PathBuf,
        base: String,
    }

    impl Repo {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!(
                "validity-affected-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir_all(root.join("validity")).unwrap();
            std::fs::write(root.join(crate::validity::MATRIX), MATRIX).unwrap();
            std::fs::write(root.join(crate::validity::SOURCES), SOURCES).unwrap();
            let mut repo = Self {
                root,
                base: String::new(),
            };
            repo.git(&["init", "-q"]);
            repo.git(&["config", "user.email", "test@example.invalid"]);
            repo.git(&["config", "user.name", "Test"]);
            repo.git(&["config", "commit.gpgsign", "false"]);
            repo.base = repo.commit("base");
            repo
        }

        fn git(&self, args: &[&str]) -> String {
            git(&self.root, args).unwrap_or_else(|e| panic!("git {args:?}: {e}"))
        }

        fn commit(&self, message: &str) -> String {
            self.git(&["add", "--all", "."]);
            self.git(&["commit", "-qm", message]);
            self.git(&["rev-parse", "HEAD"]).trim().to_string()
        }

        fn write(&self, path: &str, text: &str) {
            let target = self.root.join(path);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, text).unwrap();
        }

        fn change(&self, path: &str, text: &str) -> String {
            self.write(path, text);
            self.commit("change")
        }

        fn affected(&self, base: Option<&str>) -> Result<Vec<String>, String> {
            affected(base, &self.root)
        }

        fn since_base(&self) -> Vec<String> {
            self.affected(Some(&self.base)).unwrap()
        }
    }

    impl Drop for Repo {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn matrix_field_change_selects_only_that_cell() {
        let repo = Repo::new();
        repo.change(
            crate::validity::MATRIX,
            &MATRIX.replacen(
                "base = \"debian@sha256:a\"",
                "base = \"debian@sha256:b\"",
                1,
            ),
        );
        assert_eq!(repo.since_base(), ["bash:5"]);
    }

    #[test]
    fn shared_dockerfile_selects_both_zsh_cells() {
        let repo = Repo::new();
        repo.change("docker/shells/zsh/Dockerfile", "FROM alpine\n");
        assert_eq!(repo.since_base(), ["zsh:5.9", "zsh-sh:5.9"]);
    }

    #[test]
    fn vm_helper_selects_vm_cells_only() {
        let repo = Repo::new();
        repo.change("docker/shells/vm/vmsh", "changed\n");
        assert_eq!(repo.since_base(), ["netbsd-sh:11"]);
    }

    #[test]
    fn fetch_script_selects_every_cell() {
        let repo = Repo::new();
        repo.change("docker/shells/fetch.sh", "changed\n");
        assert_eq!(repo.since_base(), ALL);
    }

    #[test]
    fn source_shell_change_selects_that_shell() {
        let repo = Repo::new();
        repo.change(
            crate::validity::SOURCES,
            &SOURCES.replace("versions=['5']", "versions=['6']"),
        );
        assert_eq!(repo.since_base(), ["bash:5"]);
    }

    #[test]
    fn source_defaults_change_selects_every_cell() {
        let repo = Repo::new();
        repo.change(
            crate::validity::SOURCES,
            &SOURCES.replace("base = 'debian'", "base = 'alpine'"),
        );
        assert_eq!(repo.since_base(), ALL);
    }

    #[test]
    fn image_builder_change_selects_every_cell() {
        let repo = Repo::new();
        repo.change("crates/conformance/src/validity/docker.rs", "changed\n");
        assert_eq!(repo.since_base(), ALL);
    }

    #[test]
    fn tooling_workflows_the_planner_and_docs_do_not_build_images() {
        for path in [
            ".cargo/config.toml",
            ".github/workflows/shells.yml",
            "crates/conformance/src/validity/affected.rs",
            "docs/validity.md",
        ] {
            let repo = Repo::new();
            repo.change(path, "changed\n");
            assert_eq!(repo.since_base(), [""; 0], "{path}");
        }
    }

    #[test]
    fn deleted_cell_is_not_selected() {
        let repo = Repo::new();
        let (kept, _) = MATRIX
            .split_once("\n[[cell]]\nshell = \"netbsd-sh\"")
            .unwrap();
        repo.change(crate::validity::MATRIX, kept);
        assert!(!repo.since_base().contains(&"netbsd-sh:11".to_string()));
    }

    #[test]
    fn digest_only_change_does_not_build() {
        let repo = Repo::new();
        repo.change(
            crate::validity::MATRIX,
            &MATRIX.replace("digest = \"sha256:bash\"", "digest = \"sha256:new\""),
        );
        assert_eq!(repo.since_base(), [""; 0]);
    }

    #[test]
    fn missing_registry_digest_is_always_selected() {
        let repo = Repo::new();
        repo.write(
            crate::validity::MATRIX,
            &MATRIX.replacen("digest = \"sha256:bash\"\n", "", 1),
        );
        assert_eq!(repo.affected(None).unwrap(), ["bash:5"]);
    }

    #[test]
    fn pin_only_current_matrix_change_is_detected() {
        let repo = Repo::new();
        repo.write(
            crate::validity::MATRIX,
            &MATRIX.replacen(
                "base = \"debian@sha256:a\"",
                "base = \"debian@sha256:pinned\"",
                1,
            ),
        );
        assert_eq!(repo.since_base(), ["bash:5"]);
    }

    #[test]
    fn merge_base_is_used_for_divergent_base() {
        let repo = Repo::new();
        let edit = |base: &str| {
            MATRIX.replacen(
                "base = \"debian@sha256:a\"",
                &format!("base = \"debian@sha256:{base}\""),
                1,
            )
        };
        repo.git(&["checkout", "-qb", "other"]);
        let divergent = repo.change(crate::validity::MATRIX, &edit("other"));
        repo.git(&["checkout", "-q", "-b", "feature", &repo.base]);
        repo.change(crate::validity::MATRIX, &edit("feature"));
        assert_eq!(repo.affected(Some(&divergent)).unwrap(), ["bash:5"]);
    }

    #[test]
    fn missing_base_matrix_builds_all_current_cells() {
        let repo = Repo::new();
        repo.git(&["rm", "-q", crate::validity::MATRIX]);
        let without = repo.commit("remove matrix");
        repo.change(crate::validity::MATRIX, MATRIX);
        assert_eq!(repo.affected(Some(&without)).unwrap(), ALL);
    }

    #[test]
    fn malformed_current_matrix_fails() {
        let repo = Repo::new();
        repo.write(crate::validity::MATRIX, "[[cell]\n");
        let error = repo.affected(Some(&repo.base)).unwrap_err();
        assert!(error.contains("invalid TOML"), "{error}");
    }

    #[test]
    fn an_unknown_base_fails() {
        let repo = Repo::new();
        let error = repo.affected(Some(&"0".repeat(39))).unwrap_err();
        assert!(error.contains("Not a valid object name"), "{error}");
    }
}
