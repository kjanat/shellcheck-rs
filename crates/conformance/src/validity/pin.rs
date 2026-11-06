use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

use super::matrix::{self, Cell, Matrix, SourcePin};
use super::sources::{self, Kind, Source};
use super::{DOCKERFILES, REGISTRY};

pub fn run(refresh: bool) -> Result<(), String> {
    let sources = sources::load()?;
    let previous = matrix::load()?;
    let mut bases: BTreeMap<String, String> = BTreeMap::new();
    let mut plans = Vec::new();
    for (name, source) in &sources.shell {
        let dockerfile = source.image.clone().unwrap_or_else(|| name.clone());
        let file = Path::new(DOCKERFILES).join(&dockerfile).join("Dockerfile");
        if !file.is_file() {
            return Err(format!("{}: missing", file.display()));
        }
        let base_name = source.base.as_deref().unwrap_or(&sources.defaults.base);
        for version in &source.versions {
            let prev = previous.find(name, version);
            let base = match prev.filter(|_| !refresh) {
                Some(p) if p.base.starts_with(repo_of(base_name)) => p.base.clone(),
                _ => resolve_base(&mut bases, base_name)?,
            };
            plans.push(Plan {
                name,
                source,
                version,
                previous: prev.map(|c| &c.source),
                previous_digest: prev.map(|c| c.digest.as_str()),
                base,
                dockerfile: dockerfile.clone(),
            });
        }
    }

    let cells = resolve_plans(&plans, &sources.defaults.parse, refresh)?;
    let mut matrix = Matrix::default();
    for cell in cells {
        println!("pinned {}:{}", cell.shell, cell.version);
        matrix.cell.push(cell);
    }
    matrix.sort();
    matrix::save(&matrix)
}

struct Plan<'a> {
    name: &'a str,
    source: &'a Source,
    version: &'a str,
    previous: Option<&'a SourcePin>,
    previous_digest: Option<&'a str>,
    base: String,
    dockerfile: String,
}

fn resolve_plans(
    plans: &[Plan<'_>],
    default_parse: &[String],
    refresh: bool,
) -> Result<Vec<Cell>, String> {
    if plans.is_empty() {
        return Ok(Vec::new());
    }
    let workers = plans.len();
    let chunk_size = plans.len().div_ceil(workers);
    thread::scope(|scope| {
        let handles: Vec<_> = plans
            .chunks(chunk_size)
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter()
                        .map(|plan| resolve_plan(plan, default_parse, refresh))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        let mut cells = Vec::with_capacity(plans.len());
        for handle in handles {
            for cell in handle
                .join()
                .map_err(|_| "pin worker panicked".to_string())?
            {
                cells.push(cell?);
            }
        }
        Ok(cells)
    })
}

fn resolve_plan(plan: &Plan<'_>, default_parse: &[String], refresh: bool) -> Result<Cell, String> {
    let image = format!("{REGISTRY}/shell-{}:{}", plan.dockerfile, plan.version);
    Ok(Cell {
        shell: plan.name.to_string(),
        version: plan.version.to_string(),
        digest: pinned_digest(&image, lookup(&image), plan.previous_digest),
        image,
        base: plan.base.clone(),
        dockerfile: plan.dockerfile.clone(),
        argv: plan.source.argv.clone(),
        parse: plan
            .source
            .parse
            .clone()
            .unwrap_or_else(|| default_parse.to_vec()),
        shipped: plan.source.shipped,
        vm: plan.source.vm,
        dialect: plan.source.dialect.clone(),
        source: resolve_source(plan.source, plan.version, plan.previous, refresh)?,
    })
}

fn repo_of(image: &str) -> &str {
    image.rsplit_once(':').map_or(image, |(r, _)| r)
}

fn resolve_base(cache: &mut BTreeMap<String, String>, name: &str) -> Result<String, String> {
    if let Some(found) = cache.get(name) {
        return Ok(found.clone());
    }
    let digest = manifest_digest(name).ok_or_else(|| format!("{name}: no manifest digest"))?;
    let pinned = format!("{}@{digest}", repo_of(name));
    cache.insert(name.to_string(), pinned.clone());
    Ok(pinned)
}

#[derive(Debug, PartialEq, Eq)]
enum Lookup {
    Found(String),
    Missing,
    Failed(String),
}

pub fn manifest_digest(reference: &str) -> Option<String> {
    match lookup(reference) {
        Lookup::Found(digest) => Some(digest),
        Lookup::Missing | Lookup::Failed(_) => None,
    }
}

fn lookup(reference: &str) -> Lookup {
    let mut result = lookup_once(reference);
    for delay in [1, 2] {
        if !matches!(result, Lookup::Failed(_)) {
            break;
        }
        thread::sleep(std::time::Duration::from_secs(delay));
        result = lookup_once(reference);
    }
    result
}

fn lookup_once(reference: &str) -> Lookup {
    match Command::new("docker")
        .args([
            "buildx",
            "imagetools",
            "inspect",
            reference,
            "--format",
            "{{.Manifest.Digest}}",
        ])
        .output()
    {
        Ok(out) => classify(
            out.status.success(),
            &String::from_utf8_lossy(&out.stdout),
            &String::from_utf8_lossy(&out.stderr),
        ),
        Err(e) => Lookup::Failed(format!("docker: {e}")),
    }
}

fn classify(success: bool, stdout: &str, stderr: &str) -> Lookup {
    let digest = stdout.trim();
    if success && digest.starts_with("sha256:") {
        return Lookup::Found(digest.to_string());
    }
    let reason = stderr.to_ascii_lowercase();
    if !success && (reason.contains("not found") || reason.contains("manifest unknown")) {
        return Lookup::Missing;
    }
    Lookup::Failed(if stderr.trim().is_empty() {
        format!("unexpected output {digest:?}")
    } else {
        stderr.trim().to_string()
    })
}

fn pinned_digest(image: &str, lookup: Lookup, previous: Option<&str>) -> String {
    match lookup {
        Lookup::Found(digest) => digest,
        Lookup::Missing => String::new(),
        Lookup::Failed(reason) => {
            let kept = previous.unwrap_or_default();
            eprintln!("warning: {image}: digest lookup failed ({reason}); keeping {kept:?}");
            kept.to_string()
        }
    }
}

fn resolve_source(
    source: &Source,
    version: &str,
    previous: Option<&SourcePin>,
    refresh: bool,
) -> Result<SourcePin, String> {
    match source.kind {
        Kind::Tarball => {
            let url = source.url.replace("{version}", version);
            if let Some(SourcePin::Tarball { url: u, sha256 }) = previous
                && *u == url
                && !sha256.is_empty()
            {
                return Ok(SourcePin::Tarball {
                    url,
                    sha256: sha256.clone(),
                });
            }
            let sha256 = sha256_of_url(&url)?;
            Ok(SourcePin::Tarball { url, sha256 })
        }
        Kind::Git => {
            let tag = source.tag.replace("{version}", version);
            if let Some(SourcePin::Git {
                repo,
                tag: t,
                commit,
            }) = previous
                && !refresh
                && *repo == source.repo
                && *t == tag
            {
                return Ok(SourcePin::Git {
                    repo: repo.clone(),
                    tag,
                    commit: commit.clone(),
                });
            }
            let commit = ls_remote(&source.repo, &tag)?;
            Ok(SourcePin::Git {
                repo: source.repo.clone(),
                tag,
                commit,
            })
        }
        Kind::Crate => Ok(SourcePin::Crate {
            version: version.to_string(),
        }),
        Kind::Image => {
            let url = source.url.replace("{version}", version);
            if let Some(SourcePin::Image { url: u, sha256 }) = previous
                && *u == url
                && !sha256.is_empty()
            {
                return Ok(SourcePin::Image {
                    url,
                    sha256: sha256.clone(),
                });
            }
            let sha256 = sha256_of_url(&url)?;
            Ok(SourcePin::Image { url, sha256 })
        }
    }
}

fn sha256_of_url(url: &str) -> Result<String, String> {
    static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);
    let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let file = std::env::temp_dir().join(format!("validity-pin-{}-{sequence}", std::process::id()));
    let status = Command::new("curl")
        .args([
            "--silent",
            "--show-error",
            "--location",
            "--fail",
            "--connect-timeout",
            "20",
            "--max-time",
            "600",
            "--retry",
            "2",
            "--retry-connrefused",
            "--retry-max-time",
            "1800",
            "--output",
        ])
        .arg(&file)
        .arg(url)
        .status()
        .map_err(|e| format!("curl: {e}"))?;
    if !status.success() {
        return Err(format!("{url}: download failed"));
    }
    let out = Command::new("sha256sum")
        .arg(&file)
        .output()
        .map_err(|e| format!("sha256sum: {e}"))?;
    let _ = std::fs::remove_file(&file);
    let text = String::from_utf8_lossy(&out.stdout);
    parse_sha256sum(&text).ok_or_else(|| format!("{url}: no checksum"))
}

fn parse_sha256sum(output: &str) -> Option<String> {
    let sum = output.split_whitespace().next()?;
    (sum.len() == 64 && sum.chars().all(|c| c.is_ascii_hexdigit())).then(|| sum.to_string())
}

fn ls_remote(repo: &str, tag: &str) -> Result<String, String> {
    let out = Command::new("git")
        .args(["ls-remote", "--tags", repo])
        .arg(format!("refs/tags/{tag}"))
        .arg(format!("refs/tags/{tag}^{{}}"))
        .output()
        .map_err(|e| format!("git: {e}"))?;
    if !out.status.success() {
        return Err(format!("{repo}: ls-remote failed"));
    }
    parse_ls_remote(&String::from_utf8_lossy(&out.stdout), tag)
        .ok_or_else(|| format!("{repo}: no tag {tag}"))
}

fn parse_ls_remote(output: &str, tag: &str) -> Option<String> {
    let peeled = format!("refs/tags/{tag}^{{}}");
    let plain = format!("refs/tags/{tag}");
    let mut found = None;
    for line in output.lines() {
        let (sha, name) = line.split_once('\t')?;
        if name == peeled {
            return Some(sha.to_string());
        }
        if name == plain {
            found = Some(sha.to_string());
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_lookup_tells_a_missing_image_from_a_failed_request() {
        assert_eq!(
            classify(true, "sha256:abc\n", ""),
            Lookup::Found("sha256:abc".to_string())
        );
        assert_eq!(
            classify(false, "", "ERROR: ghcr.io/x/shell-bash:9: not found\n"),
            Lookup::Missing
        );
        assert_eq!(
            classify(false, "", "MANIFEST_UNKNOWN: manifest unknown"),
            Lookup::Missing
        );
        assert_eq!(
            classify(false, "", "429 Too Many Requests\n"),
            Lookup::Failed("429 Too Many Requests".to_string())
        );
        assert_eq!(
            classify(true, "garbage", ""),
            Lookup::Failed("unexpected output \"garbage\"".to_string())
        );
    }

    #[test]
    fn a_failed_lookup_keeps_the_previous_digest_and_a_missing_image_clears_it() {
        let image = "ghcr.io/x/shell-bash:5";
        assert_eq!(
            pinned_digest(
                image,
                Lookup::Found("sha256:new".to_string()),
                Some("sha256:old")
            ),
            "sha256:new"
        );
        assert_eq!(
            pinned_digest(image, Lookup::Missing, Some("sha256:old")),
            ""
        );
        assert_eq!(
            pinned_digest(image, Lookup::Failed("429".to_string()), Some("sha256:old")),
            "sha256:old"
        );
        assert_eq!(
            pinned_digest(image, Lookup::Failed("429".to_string()), None),
            ""
        );
    }

    #[test]
    fn the_peeled_tag_wins_over_the_tag_object() {
        let out = "aaaa\trefs/tags/v1\nbbbb\trefs/tags/v1^{}\n";
        assert_eq!(parse_ls_remote(out, "v1").as_deref(), Some("bbbb"));
        assert_eq!(
            parse_ls_remote("aaaa\trefs/tags/v1\n", "v1").as_deref(),
            Some("aaaa")
        );
        assert!(parse_ls_remote("", "v1").is_none());
    }

    #[test]
    fn a_pinned_image_is_reused_without_a_download() {
        let source = Source {
            kind: Kind::Image,
            url: "https://example.invalid/img-{version}.gz".to_string(),
            repo: String::new(),
            tag: String::new(),
            versions: vec!["1".to_string()],
            argv: vec!["sh".to_string()],
            parse: None,
            shipped: false,
            vm: true,
            dialect: None,
            image: None,
            base: None,
        };
        let previous = SourcePin::Image {
            url: "https://example.invalid/img-1.gz".to_string(),
            sha256: "f".repeat(64),
        };
        let pin = resolve_source(&source, "1", Some(&previous), false).unwrap();
        assert_eq!(pin, previous);
        assert_eq!(
            pin.build_args(),
            vec![
                ("KIND", "image"),
                ("SOURCE", "https://example.invalid/img-1.gz"),
                ("SHA256", "f".repeat(64).as_str()),
            ]
        );
    }

    #[test]
    fn sha256sum_output_is_validated() {
        let ok = format!("{}  file\n", "a".repeat(64));
        assert_eq!(
            parse_sha256sum(&ok).as_deref(),
            Some("a".repeat(64).as_str())
        );
        assert!(parse_sha256sum("short  file\n").is_none());
    }

    #[test]
    fn a_tag_strips_to_its_repository() {
        assert_eq!(repo_of("debian:bookworm-slim"), "debian");
        assert_eq!(repo_of("ghcr.io/x/y:1"), "ghcr.io/x/y");
        assert_eq!(repo_of("debian"), "debian");
    }
}
