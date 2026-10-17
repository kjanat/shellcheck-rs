use std::path::Path;

use schemars::JsonSchema;
use serde::Deserialize;

#[derive(Deserialize, JsonSchema, Debug)]
#[serde(deny_unknown_fields)]
pub struct Spec {
    pub code: i64,
    pub claim: String,
    pub shell: Option<String>,
    pub snippet: Script,
    pub fixed: Script,
    pub observe: Vec<Observe>,
}

#[derive(Deserialize, JsonSchema, Debug)]
#[serde(deny_unknown_fields)]
pub struct Script {
    pub script: String,
}

#[derive(Deserialize, JsonSchema, Debug)]
#[serde(deny_unknown_fields)]
pub struct Observe {
    pub kind: Kind,
    pub snippet: String,
    pub fixed: String,
}

#[derive(Deserialize, JsonSchema, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "kebab-case")]
pub enum Kind {
    Stdout,
    Status,
    StderrContains,
    Parse,
}

pub const PARSE_ACCEPTED: &str = "accepted";
pub const PARSE_REJECTED: &str = "rejected";

impl Spec {
    pub fn observes_parse(&self) -> bool {
        self.observe.iter().any(|o| o.kind == Kind::Parse)
    }

    pub fn observes_runtime(&self) -> bool {
        self.observe.iter().any(|o| o.kind != Kind::Parse)
    }
}

pub fn load(codes: &[i64]) -> Result<Vec<Spec>, String> {
    load_from(Path::new(super::SPECS), codes)
}

pub fn load_from(dir: &Path, codes: &[i64]) -> Result<Vec<Spec>, String> {
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "toml"))
        .collect();
    paths.sort();
    let mut specs = Vec::new();
    for path in paths {
        let shown = path.display().to_string();
        let text = std::fs::read_to_string(&path).map_err(|e| format!("{shown}: {e}"))?;
        let spec: Spec = toml::from_str(&text).map_err(|e| format!("{shown}: {e}"))?;
        let expected = format!("SC{}.toml", spec.code);
        if path.file_name().is_none_or(|n| n != expected.as_str()) {
            return Err(format!(
                "{shown}: file name does not match code {}",
                spec.code
            ));
        }
        if spec.observe.is_empty() {
            return Err(format!("{shown}: no observe block"));
        }
        for value in spec
            .observe
            .iter()
            .filter(|o| o.kind == Kind::Parse)
            .flat_map(|o| [&o.snippet, &o.fixed])
        {
            if value != PARSE_ACCEPTED && value != PARSE_REJECTED {
                return Err(format!(
                    "{shown}: a parse observe takes {PARSE_ACCEPTED:?} or {PARSE_REJECTED:?}, not {value:?}"
                ));
            }
        }
        if codes.is_empty() || codes.contains(&spec.code) {
            specs.push(spec);
        }
    }
    specs.sort_by_key(|s| s.code);
    Ok(specs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_checked_in_specs_load_and_filter() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(crate::validity::SPECS);
        let all = load_from(&dir, &[]).unwrap();
        assert!(all.iter().any(|s| s.code == 2086));
        let one = load_from(&dir, &[2164]).unwrap();
        assert_eq!(one.len(), 1);
        assert_eq!(one[0].observe.len(), 2);
        assert_eq!(
            all.iter()
                .find(|s| s.code == 3010)
                .unwrap()
                .shell
                .as_deref(),
            Some("sh")
        );
    }

    #[test]
    fn a_misnamed_spec_is_rejected() {
        let dir = std::env::temp_dir().join(format!("validity-spec-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("SC1.toml"),
            "code = 2\nclaim = \"c\"\n[snippet]\nscript = \"a\"\n[fixed]\nscript = \"b\"\n[[observe]]\nkind = \"stdout\"\nsnippet = \"\"\nfixed = \"\"\n",
        )
        .unwrap();
        let err = load_from(&dir, &[]).unwrap_err();
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(err.contains("does not match code 2"));
    }

    #[test]
    fn a_parse_observe_takes_only_accepted_or_rejected() {
        let dir = std::env::temp_dir().join(format!("validity-parse-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("SC3001.toml"),
            "code = 3001\nclaim = \"c\"\n[snippet]\nscript = \"a\"\n[fixed]\nscript = \"b\"\n[[observe]]\nkind = \"parse\"\nsnippet = \"rejected\"\nfixed = \"ok\"\n",
        )
        .unwrap();
        let err = load_from(&dir, &[]).unwrap_err();
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(err.contains("a parse observe takes"));
        assert!(err.contains("\"ok\""));
    }
}
