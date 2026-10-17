use std::collections::BTreeMap;
use std::path::Path;

use schemars::JsonSchema;
use serde::Deserialize;

#[derive(Deserialize, JsonSchema, Debug)]
#[serde(deny_unknown_fields)]
pub struct Sources {
    pub defaults: Defaults,
    pub shell: BTreeMap<String, Source>,
}

#[derive(Deserialize, JsonSchema, Debug)]
#[serde(deny_unknown_fields)]
pub struct Defaults {
    pub base: String,
    pub parse: Vec<String>,
}

#[derive(Deserialize, JsonSchema, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
    Tarball,
    Git,
    Crate,
    Image,
}

#[derive(Deserialize, JsonSchema, Debug)]
#[serde(deny_unknown_fields)]
#[schemars(extend("allOf" = [
    {
        "if": { "properties": { "kind": { "enum": ["tarball", "image"] } }, "required": ["kind"] },
        "then": { "properties": { "url": { "minLength": 1 } }, "required": ["url"] }
    },
    {
        "if": { "properties": { "kind": { "const": "git" } }, "required": ["kind"] },
        "then": {
            "properties": { "repo": { "minLength": 1 }, "tag": { "minLength": 1 } },
            "required": ["repo", "tag"]
        }
    }
]))]
pub struct Source {
    pub kind: Kind,
    #[serde(default)]
    pub url: String,
    #[serde(default)]
    pub repo: String,
    #[serde(default)]
    pub tag: String,
    #[schemars(length(min = 1))]
    pub versions: Vec<String>,
    #[schemars(length(min = 1))]
    pub argv: Vec<String>,
    pub parse: Option<Vec<String>>,
    #[serde(default)]
    pub shipped: bool,
    #[serde(default)]
    pub vm: bool,
    pub dialect: Option<String>,
    pub image: Option<String>,
    pub base: Option<String>,
}

pub fn load() -> Result<Sources, String> {
    load_from(Path::new(super::SOURCES))
}

pub fn load_from(path: &Path) -> Result<Sources, String> {
    let shown = path.display();
    let text = std::fs::read_to_string(path).map_err(|e| format!("{shown}: {e}"))?;
    let sources: Sources = toml::from_str(&text).map_err(|e| format!("{shown}: {e}"))?;
    for (name, source) in &sources.shell {
        let missing = match source.kind {
            Kind::Tarball | Kind::Image => source.url.is_empty(),
            Kind::Git => source.repo.is_empty() || source.tag.is_empty(),
            Kind::Crate => false,
        };
        if missing {
            return Err(format!("{shown}: shell.{name} lacks its source location"));
        }
        if source.versions.is_empty() || source.argv.is_empty() {
            return Err(format!("{shown}: shell.{name} needs versions and argv"));
        }
    }
    Ok(sources)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_checked_in_sources_parse() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(crate::validity::SOURCES);
        let sources = load_from(&path).unwrap();
        assert!(sources.shell["bash"].shipped);
        assert_eq!(sources.shell["zsh-sh"].image.as_deref(), Some("zsh"));
    }

    #[test]
    fn a_git_source_without_a_tag_is_rejected() {
        let dir = std::env::temp_dir().join(format!("validity-sources-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("sources.toml");
        std::fs::write(
            &path,
            "[defaults]\nbase = \"b\"\nparse = [\"-n\"]\n[shell.x]\nkind = \"git\"\nrepo = \"r\"\nversions = [\"1\"]\nargv = [\"x\"]\n",
        )
        .unwrap();
        let err = load_from(&path).unwrap_err();
        std::fs::write(
            &path,
            "[defaults]\nbase = \"b\"\nparse = [\"-n\"]\n[shell.x]\nkind = \"image\"\nvm = true\nversions = [\"1\"]\nargv = [\"sh\"]\n",
        )
        .unwrap();
        let image_err = load_from(&path).unwrap_err();
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(
            image_err.contains("lacks its source location"),
            "{image_err}"
        );
        assert!(err.contains("shell.x lacks"));
    }
}
