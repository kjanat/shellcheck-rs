use std::path::Path;

use schemars::generate::SchemaSettings;
use schemars::{JsonSchema, Schema};
use serde_json::Value;
use shellcheck_cli::formatter::json1;
use shellcheck_cli::oracle::UpstreamPin;

use crate::validity::{matrix, outcomes, sources, spec};

pub const DIR: &str = "schemas";
const BASE: &str = "https://raw.githubusercontent.com/kjanat/shellcheck-rs/master/schemas";

struct Entry {
    name: &'static str,
    title: &'static str,
    schema: fn() -> Schema,
}

const ENTRIES: [Entry; 7] = [
    Entry {
        name: "validity-sources",
        title: "Validity matrix sources",
        schema: input::<sources::Sources>,
    },
    Entry {
        name: "validity-matrix",
        title: "Validity matrix",
        schema: input::<matrix::Matrix>,
    },
    Entry {
        name: "validity-outcomes",
        title: "Validity matrix outcomes",
        schema: input::<outcomes::Outcomes>,
    },
    Entry {
        name: "validity-spec",
        title: "Validity spec",
        schema: input::<spec::Spec>,
    },
    Entry {
        name: "upstream-pin",
        title: "Upstream ShellCheck pin",
        schema: input::<UpstreamPin>,
    },
    Entry {
        name: "wasm-request",
        title: "shellcheck-wasm request",
        schema: input::<shellcheck_wasm::Request>,
    },
    Entry {
        name: "json1-output",
        title: "rshellcheck json1 output",
        schema: output::<json1::Output>,
    },
];

fn input<T: JsonSchema>() -> Schema {
    SchemaSettings::draft2020_12()
        .into_generator()
        .into_root_schema_for::<T>()
}

fn output<T: JsonSchema>() -> Schema {
    SchemaSettings::draft2020_12()
        .for_serialize()
        .into_generator()
        .into_root_schema_for::<T>()
}

fn render(entry: &Entry) -> Result<String, String> {
    let mut value = Value::from((entry.schema)());
    let Value::Object(map) = &mut value else {
        return Err(format!("{}: the schema is not an object", entry.name));
    };
    map.insert(
        "$id".to_string(),
        Value::String(format!("{BASE}/{}.schema.json", entry.name)),
    );
    map.insert("title".to_string(), Value::String(entry.title.to_string()));
    serde_json::to_string_pretty(&json_schema_sort::sorted_schema(value))
        .map(|text| text + "\n")
        .map_err(|e| format!("{}: {e}", entry.name))
}

pub fn write_to(dir: &Path) -> Result<(), String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in &ENTRIES {
        let path = dir.join(format!("{}.schema.json", entry.name));
        std::fs::write(&path, render(entry)?).map_err(|e| format!("{}: {e}", path.display()))?;
        println!("wrote {}", path.display());
    }
    Ok(())
}

pub fn run() -> Result<bool, String> {
    write_to(Path::new(DIR)).map(|()| true)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn committed(name: &str) {
        let entry = ENTRIES.iter().find(|e| e.name == name).unwrap();
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(DIR)
            .join(format!("{name}.schema.json"));
        let written = std::fs::read_to_string(&path).unwrap();
        assert_eq!(render(entry).unwrap(), written, "run `cargo schemas`");
    }

    #[test]
    fn the_validity_sources_schema_is_committed() {
        committed("validity-sources");
    }

    #[test]
    fn the_validity_matrix_schema_is_committed() {
        committed("validity-matrix");
    }

    #[test]
    fn the_validity_outcomes_schema_is_committed() {
        committed("validity-outcomes");
    }

    #[test]
    fn the_validity_spec_schema_is_committed() {
        committed("validity-spec");
    }

    #[test]
    fn validity_specs_require_observations_and_constrain_parse_results() {
        let schema = Value::from(input::<spec::Spec>());
        assert_eq!(schema["properties"]["observe"]["minItems"], 1);
        let observe = &schema["$defs"]["Observe"];
        assert_eq!(observe["if"]["properties"]["kind"]["const"], "parse");
        assert_eq!(observe["if"]["required"], serde_json::json!(["kind"]));
        for field in ["snippet", "fixed"] {
            assert_eq!(
                observe["then"]["properties"][field]["enum"],
                serde_json::json!(["accepted", "rejected"])
            );
            assert!(observe["properties"][field].get("enum").is_none());
        }
    }

    #[test]
    fn validity_sources_require_versions_argv_and_their_kind_location() {
        let schema = Value::from(input::<sources::Sources>());
        let source = &schema["$defs"]["Source"];
        for field in ["versions", "argv"] {
            assert_eq!(source["properties"][field]["minItems"], 1);
        }
        let conditions = source["allOf"].as_array().unwrap();
        assert_eq!(conditions.len(), 2);
        assert_eq!(
            conditions[0]["if"]["properties"]["kind"]["enum"],
            serde_json::json!(["tarball", "image"])
        );
        assert_eq!(conditions[1]["if"]["properties"]["kind"]["const"], "git");
        for (condition, fields) in [
            (&conditions[0], &["url"][..]),
            (&conditions[1], &["repo", "tag"][..]),
        ] {
            assert_eq!(condition["if"]["required"], serde_json::json!(["kind"]));
            assert_eq!(condition["then"]["required"], serde_json::json!(fields));
            for field in fields {
                assert_eq!(condition["then"]["properties"][field]["minLength"], 1);
            }
        }
    }

    #[test]
    fn the_upstream_pin_schema_is_committed() {
        committed("upstream-pin");
    }

    #[test]
    fn the_wasm_request_schema_is_committed() {
        committed("wasm-request");
    }

    #[test]
    fn the_json1_output_schema_is_committed() {
        committed("json1-output");
    }

    #[test]
    fn every_hand_written_validity_file_names_its_schema() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut files = vec![(
            root.join(crate::validity::SOURCES),
            "#:schema ../schemas/validity-sources.schema.json\n",
        )];
        for entry in std::fs::read_dir(root.join(crate::validity::SPECS)).unwrap() {
            files.push((
                entry.unwrap().path(),
                "#:schema ../../schemas/validity-spec.schema.json\n",
            ));
        }
        assert!(files.len() > 1);
        for (path, header) in files {
            let text = std::fs::read_to_string(&path).unwrap();
            assert!(
                text.starts_with(header),
                "{} lacks {header:?}",
                path.display()
            );
        }
    }

    #[test]
    fn a_second_run_rewrites_nothing() {
        let dir = std::env::temp_dir().join(format!("schemas-{}", std::process::id()));
        let read = || {
            let mut files: Vec<_> = std::fs::read_dir(&dir)
                .unwrap()
                .map(|e| {
                    let path = e.unwrap().path();
                    let text = std::fs::read_to_string(&path).unwrap();
                    (path, text)
                })
                .collect();
            files.sort();
            files
        };
        write_to(&dir).unwrap();
        let first = read();
        write_to(&dir).unwrap();
        let second = read();
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(first.len(), ENTRIES.len());
        assert_eq!(first, second);
    }
}
