//! Core-only JSON API shared by native parity tests and an import-free WASM ABI.

use serde::Deserialize;
use serde_json::{Value, json};
use shellcheck_rs::interface::{InsertionPoint, System};
use shellcheck_rs::{CheckSpec, Dialect, Severity};
use std::{collections::BTreeMap, rc::Rc};

/// Maximum serialized request size, including virtual source files.
pub const MAX_REQUEST_BYTES: usize = 16 * 1024 * 1024;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    script: String,
    #[serde(default = "default_filename")]
    filename: String,
    #[serde(default)]
    shell: Option<String>,
    #[serde(default)]
    files: BTreeMap<String, String>,
    #[serde(default)]
    check_sourced: bool,
    #[serde(default)]
    exclude: Vec<i64>,
    #[serde(default)]
    include: Option<Vec<i64>>,
    #[serde(default)]
    optional_checks: Vec<String>,
    #[serde(default)]
    extended_analysis: Option<bool>,
    #[serde(default)]
    severity: Option<String>,
}

fn default_filename() -> String {
    "script.sh".into()
}

struct VirtualFiles(BTreeMap<String, String>);

impl System for VirtualFiles {
    fn read_file(&self, external: Option<bool>, file: &str) -> Result<String, String> {
        if external == Some(false) {
            return Err("external-sources=false".into());
        }
        self.0
            .get(file)
            .cloned()
            .ok_or_else(|| format!("{file} was not supplied in files"))
    }

    fn find_source(&self, _: &str, _: Option<bool>, _: &[String], name: &str) -> String {
        name.to_owned()
    }
}

fn analyze(input: &[u8]) -> Result<Value, String> {
    if input.len() > MAX_REQUEST_BYTES {
        return Err("request exceeds 16 MiB".into());
    }
    let req: Request = serde_json::from_slice(input).map_err(|e| e.to_string())?;
    let shell = match req.shell.as_deref() {
        None => None,
        Some(s) => Some(Dialect::from_name(s).ok_or_else(|| format!("unsupported shell: {s}"))?),
    };
    let severity = match req.severity.as_deref() {
        None | Some("style") => Severity::StyleC,
        Some("info") => Severity::InfoC,
        Some("warning") => Severity::WarningC,
        Some("error") => Severity::ErrorC,
        Some(s) => return Err(format!("unsupported severity: {s}")),
    };
    let system = VirtualFiles(req.files);
    let spec = CheckSpec {
        script: req.script,
        filename: req.filename,
        shell_type_override: shell,
        check_sourced: req.check_sourced,
        ignore_rc: true,
        excluded_warnings: req.exclude,
        included_warnings: req.include,
        optional_checks: req.optional_checks,
        extended_analysis: req.extended_analysis,
        min_severity: severity,
        ..CheckSpec::default()
    };
    let result = shellcheck_rs::checker::check_script_with(Rc::new(system), &spec);
    let comments: Vec<_> = result.comments.iter().map(|c| {
        let fix = c.fix.as_ref().map(|f| json!({"replacements": f.replacements.iter().map(|r| json!({
            "file": r.start.file, "line": r.start.line, "column": r.start.column,
            "endLine": r.end.line, "endColumn": r.end.column,
            "replacement": r.string, "precedence": r.precedence,
            "insertionPoint": match r.insertion_point {
                InsertionPoint::InsertBefore => "beforeStart", InsertionPoint::InsertAfter => "afterEnd",
            }
        })).collect::<Vec<_>>() }));
        json!({"file": c.start.file, "line": c.start.line, "column": c.start.column,
            "endLine": c.end.line, "endColumn": c.end.column,
            "level": c.comment.severity.as_str(), "code": c.comment.code,
            "message": c.comment.message, "fix": fix})
    }).collect();
    Ok(json!({"comments": comments,
        "dataflowError": result.dataflow_error.map(|e| format!("{e:?}")),
        "sources": result.sources}))
}

/// Analyze a UTF-8 JSON request. Errors are returned as an `error` JSON object.
/// Diagnostic positions are the core's 1-based character columns (tabs expand
/// to eight-column stops), not UTF-8 byte or JavaScript UTF-16 offsets.
#[must_use]
pub fn check_json(input: &[u8]) -> Vec<u8> {
    let output = analyze(input).unwrap_or_else(|error| json!({"error": error}));
    // JSON values contain no fallible custom serializers.
    output.to_string().into_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(request: Value) -> Value {
        serde_json::from_slice(&check_json(request.to_string().as_bytes())).unwrap()
    }

    #[test]
    fn diagnostics_and_fixes_retain_core_positions() {
        let result = check(json!({"script": "#!/bin/sh\necho $value\n", "filename": "test.sh"}));
        let quote = result["comments"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["code"] == 2086)
            .unwrap();
        assert_eq!(quote["file"], "test.sh");
        assert_eq!(quote["line"], 2);
        assert_eq!(quote["column"], 6);
        assert_eq!(quote["endColumn"], 12);
        assert_eq!(quote["fix"]["replacements"].as_array().unwrap().len(), 2);
        assert!(result["dataflowError"].is_null());
    }

    #[test]
    fn only_supplied_files_are_read_and_state_does_not_leak() {
        let script = "#!/bin/sh\n. shared.sh\necho \"$shared\"\n";
        let with_file = check(json!({"script": script, "files": {"shared.sh": "shared=hello\n"}}));
        assert_eq!(with_file["comments"], json!([]));
        assert_eq!(with_file["sources"], json!(["shared.sh"]));
        let without_file = check(json!({"script": script}));
        assert!(
            without_file["comments"]
                .as_array()
                .unwrap()
                .iter()
                .any(|c| c["code"] == 1091)
        );
        assert_eq!(without_file["sources"], json!([]));
    }

    #[test]
    fn invalid_requests_are_errors_not_clean_results() {
        for input in [b"null".as_slice(), b"{}", b"{", b"\xff"] {
            let value: Value = serde_json::from_slice(&check_json(input)).unwrap();
            assert!(value["error"].is_string());
            assert!(value.get("comments").is_none());
        }
        assert!(check(json!({"script": "true", "shell": "fish"}))["error"].is_string());
    }

    #[test]
    fn an_added_dialect_is_checked_as_its_floor() {
        let zsh = check(json!({"script": "[[ -n $1 ]]\n", "shell": "zsh"}));
        assert_eq!(zsh["comments"], json!([]));
        let posh = check(json!({"script": "[[ -n $1 ]]\n", "shell": "posh"}));
        let codes: Vec<_> = posh["comments"]
            .as_array()
            .unwrap()
            .iter()
            .map(|c| c["code"].clone())
            .collect();
        assert_eq!(codes, vec![json!(3010)]);
    }
}

#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code)] // Export names only; there are no unsafe blocks or raw reads.
mod abi {
    use std::cell::RefCell;

    #[derive(Default)]
    struct Buffers {
        input: Vec<u8>,
        output: Vec<u8>,
        prepared: bool,
    }
    thread_local! { static BUFFERS: RefCell<Buffers> = RefCell::default(); }

    #[unsafe(no_mangle)]
    pub extern "C" fn sc_abi_version() -> u32 {
        1
    }

    // Hosts may write exactly `len` bytes at this pointer, until sc_check.
    // Returning zero rejects oversized requests and invalidates old input.
    #[unsafe(no_mangle)]
    pub extern "C" fn sc_prepare(len: u32) -> u32 {
        BUFFERS.with_borrow_mut(|b| {
            b.prepared = false;
            b.output.clear();
            if len as usize > super::MAX_REQUEST_BYTES {
                return 0;
            }
            b.input.resize(len as usize, 0);
            b.prepared = true;
            b.input.as_mut_ptr() as u32
        })
    }

    #[unsafe(no_mangle)]
    pub extern "C" fn sc_check() -> u32 {
        BUFFERS.with_borrow_mut(|b| {
            b.output = if b.prepared {
                super::check_json(&b.input)
            } else {
                br#"{"error":"call sc_prepare before sc_check"}"#.to_vec()
            };
            b.prepared = false;
            b.output.as_ptr() as u32
        })
    }

    #[unsafe(no_mangle)]
    pub extern "C" fn sc_output_len() -> u32 {
        BUFFERS.with_borrow(|b| b.output.len() as u32)
    }

    #[unsafe(no_mangle)]
    pub extern "C" fn sc_reset() {
        BUFFERS.with_borrow_mut(|b| *b = Buffers::default());
    }
}
