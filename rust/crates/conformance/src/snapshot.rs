//! Characterization testing: freeze what the port *does*, so a refactor that
//! changes it says so.
//!
//! `gate` and `fuzz` ask whether the port agrees with the oracle. During a
//! refactor that is the wrong question: the port does not agree with the oracle
//! everywhere yet (`DIVERGENCES.md`), so "still diverges the same way" is
//! success and a comparison against the oracle cannot express it. The question
//! a refactor needs answered is narrower and stricter: *did any observable
//! behaviour change at all?*
//!
//! So this records the port's own answer for every input in a fixed corpus, and
//! fails on any difference. It needs no oracle, runs in seconds, and covers the
//! divergences too -- which is exactly where an oracle-based check is blind.
//!
//! The file is line-per-input and sorted, so `git diff` on it reads as a list of
//! behaviour changes: the codes are spelled out next to the payload hash that
//! actually decides the comparison.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::{Args, port_keys};

/// The corpus a snapshot covers, as (label, script) pairs.
///
/// Two sources, for two different kinds of coverage: every upstream property
/// script (what the checks are *for*), and a deterministic slice of the
/// generator (the parse-recovery paths no property reaches). Both are derived,
/// so nothing here can go stale against the sources.
fn corpus_for(args: &Args) -> Result<Vec<(String, String)>, String> {
    let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
    let coverage = crate::corpus::coverage(&src)?;
    let mut out: Vec<(String, String)> = coverage
        .entries
        .iter()
        .map(|e| (e.id.clone(), e.script.clone()))
        .collect();
    let seeds: Vec<String> = out.iter().map(|(_, s)| s.clone()).collect();
    for (i, s) in crate::fuzz::sample_scripts(&seeds, args.seed, args.iterations)
        .into_iter()
        .enumerate()
    {
        out.push((format!("gen/{}/{i:05}", args.seed), s));
    }
    Ok(out)
}

/// FNV-1a of a string. Not a digest, just a compact identity for a payload.
fn fnv(s: &str) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.as_bytes() {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{h:016x}")
}

/// One input's recorded behaviour: the exact payload hash, and a readable
/// summary of it so a diff of the file is worth reading.
struct Entry {
    payload: String,
    summary: String,
}

/// Run the port over every dialect it can be asked for, so a change that only
/// shows in one of them cannot hide.
const DIALECTS: [Option<&str>; 6] = [
    None,
    Some("bash"),
    Some("sh"),
    Some("dash"),
    Some("ksh"),
    Some("busybox"),
];

fn record(script: &str) -> Entry {
    let mut payload = String::new();
    let mut messages = String::new();
    let mut codes: Vec<String> = Vec::new();
    for shell in DIALECTS {
        let keys = port_keys(script, "-", shell);
        let _ = write!(payload, "[{}]", shell.unwrap_or("-"));
        for k in &keys {
            // Everything a user can observe, in the order they see it.
            let _ = write!(
                payload,
                "{}:{}:{}:{}:{}:{}:{}:{:?};",
                k.code, k.level, k.line, k.column, k.end_line, k.end_column, k.message, k.fix
            );
            messages.push_str(&k.message);
            // The summary carries code and span, so the common changes (a check
            // that stops firing, a span that moves) are legible in the diff
            // rather than only in the hash.
            codes.push(format!("{}@{}:{}", k.code, k.line, k.column));
        }
    }
    codes.sort_unstable();
    codes.dedup();
    Entry {
        payload: fnv(&payload),
        // A message-only change would otherwise move nothing but the payload
        // hash, so its own short hash rides along.
        summary: format!("{} msg:{}", codes.join(","), &fnv(&messages)[..8]),
    }
}

fn build(args: &Args) -> Result<BTreeMap<String, Entry>, String> {
    let mut map = BTreeMap::new();
    for (label, script) in corpus_for(args)? {
        // The script is part of the key: an input that changed is a different
        // input, reported as added/removed rather than as a behaviour change.
        let key = format!("{label} {}", fnv(&script));
        map.insert(key, record(&script));
    }
    Ok(map)
}

fn path(args: &Args) -> std::path::PathBuf {
    std::path::Path::new(&args.repo).join("rust/snapshot.txt")
}

fn serialize(map: &BTreeMap<String, Entry>) -> String {
    let mut s = String::new();
    let _ = writeln!(
        s,
        "# Behaviour of the Rust port, frozen. Regenerate: conformance snapshot --write"
    );
    let _ = writeln!(
        s,
        "# <property-or-generated id> <input hash> <output hash> <codes seen, any dialect>"
    );
    for (k, e) in map {
        let _ = writeln!(s, "{k} {} {}", e.payload, e.summary);
    }
    s
}

fn parse(text: &str) -> BTreeMap<String, (String, String)> {
    let mut map = BTreeMap::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        // `<id> <input hash> <output hash> <summary...>`: split from the left,
        // because the summary itself contains spaces.
        let mut it = line.splitn(4, ' ');
        let id = it.next().unwrap_or("");
        let input = it.next().unwrap_or("");
        let payload = it.next().unwrap_or("").to_string();
        let summary = it.next().unwrap_or("").to_string();
        map.insert(format!("{id} {input}"), (payload, summary));
    }
    map
}

/// Write or check the snapshot. `--write` re-freezes; otherwise any difference
/// is an error, with the changed entries spelled out.
pub fn run(args: &Args) -> Result<bool, String> {
    let current = build(args)?;
    let file = path(args);
    if args.write {
        std::fs::write(&file, serialize(&current))
            .map_err(|e| format!("{}: {e}", file.display()))?;
        println!(
            "snapshot: wrote {} entries to {}",
            current.len(),
            file.display()
        );
        return Ok(true);
    }
    let text = std::fs::read_to_string(&file).map_err(|e| {
        format!(
            "{}: {e}\n  Create it first: conformance snapshot --write",
            file.display()
        )
    })?;
    let previous = parse(&text);

    let mut changed: Vec<(&String, &str, &str)> = Vec::new();
    let mut added: Vec<&String> = Vec::new();
    for (k, e) in &current {
        match previous.get(k) {
            None => added.push(k),
            Some((payload, summary)) => {
                if *payload != e.payload {
                    changed.push((k, summary, &e.summary));
                }
            }
        }
    }
    let removed: Vec<&String> = previous
        .keys()
        .filter(|k| !current.contains_key(*k))
        .collect();

    if !args.quiet {
        for (k, was, now) in changed.iter().take(args.max_findings) {
            println!("CHANGED {k}");
            println!("  was: {was}");
            println!("  now: {now}");
        }
        if changed.len() > args.max_findings {
            println!("... and {} more", changed.len() - args.max_findings);
        }
        for k in added.iter().take(5) {
            println!("ADDED   {k}");
        }
        for k in removed.iter().take(5) {
            println!("REMOVED {k}");
        }
    }
    println!(
        "snapshot: {} entries, {} changed, {} added, {} removed",
        current.len(),
        changed.len(),
        added.len(),
        removed.len()
    );
    if !added.is_empty() || !removed.is_empty() {
        println!(
            "  (added/removed entries mean the corpus moved, not the port: \
             re-freeze with --write once that is expected)"
        );
    }
    Ok(changed.is_empty())
}
