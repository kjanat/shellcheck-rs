//! Differential fuzzing: shell nobody wrote a test for.
//!
//! `gate` replays ShellCheck's own properties, so it can only ever prove that
//! the port handles what upstream already thought to test. Divergences have
//! shipped straight through a green gate: a check that fired SC2066 on
//! `for x in "a b"`, three codes emitted twice from two modules, five checks
//! missing outright. None of those shapes appear in the property corpus.
//!
//! This module produces shapes that are not in any corpus — generated from a
//! shell-flavoured grammar, and mutated out of the property scripts — runs both
//! tools over them in every dialect, and reports any difference in the full
//! json1 payload. Each distinct divergence is then shrunk, by removing lines
//! and then character runs, to the smallest input that still diverges, so the
//! report is a set of minimal reproducers rather than a pile of noise.

use std::collections::HashSet;

use crate::corpus;
use crate::oracle::Oracle;
use crate::{Args, CommentKey, keys_match, port_keys, render_keys};

/// A divergence as the search records it: signature, dialect, the input that
/// produced it, and both sides' answers.
type Finding = (
    String,
    Option<String>,
    String,
    Vec<CommentKey>,
    Vec<CommentKey>,
);

// ---------------------------------------------------------------------------
// Deterministic RNG (xorshift64*), so a seed reproduces a run exactly.
// ---------------------------------------------------------------------------
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(2685821657736338717).max(1))
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(2685821657736338717)
    }
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() % n as u64) as usize
        }
    }
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + self.below(hi - lo + 1)
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
    /// True with probability `num/100`.
    fn chance(&mut self, pct: u64) -> bool {
        self.next_u64() % 100 < pct
    }
}

// ---------------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------------
const SHELLS: [Option<&str>; 6] = [
    None,
    Some("bash"),
    Some("sh"),
    Some("dash"),
    Some("ksh"),
    Some("busybox"),
];

const WORDS: [&str; 9] = [
    "foo", "bar", "$var", "\"$var\"", "'lit'", "*.txt", "$(cmd)", "`cmd`", "--",
];

const EXPANSIONS: [&str; 24] = [
    "$var",
    "${var}",
    "\"$var\"",
    "${var:-def}",
    "${var:1:2}",
    "${var//a/b}",
    "${var^^}",
    "${!var}",
    "${#var}",
    "${arr[@]}",
    "\"${arr[@]}\"",
    "${arr[*]}",
    "$@",
    "\"$@\"",
    "$*",
    "$?",
    "$$",
    "$!",
    "$(cmd)",
    "`cmd`",
    "$((1+2))",
    "$[1+2]",
    "$(<file)",
    "${!pre@}",
];

const CMDS: [&str; 40] = [
    "echo", "printf", "read", "eval", "export", "local", "declare", "readonly", "unset", "trap",
    "alias", "source", ".", "cd", "exit", "return", "set", "let", "getopts", "grep", "sed", "awk",
    "find", "tr", "ls", "rm", "cp", "mv", "ln", "mkdir", "chmod", "xargs", "sudo", "su", "ssh",
    "which", "expr", "test", "time", "builtin",
];

const REDIRS: [&str; 13] = [
    "> out",
    ">> out",
    "< in",
    "2> err",
    "2>&1",
    "&> both",
    ">& both",
    "<<< 'here'",
    "3< f",
    "{fd}> f",
    "10> f",
    "> /dev/null",
    "> /dev/tcp/h/80",
];

const TEST_OPS: [&str; 12] = [
    "-eq", "-ne", "-lt", "-gt", "=", "==", "!=", "=~", "<", ">", "-nt", "-ef",
];

const UNARY_OPS: [&str; 10] = ["-z", "-n", "-e", "-f", "-d", "-v", "-a", "-o", "-r", "-x"];

const SHEBANGS: [&str; 7] = [
    "#!/bin/sh",
    "#!/bin/bash",
    "#!/bin/dash",
    "#!/bin/ksh",
    "#!/usr/bin/env bash",
    "#!/bin/bash -e",
    "#!/bin/zsh",
];

const INSERTS: [&str; 33] = [
    "\"", "'", "`", "$", "\\", "{", "}", "(", ")", "[", "]", ";", "|", "&", "<", ">", "#", "\n",
    " ", "\t", "$(", "${", "$((", "[[", "]]", "done", "fi", "esac", "!", "*", "@", "+=", "--",
];

// ---------------------------------------------------------------------------
// Generation
// ---------------------------------------------------------------------------
fn word(r: &mut Rng, depth: usize) -> String {
    match r.below(100) {
        0..=34 => r.pick(&WORDS).to_string(),
        35..=64 => r.pick(&EXPANSIONS).to_string(),
        65..=74 => format!(
            "\"{}{}\"",
            r.pick(&EXPANSIONS),
            r.pick(&["", " x", "/y", "=z"])
        ),
        75..=81 => format!("'{}'", r.pick(&["a b", "$novar", "*"])),
        82..=87 => r
            .pick(&["{a,b}", "{1..3}", "[ab]*", "!(x)", "?(y)", "*"])
            .to_string(),
        88..=93 if depth < 2 => format!("$({})", simple(r, depth + 1)),
        _ => r
            .pick(&["-r", "-e", "-n", "--flag=val", "-abc"])
            .to_string(),
    }
}

fn condition(r: &mut Rng, depth: usize) -> String {
    let style = *r.pick(&["[", "[[", "test"]);
    let body = match r.below(100) {
        0..=39 => format!(
            " {} {} {}",
            word(r, depth),
            r.pick(&TEST_OPS),
            word(r, depth)
        ),
        40..=69 => format!(" {} {}", r.pick(&UNARY_OPS), word(r, depth)),
        70..=84 => format!(" {}", word(r, depth)),
        _ => format!(
            " {} {} {} {} {} {}",
            r.pick(&UNARY_OPS),
            word(r, depth),
            r.pick(&["-a", "-o", "&&", "||"]),
            word(r, depth),
            r.pick(&TEST_OPS),
            word(r, depth)
        ),
    };
    match style {
        "[" => format!("[{body} ]"),
        "[[" => format!("[[{body} ]]"),
        _ => format!("test{body}"),
    }
}

fn assignment(r: &mut Rng, depth: usize) -> String {
    let v = *r.pick(&["var", "x", "arr", "PATH", "IFS", "PS1"]);
    match r.below(100) {
        0..=14 => format!("{v}=({} {})", word(r, depth), word(r, depth)),
        15..=24 => format!("{v}+={}", word(r, depth)),
        25..=34 => format!("{v}[{}]={}", r.pick(&["0", "$i", "x"]), word(r, depth)),
        35..=44 => format!(
            "{} {v}={}",
            r.pick(&["local", "declare", "export", "readonly", "typeset"]),
            word(r, depth)
        ),
        _ => format!("{v}={}", word(r, depth)),
    }
}

fn simple(r: &mut Rng, depth: usize) -> String {
    let mut parts = vec![r.pick(&CMDS).to_string()];
    for _ in 0..r.below(4) {
        parts.push(word(r, depth));
    }
    if r.chance(25) {
        parts.push(r.pick(&REDIRS).to_string());
    }
    parts.join(" ")
}

fn pipeline(r: &mut Rng, depth: usize) -> String {
    let sep = *r.pick(&["|", "|&", "&&", "||"]);
    let n = r.range(1, 3);
    let cmds: Vec<String> = (0..n).map(|_| simple(r, depth)).collect();
    let mut s = cmds.join(&format!(" {sep} "));
    if r.chance(10) {
        s = format!("! {s}");
    }
    if r.chance(5) {
        s = format!("! ! {s}");
    }
    s
}

fn compound(r: &mut Rng, depth: usize) -> String {
    let body = stmt(r, depth + 1);
    match *r.pick(&[
        "if", "while", "until", "for", "forc", "case", "func", "sub", "group", "select", "arith",
        "coproc", "heredoc",
    ]) {
        "if" => {
            let els = if r.chance(40) {
                format!("else {}; ", stmt(r, depth + 1))
            } else {
                String::new()
            };
            format!("if {}; then {body}; {els}fi", condition(r, depth))
        }
        k @ ("while" | "until") => format!("{k} {}; do {body}; done", condition(r, depth)),
        "for" => {
            let n = r.range(1, 3);
            let items: Vec<String> = (0..n).map(|_| word(r, depth)).collect();
            format!(
                "for {} in {}; do {body}; done",
                r.pick(&["i", "f", "x"]),
                items.join(" ")
            )
        }
        "forc" => format!("for ((i=0; i<{}; i++)); do {body}; done", r.range(1, 9)),
        "case" => format!(
            "case {} in {}) {body};; esac",
            word(r, depth),
            r.pick(&["a", "*", "[ab]", "$x"])
        ),
        "func" => {
            let name = *r.pick(&["f", "foo-bar", "my_func", "a.b"]);
            if r.chance(50) {
                format!("{name}() {{ {body}; }}")
            } else {
                format!("function {name} {{ {body}; }}")
            }
        }
        "sub" => format!("( {body} )"),
        "group" => format!("{{ {body}; }}"),
        "select" => format!("select x in {}; do {body}; done", word(r, depth)),
        "arith" => r
            .pick(&[
                "(( i++ ))",
                "(( x = 1 ))",
                "(( a**b ))",
                "(( 1.5*2 ))",
                "(( 010 + 1 ))",
                "let i=i+1",
                "let x++",
            ])
            .to_string(),
        "coproc" => format!("coproc {} {{ {body}; }}", r.pick(&["foo", "NAME"])),
        _ => format!(
            "cat <<{}\n{}\nEOF",
            r.pick(&["EOF", "'EOF'", "\"EOF\"", "-EOF"]),
            r.pick(&["plain", "$var", "`cmd`"])
        ),
    }
}

fn stmt(r: &mut Rng, depth: usize) -> String {
    if depth > 2 {
        return simple(r, depth);
    }
    match r.below(100) {
        0..=31 => pipeline(r, depth),
        32..=51 => assignment(r, depth),
        52..=59 => simple(r, depth),
        _ => compound(r, depth),
    }
}

fn script(r: &mut Rng) -> String {
    let mut lines: Vec<String> = Vec::new();
    if r.chance(45) {
        lines.push(r.pick(&SHEBANGS).to_string());
    }
    if r.chance(8) {
        lines.push(format!(
            "# shellcheck {}",
            r.pick(&["disable=SC2086", "shell=bash", "disable=all", "source=lib"])
        ));
    }
    for _ in 0..r.range(1, 4) {
        lines.push(stmt(r, 0));
    }
    lines.join("\n") + "\n"
}

/// One input in the mix this module checks against the oracle: a mutated seed,
/// a generated script, or a generated script mutated again. Shared so other
/// modes measure the same population rather than inventing their own.
pub fn generate(r: &mut Rng, seeds: &[String]) -> String {
    let s = if r.chance(45) && !seeds.is_empty() {
        let base = r.pick(seeds).clone();
        mutate(r, &base, seeds)
    } else if r.chance(50) {
        script(r)
    } else {
        let g = script(r);
        mutate(r, &g, seeds)
    };
    if s.len() > 4000 {
        s[..4000].to_string()
    } else {
        s
    }
}

// ---------------------------------------------------------------------------
// Mutation
// ---------------------------------------------------------------------------
fn mutate(r: &mut Rng, s: &str, seeds: &[String]) -> String {
    let chars: Vec<char> = s.chars().collect();
    match r.below(8) {
        0 if !seeds.is_empty() => {
            // Splice: take the head of one script and the tail of another.
            let lines: Vec<&str> = s.lines().collect();
            let other_s = r.pick(seeds).clone();
            let other: Vec<&str> = other_s.lines().collect();
            if lines.is_empty() || other.is_empty() {
                return s.to_string();
            }
            let i = r.below(lines.len());
            let j = r.below(other.len());
            let mut out: Vec<&str> = lines[..i].to_vec();
            out.extend_from_slice(&other[j..]);
            out.join("\n")
        }
        1 if !seeds.is_empty() => format!("{}\n{}", s.trim_end(), r.pick(seeds)),
        2 if !chars.is_empty() => {
            let i = r.below(chars.len() + 1);
            let mut out: String = chars[..i].iter().collect();
            out.push_str(r.pick(&INSERTS));
            out.extend(chars[i..].iter());
            out
        }
        3 if chars.len() > 1 => {
            let i = r.below(chars.len());
            let n = r.range(1, 6).min(chars.len() - i);
            chars[..i].iter().chain(chars[i + n..].iter()).collect()
        }
        4 => {
            let mut lines: Vec<String> = s.lines().map(str::to_string).collect();
            if lines.is_empty() {
                return s.to_string();
            }
            let i = r.below(lines.len());
            lines.insert(i, lines[i].clone());
            lines.join("\n")
        }
        5 if !chars.is_empty() => {
            let i = r.below(chars.len() + 1);
            let q = *r.pick(&["\"", "'", "`"]);
            let mut out: String = chars[..i].iter().collect();
            out.push_str(q);
            out.extend(chars[i..].iter());
            out
        }
        6 if !chars.is_empty() => {
            let i = r.below(chars.len());
            let mut out: String = chars[..i].iter().collect();
            out.push_str(r.pick(&INSERTS));
            out.extend(chars[i + 1..].iter());
            out
        }
        _ => {
            let inner = s.trim();
            match r.below(6) {
                0 => format!("f() {{\n{inner}\n}}\n"),
                1 => format!("if true; then\n{inner}\nfi\n"),
                2 => format!("while read -r x; do\n{inner}\ndone\n"),
                3 => format!("(\n{inner}\n)\n"),
                4 => format!("case $x in a)\n{inner}\n;; esac\n"),
                _ => format!("echo \"$(\n{inner}\n)\"\n"),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Divergence identity
// ---------------------------------------------------------------------------
/// How one script's two answers differ, reduced to something groupable so a
/// single root cause is reported once instead of five hundred times.
fn signature(port: &[CommentKey], oracle: &[CommentKey], shell: Option<&str>) -> String {
    let pc: HashSet<i64> = port.iter().map(|k| k.code).collect();
    let oc: HashSet<i64> = oracle.iter().map(|k| k.code).collect();
    let mut missing: Vec<i64> = oc.difference(&pc).copied().collect();
    let mut extra: Vec<i64> = pc.difference(&oc).copied().collect();
    missing.sort_unstable();
    extra.sort_unstable();
    if missing.is_empty() && extra.is_empty() {
        // Same codes, different detail: group by which codes' details differ.
        let mut differing: Vec<i64> = port
            .iter()
            .zip(oracle)
            .filter(|(p, o)| p != o)
            .map(|(_, o)| o.code)
            .collect();
        differing.sort_unstable();
        differing.dedup();
        return format!("{shell:?}|detail|{differing:?}");
    }
    format!("{shell:?}|missing{missing:?}|extra{extra:?}")
}

// ---------------------------------------------------------------------------
// Shrinking
// ---------------------------------------------------------------------------
struct Shrinker<'a> {
    oracle: &'a Oracle,
    shell: Option<&'a str>,
    want: String,
}

impl Shrinker<'_> {
    fn diverges_the_same_way(&self, cand: &str) -> bool {
        if cand.trim().is_empty() {
            return false;
        }
        let Ok((ocomments, _)) = self.oracle.check_one(cand, self.shell) else {
            return false;
        };
        let ok = crate::oracle_keys(&ocomments);
        let name = format!("{}/x", self.oracle.dir().display());
        let pk = port_keys(cand, &name, self.shell);
        if keys_match(&pk, &ok) {
            return false;
        }
        signature(&pk, &ok, self.shell) == self.want
    }

    fn shrink(&self, start: &str) -> String {
        let mut cur = start.to_string();
        let mut budget = 200;
        // Whole lines first: the biggest wins, and keeps the result readable.
        let mut progress = true;
        while progress && budget > 0 {
            progress = false;
            let lines: Vec<String> = cur.lines().map(str::to_string).collect();
            for i in 0..lines.len() {
                if budget == 0 {
                    break;
                }
                budget -= 1;
                let mut cand: Vec<String> = lines.clone();
                cand.remove(i);
                let cand = cand.join("\n");
                if self.diverges_the_same_way(&cand) {
                    cur = cand;
                    progress = true;
                    break;
                }
            }
        }
        // Then character runs, coarse to fine.
        let mut size = (cur.len() / 4).max(1);
        while size >= 1 && budget > 0 {
            let mut i = 0;
            while i < cur.len() && budget > 0 {
                budget -= 1;
                let end = (i + size).min(cur.len());
                if !cur.is_char_boundary(i) || !cur.is_char_boundary(end) {
                    i += 1;
                    continue;
                }
                let cand = format!("{}{}", &cur[..i], &cur[end..]);
                if self.diverges_the_same_way(&cand) {
                    cur = cand;
                } else {
                    i += size;
                }
            }
            size /= 2;
        }
        cur
    }
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------
pub fn run(args: &Args) -> Result<bool, String> {
    let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
    let seeds: Vec<String> = corpus::extract(&src)
        .map(|e| e.into_iter().map(|x| x.script).collect())
        .unwrap_or_default();
    let oracle = Oracle::new(args.oracle())?;
    println!(
        "{}",
        crate::oracle::verify(&oracle, &args.repo, args.any_oracle_version())?
    );
    let mut rng = Rng::new(args.seed.wrapping_add(1));

    let mut seen: HashSet<String> = HashSet::new();
    // Deviation ids already announced, so one class is reported once rather
    // than for every generated spelling of it.
    let mut sanctioned: HashSet<&'static str> = HashSet::new();
    let mut found: Vec<Finding> = Vec::new();
    let mut checked = 0usize;

    const ROUND: usize = crate::oracle::BATCH;
    let rounds = args.iterations.div_ceil(ROUND);
    'outer: for _ in 0..rounds {
        // Build a round of inputs, each with the dialect it will be checked in.
        let shell: Option<String> = if args.all_shells {
            None
        } else {
            rng.pick(&SHELLS).map(str::to_string)
        };
        let mut batch: Vec<(String, String)> = Vec::with_capacity(ROUND);
        let mut sources: Vec<String> = Vec::with_capacity(ROUND);
        for _ in 0..ROUND {
            let s = if rng.chance(45) && !seeds.is_empty() {
                let base = rng.pick(&seeds).clone();
                mutate(&mut rng, &base, &seeds)
            } else if rng.chance(50) {
                script(&mut rng)
            } else {
                let g = script(&mut rng);
                mutate(&mut rng, &g, &seeds)
            };
            let s = if s.len() > 4000 {
                s[..4000].to_string()
            } else {
                s
            };
            batch.push((oracle.name(), s.clone()));
            sources.push(s);
        }

        let by_name = oracle.check(&batch, shell.as_deref())?;
        for ((name, _), source) in batch.iter().zip(&sources) {
            checked += 1;
            let Some(ocomments) = by_name.get(name) else {
                continue;
            };
            let ok = crate::oracle_keys(ocomments);
            let path = oracle.dir().join(name);
            let pk = port_keys(source, &path.to_string_lossy(), shell.as_deref());
            if keys_match(&pk, &ok) {
                continue;
            }
            // A difference the port is entitled to (see `deviations`) is not a
            // finding, however the generator spelled it.
            if let Some(d) = crate::deviations::sanctioned(source, shell.as_deref(), &pk, &ok) {
                if sanctioned.insert(d.id) && !args.quiet {
                    println!("sanctioned deviation [{}]: {}", d.id, d.what);
                }
                continue;
            }
            let sig = signature(&pk, &ok, shell.as_deref());
            if !seen.insert(sig.clone()) {
                continue;
            }
            if !args.quiet {
                println!("found divergence {} ({sig})", found.len() + 1);
            }
            found.push((sig, shell.clone(), source.clone(), pk, ok));
            if found.len() >= args.max_findings {
                break 'outer;
            }
        }
    }

    println!(
        "\nfuzz: {checked} inputs checked, {} distinct divergences",
        found.len()
    );
    for (sig, shell, source, _, _) in &found {
        let sh = shell.as_deref();
        let sm = Shrinker {
            oracle: &oracle,
            shell: sh,
            want: sig.clone(),
        };
        let small = sm.shrink(source);
        let (ocomments, oexit) = oracle.check_one(&small, sh)?;
        let ok = crate::oracle_keys(&ocomments);
        let path = oracle.dir().join("x");
        let pk = port_keys(&small, &path.to_string_lossy(), sh);
        println!("\n--- {sig}");
        println!("  script: {:?}", small);
        println!("  oracle (exit {oexit}): {}", render_keys(&ok));
        println!("  port:   {}", render_keys(&pk));
    }
    crate::report_crashes(&oracle, args.max_findings, args.quiet);
    Ok(found.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rng_is_deterministic_for_a_seed() {
        let a: Vec<usize> = (0..8).map(|_| Rng::new(42).below(1000)).collect();
        let b: Vec<usize> = (0..8).map(|_| Rng::new(42).below(1000)).collect();
        assert_eq!(a, b);
        let mut r1 = Rng::new(7);
        let mut r2 = Rng::new(7);
        let s1: Vec<usize> = (0..20).map(|_| r1.below(100)).collect();
        let s2: Vec<usize> = (0..20).map(|_| r2.below(100)).collect();
        assert_eq!(s1, s2);
    }

    #[test]
    fn rng_below_stays_in_range() {
        let mut r = Rng::new(3);
        for _ in 0..500 {
            assert!(r.below(10) < 10);
        }
        assert_eq!(r.below(0), 0);
    }

    #[test]
    fn generated_scripts_are_non_empty() {
        let mut r = Rng::new(1);
        for _ in 0..50 {
            assert!(!script(&mut r).trim().is_empty());
        }
    }

    #[test]
    fn mutation_of_empty_seed_list_is_safe() {
        let mut r = Rng::new(5);
        for _ in 0..50 {
            let _ = mutate(&mut r, "echo hi\n", &[]);
        }
    }

    #[test]
    fn signature_groups_by_code_sets() {
        let k = |code| CommentKey {
            line: 1,
            column: 1,
            end_line: 1,
            end_column: 1,
            level: "warning".into(),
            code,
            message: "m".into(),
            fix: None,
        };
        let a = signature(&[k(2086)], &[], Some("sh"));
        let b = signature(&[k(2086)], &[], Some("sh"));
        assert_eq!(a, b);
        let c = signature(&[], &[k(2086)], Some("sh"));
        assert_ne!(a, c, "extra and missing must not collide");
    }
}
