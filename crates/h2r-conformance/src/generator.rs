//! Seeded shell generation and mutation, adapted from rust-port conformance.

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
        s[..s.floor_char_boundary(4000)].to_string()
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seeded_generation_is_reproducible() {
        let seeds = vec!["echo $x".into()];
        let mut a = Rng::new(7);
        let mut b = Rng::new(7);
        for _ in 0..100 {
            assert_eq!(generate(&mut a, &seeds), generate(&mut b, &seeds));
        }
    }

    #[test]
    fn unicode_seeds_are_truncated_on_character_boundaries() {
        let seeds = vec!["€".repeat(2000)];
        let mut r = Rng::new(1);
        for _ in 0..100 {
            let script = generate(&mut r, &seeds);
            assert!(script.len() <= 4000);
        }
    }

    #[test]
    fn empty_seed_list_is_supported() {
        let mut r = Rng::new(3);
        for _ in 0..100 {
            let _ = generate(&mut r, &[]);
        }
    }
}
