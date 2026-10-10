"""Generate the benchmark corpus: deterministic, realistic-ish bash.

The scripts are assembled from a fixed set of building blocks
(functions, option parsing, loops over files, arrays, here-documents, traps, arithmetic, pipelines...)
with identifiers drawn from a seeded PRNG, so the corpus is reproducible byte for byte from this file
alone and never needs to be checked in.
Roughly a third of the blocks contain the classic ShellCheck findings
(unquoted expansions, `for f in $(ls)`, `[ $x == y ]`, `cat | grep` ...),
the rest are clean, so the analyser does real work without every line firing.

    corpus --out .bench/corpus [--seed 20260928]

Writes startup.sh, small.sh, medium.sh, large.sh, many/NNN.sh and corpus.json
(sha256 and line count per file, plus the seed).
"""

import argparse
import hashlib
import random
from collections.abc import Callable
from pathlib import Path
from typing import ClassVar, Literal

from bench.schema import CorpusFile, CorpusManifest, CorpusSource

SEED = 20260928

WORDS = [
    "config",
    "backup",
    "archive",
    "cache",
    "deploy",
    "target",
    "source",
    "build",
    "release",
    "stage",
    "log",
    "data",
    "user",
    "host",
    "port",
    "path",
    "file",
    "dir",
    "item",
    "entry",
    "queue",
    "job",
    "task",
    "worker",
    "index",
    "count",
    "total",
    "limit",
    "retry",
    "token",
    "bucket",
    "region",
    "cluster",
    "node",
    "volume",
    "image",
    "tag",
    "version",
    "branch",
    "commit",
    "repo",
    "package",
    "module",
    "service",
    "unit",
]


class Gen:
    rng: random.Random
    counter: int

    def __init__(self, rng: random.Random):
        self.rng = rng
        self.counter = 0

    def ident(self, kind: Literal["var", "VAR", "fn"] = "var"):
        self.counter += 1
        w = self.rng.choice(WORDS)
        if kind == "var":
            return f"{w}_{self.counter}"
        if kind == "VAR":
            return f"{w.upper()}_{self.counter}"
        return f"{w}_{self.rng.choice(WORDS)}_{self.counter}"

    def path(self):
        return "/".join([
            "",
            self.rng.choice(("var", "opt", "srv", "tmp", "etc")),
            self.rng.choice(WORDS),
            self.rng.choice(WORDS),
        ])

    # --- clean blocks -----------------------------------------------------

    def block_function_clean(self):
        f, a, b = self.ident("fn"), self.ident(), self.ident()
        return f"""
# {f}: copy one entry, keeping a marker of what was done
{f}() {{
    local {a}="$1"
    local {b}="${{2:-{self.path()}}}"
    if [ ! -e "${a}" ]; then
        printf 'missing: %s\\n' "${a}" >&2
        return 1
    fi
    mkdir -p "${b}"
    cp -- "${a}" "${b}/"
    printf '%s\\t%s\\n' "${a}" "$(date +%s)" >>"${b}/.done"
}}
"""

    def block_getopts(self):
        v, w, x = self.ident(), self.ident(), self.ident()
        return f"""
{v}=0
{w}=""
{x}=()
while getopts ":vo:h" opt; do
    case "$opt" in
        v) {v}=$(({v} + 1)) ;;
        o) {w}="$OPTARG" ;;
        h) usage; exit 0 ;;
        :) echo "option -$OPTARG needs an argument" >&2; exit 2 ;;
        \\?) echo "unknown option -$OPTARG" >&2; exit 2 ;;
    esac
done
shift $((OPTIND - 1))
{x}=("$@")
"""

    def block_case(self):
        v = self.ident()
        return f"""
case "${{{v}:-}}" in
    start|up)
        echo "starting"
        ;;
    stop|down)
        echo "stopping"
        ;;
    restart)
        "$0" stop && "$0" start
        ;;
    *)
        echo "usage: $0 {{start|stop|restart}}" >&2
        exit 64
        ;;
esac
"""

    def block_find_loop_clean(self):
        d, f = self.ident(), self.ident()
        return f'''
{d}="{self.path()}"
while IFS= read -r -d '' {f}; do
    [ -f "${f}" ] || continue
    gzip -9 -- "${f}"
done < <(find "${d}" -type f -name '*.log' -mtime +7 -print0)
'''

    def block_array_clean(self):
        a, i = self.ident(), self.ident()
        return f"""
declare -a {a}=(alpha beta "gamma delta" epsilon)
{a}+=("zeta")
for {i} in "${{{a}[@]}}"; do
    printf '[%s]\\n' "${i}"
done
echo "count: ${{#{a}[@]}}"
"""

    def block_heredoc(self):
        v, u = self.ident(), self.ident("VAR")
        return f'''
{u}="{self.rng.choice(WORDS)}"
cat <<EOF_{u}
Report for ${u}
  generated: $(date -u +%Y-%m-%dT%H:%M:%SZ)
  host:      $(hostname)
EOF_{u}
{v}=$(cat <<'EOT'
literal $not expanded ${{here}}
EOT
)
echo "${v}"
'''

    def block_trap(self):
        t = self.ident()
        return f"""
{t}=$(mktemp -d)
cleanup_{t}() {{
    rm -rf -- "${t}"
}}
trap cleanup_{t} EXIT INT TERM
"""

    def block_arith(self):
        a, b, c = self.ident(), self.ident(), self.ident()
        return f'''
{a}={self.rng.randint(1, 500)}
{b}={self.rng.randint(1, 50)}
{c}=$(( ({a} * {b}) % 97 + ({a} >> 2) ))
if (( {c} > 50 && {b} != 0 )); then
    {c}=$(( {c} / {b} ))
fi
echo "{c}=${c}"
'''

    def block_pipeline_clean(self):
        v = self.ident()
        return f'''
{v}=$(grep -c '^[[:alpha:]]' "{self.path()}.conf" || true)
sort -u "{self.path()}.txt" | awk -F: '{{ print $1 }}' | head -n "${{{v}:-10}}"
'''

    def block_read_loop(self):
        k, v, f = self.ident(), self.ident(), self.ident()
        return f'''
while IFS='=' read -r {k} {v}; do
    case "${k}" in
        ''|\\#*) continue ;;
    esac
    printf -v "cfg_${k}" '%s' "${v}"
done < "{self.path()}.env"
{f}="${{cfg_{self.rng.choice(WORDS)}:-default}}"
echo "${f}"
'''

    def block_test_clean(self):
        a, b = self.ident(), self.ident()
        return f"""
{a}="${{1:-}}"
{b}="${{2:-0}}"
if [[ -n "${a}" && "${b}" -gt 0 ]]; then
    echo "ok"
elif [[ "${a}" == *.tar.gz ]]; then
    tar -xzf "${a}"
else
    exit 1
fi
"""

    def block_subshell(self):
        d = self.ident()
        return f'''
(
    cd "{self.path()}" || exit 1
    {d}=$(git rev-parse --short HEAD 2>/dev/null || echo unknown)
    echo "at ${d}"
    make -j"$(nproc)" all
)
'''

    def block_printf_loop(self):
        i, n = self.ident(), self.ident()
        return f"""
{n}={self.rng.randint(3, 12)}
for (( {i} = 0; {i} < {n}; {i}++ )); do
    printf '%03d ' "${i}"
done
printf '\\n'
"""

    # --- blocks with findings ---------------------------------------------

    def block_unquoted(self):
        v, w = self.ident(), self.ident()
        return f"""
{v}={self.path()}
{w}="$1 $2"
echo $HOME/${v}
cp ${v}/* {self.path()}/
ls -l ${w}
"""

    def block_for_ls(self):
        f = self.ident()
        return f"""
for {f} in $(ls {self.path()}); do
    echo "found: ${f}"
    rm $f
done
"""

    def block_bad_test(self):
        v = self.ident()
        return rf"""
{v}=$1
if [ $\{{v}} == "yes" ]; then
    echo affirmative
fi
if [ -z $\{{v}} -o $\{{v}} = "no" ]; then
    echo negative
fi
[ "${v}" -eq 1 ] && echo one || echo other
""".replace("$\\{", "${")

    def block_useless_cat(self):
        v = self.ident()
        return f"""
{v}=`cat {self.path()}.txt | grep -v '^#' | wc -l`
echo "lines: ${v}"
cat {self.path()}.log | grep ERROR | cut -d' ' -f3
"""

    def block_read_noraw(self):
        ln = self.ident()
        return f"""
cat {self.path()}.list | while read {ln}; do
    echo $l
done
"""

    def block_assign_in_subshell(self):
        c, x = self.ident(), self.ident()
        return f"""
{c}=0
find {self.path()} -name '*.sh' | while read -r {x}; do
    {c}=$(({c} + 1))
done
echo "seen ${c} scripts"
"""

    def block_sc2181(self):
        return """
grep -q root /etc/passwd
if [ $? -eq 0 ]; then
    echo "root exists"
fi
"""

    def block_array_expansion_bug(self):
        a = self.ident()
        return f"""
{a}=(one two "three four")
for x in ${{{a}[*]}}; do
    echo "$x"
done
echo ${a}
"""

    def block_backticks_and_seq(self):
        i = self.ident()
        return f"""
for {i} in `seq 1 10`; do
    echo "iteration $i" >> /tmp/{self.rng.choice(WORDS)}.log
done
"""

    def block_return_and_exit(self):
        f = self.ident("fn")
        return f"""
{f}() {{
    local status
    status=$(false)
    [ $? -ne 0 ] && return 1
    echo "$status"
    return 0
}}
"""

    def block_glob_expansion(self):
        d = self.ident()
        return f'''
{d}="{self.path()}"
ls $d/*.txt | xargs rm -f
echo "cleaned $(ls $d | wc -l) files"
'''

    def block_sc2086_sc2046(self):
        return f"""
chmod 644 $(find {self.path()} -type f)
chown $USER:$GROUP {self.path()}
"""

    CLEAN: ClassVar[list[Callable[[Gen], str]]] = [
        block_function_clean,
        block_getopts,
        block_case,
        block_find_loop_clean,
        block_array_clean,
        block_heredoc,
        block_trap,
        block_arith,
        block_pipeline_clean,
        block_read_loop,
        block_test_clean,
        block_subshell,
        block_printf_loop,
    ]
    DIRTY: ClassVar[list[Callable[[Gen], str]]] = [
        block_unquoted,
        block_for_ls,
        block_bad_test,
        block_useless_cat,
        block_read_noraw,
        block_assign_in_subshell,
        block_sc2181,
        block_array_expansion_bug,
        block_backticks_and_seq,
        block_return_and_exit,
        block_glob_expansion,
        block_sc2086_sc2046,
    ]

    def script(self, target_lines: int, name: str) -> str:
        """Assemble a script: most blocks become the bodies of functions that
        main() calls in turn (the shape of real scripts of this size), and a
        few stay at top level, so both the per-function and the whole-script
        data-flow analyses get exercised without the latter exploding on
        thousands of lines of straight-line code."""
        out = [
            "#!/usr/bin/env bash",
            f"# {name}: generated by bench/corpus.py for the ShellCheck benchmark; do not edit",
            "set -euo pipefail",
            "",
            "usage() {",
            '    echo "usage: ${0##*/} [-v] [-o out] args..." >&2',
            "}",
        ]
        steps: list[str] = []
        lines = len(out)
        while lines < target_lines:
            pool = self.DIRTY if self.rng.random() < 0.35 else self.CLEAN
            block = self.rng.choice(pool)(self).strip("\n")
            # Here-documents cannot be indented into a function body, so they
            # stay at top level along with a fifth of the other blocks.
            if "<<" in block or self.rng.random() < 0.2:
                out.extend(("", block))
                lines += block.count("\n") + 2
            else:
                step = f"step_{len(steps) + 1}_{self.rng.choice(WORDS)}"
                body = "\n".join("    " + ln if ln else "" for ln in block.split("\n"))
                out.extend(("", f"{step}() {{", body, "}"))
                steps.append(step)
                lines += block.count("\n") + 4
        out.extend(("", "main() {"))
        for step in steps:
            out.append(f'    {step} "$@"')
        out.extend(('    echo "done"', "}", "", 'main "$@"', ""))
        return "\n".join(out)


class Args(argparse.Namespace):
    out: Path = Path()
    seed: int = SEED
    omarchy: bool = False
    omarchy_source: Path | None = None


def main(argv: list[str] | None = None):
    ap = argparse.ArgumentParser(description=(__doc__ or "").split("\n\n")[0])
    _ = ap.add_argument("--out", required=True, type=Path)
    _ = ap.add_argument("--seed", type=int, default=SEED)
    _ = ap.add_argument(
        "--omarchy", action="store_true", help="include the pinned Omarchy shell corpus"
    )
    _ = ap.add_argument(
        "--omarchy-source",
        type=Path,
        help="read an existing clean checkout at the pinned Omarchy commit",
    )
    args = ap.parse_args(argv, namespace=Args())
    if args.omarchy_source and not args.omarchy:
        raise ValueError("--omarchy-source requires --omarchy")

    rng = random.Random(args.seed)
    gen = Gen(rng)
    out = args.out
    (out / "many").mkdir(parents=True, exist_ok=True)

    files: dict[str, str] = {
        "startup.sh": "#!/bin/sh\ntrue\n",
        "small.sh": gen.script(150, "small.sh"),
        "medium.sh": gen.script(1500, "medium.sh"),
        "large.sh": gen.script(4000, "large.sh"),
    }
    for i in range(120):
        files[f"many/{i:03d}.sh"] = gen.script(rng.randint(30, 90), f"many/{i:03d}.sh")

    entries: dict[str, CorpusFile] = {}
    for rel, text in files.items():
        _ = (out / rel).write_text(text)
        entries[rel] = CorpusFile(
            sha256=hashlib.sha256(text.encode()).hexdigest(),
            lines=text.count("\n"),
            bytes=len(text.encode()),
        )
    sources: dict[str, CorpusSource] = {}
    if args.omarchy:
        from bench.omarchy import prepare

        imported, identity = prepare(out, args.omarchy_source)
        entries.update(imported)
        sources["omarchy"] = identity
    manifest = CorpusManifest(
        seed=args.seed,
        generator="src/bench/corpus.py",
        files=entries,
        sha256=hashlib.sha256(
            "".join(f"{k}:{entries[k].sha256}\n" for k in sorted(entries)).encode()
        ).hexdigest(),
        sources=sources,
    )
    _ = (out / "corpus.json").write_text(manifest.model_dump_json(indent=2) + "\n")
    total = sum(v.lines for v in entries.values())
    print(
        f"wrote {len(entries)} files, {total} lines, corpus sha256 {manifest.sha256[:16]} to {out}"
    )


if __name__ == "__main__":
    main()
