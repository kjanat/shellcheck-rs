#!/usr/bin/env python3
"""
Extract the ShellCheck conformance corpora from the Haskell `prop_` tests, with
complete provenance: EVERY `prop_*` definition in the source tree is accounted
for and categorised. Nothing is silently skipped.

ShellCheck's tests come in three behavioural layers, and this script emits one
corpus per layer plus a full manifest:

1. FULL-PIPELINE  (`verify` / `verifyNot` / `verifyTree` / `verifyNotTree` /
   `verifyCodes` / `check` / `checkWithIncludes`)
   -> a whole script run through the entire checker. These are validated against
      the Haskell oracle's `--format=json1` output.  => corpus.json

2. PARSER          (`isOk` / `isWarning` / `isNotOk`)
   -> `helper subParser "fragment"`: runs a *specific parser production* on a
      fragment and asserts it parses cleanly / with warnings / not at all. These
      validate the Rust parser's individual productions, not full-pipeline
      output.  => parser_corpus.json  (records the sub-parser and expectation)

3. FUNCTION UNIT   (`getLiteralString`, `getBracedReference`, `checkGetOpts`,
   `getPrintfFormats`, `executableFromShebang`, `determineShellTest`, `testFixes`,
   ... and wrappers `null`/`not`/`result`/`all`)
   -> assertions about intermediate helper functions. Captured RAW (the full
      right-hand side) for porting as Rust `#[test]`s alongside each function.
      Not decodable to a single script.  => fn_tests.json

String expressions for layers 1 and 2 are decoded EXACTLY by evaluating them in
GHCi (handles escapes, `unlines`, `intercalate`, `++`, gap notation); a prop
whose expression fails to compile is recorded as decoded=false rather than
dropped from the manifest.

Outputs (all under this directory):
  corpus.json         full-pipeline scripts (decoded)
  parser_corpus.json  parser-production fragments (decoded) + sub-parser + expect
  fn_tests.json       raw function-unit props for later porting
  prop_manifest.json  EVERY prop: {id, file, category, helper, decoded, ...}
"""

import json
import os
import re
import subprocess
import sys
from collections.abc import Iterator
from typing import NotRequired, TypedDict


class Classification(TypedDict):
    category: str
    helper: str
    target: NotRequired[str | None]
    polarity: NotRequired[str]
    expr: NotRequired[str]
    parser: NotRequired[str | None]
    expect: NotRequired[str]
    raw: NotRequired[str]


class ManifestEntry(Classification):
    id: str
    file: str
    script: NotRequired[str | None]
    decoded: NotRequired[bool]


SRC = os.environ.get("SC_SRC", "src")

FULL_ONE_ARG = {"verify", "verifyNot", "verifyTree", "verifyNotTree"}
PARSER_HELPERS = {"isOk", "isWarning", "isNotOk"}
POLARITY = {
    "verify": "positive",
    "verifyTree": "positive",
    "verifyCodes": "positive",
    "verifyNot": "negative",
    "verifyNotTree": "negative",
}
PARSER_EXPECT = {"isOk": "ok", "isWarning": "warning", "isNotOk": "notok"}

PROP_START = re.compile(r"^prop_(\w+)\s*((?:[\w']+\s*)*)=\s*(.*)$")


def collect_props(path: str) -> Iterator[tuple[str, str, str]]:
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()
    i, n = 0, len(lines)
    while i < n:
        m = PROP_START.match(lines[i])
        if not m:
            i += 1
            continue
        name = "prop_" + m.group(1)
        rhs_parts = [m.group(3)]
        j = i + 1
        while j < n:
            nxt = lines[j]
            if nxt.strip() == "":
                break
            if not nxt.startswith((" ", "\t")):
                break
            if PROP_START.match(nxt):
                break
            rhs_parts.append(nxt)
            j += 1
        rhs = " ".join(p.rstrip("\n") for p in rhs_parts).strip()
        yield name, rhs, os.path.basename(path)
        i = j


def skip_atom(s: str) -> tuple[str, str] | tuple[None, None]:
    s = s.lstrip()
    m = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", s)
    if not m:
        return None, None
    return s[: m.end()].strip(), s[m.end() :]


def skip_bracket_list(s: str) -> str | None:
    s = s.lstrip()
    if not s.startswith("["):
        return None
    depth = 0
    for idx, ch in enumerate(s):
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return s[idx + 1 :]
    return None


def find_top_level(s: str, op: str) -> int | None:
    depth = 0
    in_str = esc = False
    i = 0
    while i < len(s):
        ch = s[i]
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
        elif ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif depth == 0 and s.startswith(op, i):
            return i
        i += 1
    return None


def strip_trailing_cmp(strexpr: str) -> str:
    for op in ("==", "`elem`", "/=", "`notElem`"):
        idx = find_top_level(strexpr, op)
        if idx is not None:
            return strexpr[:idx].strip()
    return strexpr


def categorize(_name: str, rhs: str) -> Classification:
    """Return a manifest entry dict (always), possibly with a decodable 'expr'."""
    parts = rhs.split(None, 1)
    helper = parts[0] if parts else ""
    rest = parts[1] if len(parts) > 1 else ""

    if helper in FULL_ONE_ARG:
        target, rem = skip_atom(rest)
        if rem is not None:
            expr = clean_expr(rem)
            return {
                "category": "full",
                "helper": helper,
                "target": target,
                "polarity": POLARITY[helper],
                "expr": expr,
            }
    if helper == "verifyCodes":
        target, rem = skip_atom(rest)
        if rem is not None:
            rem2 = skip_bracket_list(rem)
            if rem2 is not None:
                return {
                    "category": "full",
                    "helper": helper,
                    "target": target,
                    "polarity": "positive",
                    "expr": clean_expr(rem2),
                }
    if helper == "check":
        return {
            "category": "full",
            "helper": helper,
            "target": "",
            "polarity": "positive",
            "expr": clean_expr(strip_trailing_cmp(rest)),
        }
    if helper == "checkWithIncludes":
        rem = skip_bracket_list(rest)
        if rem is not None:
            return {
                "category": "full",
                "helper": helper,
                "target": "",
                "polarity": "positive",
                "expr": clean_expr(strip_trailing_cmp(rem)),
            }
    if helper in PARSER_HELPERS:
        parser, rem = skip_atom(rest)
        if rem is not None:
            return {
                "category": "parser",
                "helper": helper,
                "parser": parser,
                "expect": PARSER_EXPECT[helper],
                "expr": clean_expr(rem),
            }

    # Everything else: function-unit test or wrapper. Preserve raw for porting.
    return {"category": "fn", "helper": helper, "raw": rhs}


def clean_expr(strexpr: str) -> str:
    strexpr = strexpr.strip()
    if strexpr.startswith("$"):
        strexpr = strexpr[1:].strip()
    # Strip a trailing top-level Haskell line comment (`-- SCxxxx`), which would
    # otherwise comment out the closing paren when spliced into GHCi.
    idx = find_top_level(strexpr, "--")
    if idx is not None:
        strexpr = strexpr[:idx].strip()
    return strexpr


def main() -> None:
    manifest: list[ManifestEntry] = []
    for root, _d, files in os.walk(SRC):
        for f in sorted(files):
            if not f.endswith(".hs"):
                continue
            path = os.path.join(root, f)
            for name, rhs, base in collect_props(path):
                ent: ManifestEntry = {**categorize(name, rhs), "id": name, "file": base}
                manifest.append(ent)

    total = len(manifest)
    decodable = [e for e in manifest if "expr" in e]
    _ = sys.stderr.write(
        f"[extract] total props: {total}; decodable exprs: {len(decodable)}\n"
    )

    # Decode all decodable exprs in one GHCi pass.
    decoded = decode_exprs(decodable)
    for e in manifest:
        if "expr" in e:
            e["script"] = decoded.get(e["id"])
            e["decoded"] = e["id"] in decoded

    full = [e for e in manifest if e["category"] == "full"]
    parser = [e for e in manifest if e["category"] == "parser"]
    fn = [e for e in manifest if e["category"] == "fn"]

    full_ok = [e for e in full if e.get("decoded")]
    parser_ok = [e for e in parser if e.get("decoded")]

    here = os.path.dirname(os.path.abspath(__file__))

    def dump(fname: str, obj: object) -> None:
        with open(os.path.join(here, fname), "w", encoding="utf-8") as fh:
            json.dump(obj, fh, ensure_ascii=False, indent=0)
            _ = fh.write("\n")

    dump(
        "corpus.json",
        [
            {
                "id": e["id"],
                "file": e["file"],
                "helper": e["helper"],
                "target": e.get("target", ""),
                "polarity": e.get("polarity", ""),
                "script": e.get("script"),
            }
            for e in full_ok
        ],
    )
    dump(
        "parser_corpus.json",
        [
            {
                "id": e["id"],
                "file": e["file"],
                "parser": e.get("parser", ""),
                "expect": e.get("expect", ""),
                "script": e.get("script"),
            }
            for e in parser_ok
        ],
    )
    dump(
        "fn_tests.json",
        [
            {
                "id": e["id"],
                "file": e["file"],
                "helper": e["helper"],
                "raw": e.get("raw", ""),
            }
            for e in fn
        ],
    )
    dump(
        "prop_manifest.json",
        [{k: v for k, v in e.items() if k != "expr"} for e in manifest],
    )

    # Provenance summary.
    from collections import Counter

    by_cat = Counter(e["category"] for e in manifest)
    _ = sys.stderr.write(
        f"[extract] categories: {dict(by_cat)}\n[extract] full decoded: {len(full_ok)}/{len(full)}; parser decoded: {len(parser_ok)}/{len(parser)}; fn (raw, not decoded): {len(fn)}\n"
    )
    undecoded = [e["id"] for e in (full + parser) if not e.get("decoded")]
    if undecoded:
        _ = sys.stderr.write(
            f"[extract] undecodable full/parser exprs ({len(undecoded)}): {', '.join(undecoded[:20])}{'...' if len(undecoded) > 20 else ''}\n"
        )
    print(
        json.dumps(
            {
                "total_props": total,
                "categories": dict(by_cat),
                "full_decoded": len(full_ok),
                "full_total": len(full),
                "parser_decoded": len(parser_ok),
                "parser_total": len(parser),
                "fn_raw": len(fn),
                "undecoded_ids": undecoded,
            },
            indent=2,
        )
    )


def decode_exprs(entries: list[ManifestEntry]) -> dict[str, str]:
    """Evaluate each Haskell String expr in GHCi; return {id: string}."""
    # Framing: \x01 id \x02 script \x03 per record. Scripts contain no control
    # bytes 1-3 in practice, so this is unambiguous even for empty scripts.
    script_lines = [
        ":set -XExtendedDefaultRules",
        ':set prompt ""',
        ":set -v0",
        "import Data.List",
        "import System.IO",
        "hSetBuffering stdout (BlockBuffering Nothing)",
        r'let dump name s = putStr ("\SOH" ++ name ++ "\STX" ++ (s :: String) ++ "\ETX")',
    ]
    for e in entries:
        assert "expr" in e
        expr = e["expr"].replace("\n", " ")
        script_lines.append(f'dump "{e["id"]}" ({expr})')
    script_lines += ["hFlush stdout", ":quit"]
    ghc = os.environ.get("GHCI", os.path.expanduser("~/.ghcup/bin/ghci"))
    proc = subprocess.run(
        [ghc, "-ignore-dot-ghci"],
        input=("\n".join(script_lines) + "\n").encode("utf-8"),
        capture_output=True,
        check=False,
    )
    ids = {e["id"] for e in entries}
    decoded: dict[str, str] = {}
    for m in re.finditer(b"\x01(.*?)\x02(.*?)\x03", proc.stdout, re.DOTALL):
        name = m.group(1).decode("utf-8", "replace").strip()
        if name in ids:
            decoded[name] = m.group(2).decode("utf-8", "replace")
    # Warn if any decoded script contains framing control bytes (would be unsafe).
    for name, s in decoded.items():
        if any(c in s for c in ("\x01", "\x02", "\x03")):
            _ = sys.stderr.write(
                f"[extract] WARNING: {name} contains a framing control byte\n"
            )
    return decoded


if __name__ == "__main__":
    main()
