"""Small helper around bench/candidates.toml for the shell scripts.

Usage:
    candidates names                    -> one candidate name per line
    candidates get <name> <field>       -> one field (empty line if unset)
    candidates json                     -> the whole table as JSON
    candidates manifest <out-dir> key=value ...
                                        -> write <out-dir>/manifest.json, adding the
                                           binary's sha256, its --version output and
                                           the builder's toolchain.txt
"""

import hashlib
import os
import subprocess
import sys
import tomllib
from datetime import UTC, datetime
from pathlib import Path

from pydantic import TypeAdapter

from bench.schema import CandidatesFile, CandidateSpec, GitSpec, Manifest, ReleaseSpec

HERE = Path(__file__).resolve().parent


def load() -> dict[str, CandidateSpec]:
    with open(HERE / "candidates.toml", "rb") as f:
        return CandidatesFile.model_validate(tomllib.load(f)).candidates


def field(spec: CandidateSpec, name: str) -> str:
    match spec, name:
        case _, "kind":
            return spec.kind
        case _, "baseline":
            return "true" if spec.baseline else "false"
        case ReleaseSpec(), "ref" | "build":
            return ""
        case GitSpec(ref=ref), "ref":
            return ref
        case GitSpec(build=build), "build":
            return build
        case _:
            sys.exit(f"bench: unknown candidate field {name!r}")


def manifest(out: Path, pairs: list[str]) -> Manifest:
    fields: dict[str, str] = {}
    for pair in pairs:
        key, _, value = pair.partition("=")
        fields[key] = value
    binary = out / "shellcheck"
    toolchain = out / "toolchain.txt"
    version = subprocess.run(
        [str(binary), "--version"], capture_output=True, text=True, check=False
    )
    return Manifest.model_validate({
        **fields,
        "binary": str(binary),
        "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "binary_bytes": binary.stat().st_size,
        "version_output": (version.stdout + version.stderr).strip(),
        "toolchain": toolchain.read_text().strip().splitlines()
        if toolchain.exists()
        else [],
        "built_at": datetime.now(UTC).isoformat(timespec="seconds"),
        "built_on": " ".join(os.uname()),
    })


def main() -> None:
    cmd, *rest = sys.argv[1:] or ["json"]
    table = load()
    if cmd == "names":
        print("\n".join(table))
    elif cmd == "get":
        name, key = rest
        print(field(table[name], key))
    elif cmd == "json":
        adapter = TypeAdapter(dict[str, CandidateSpec])
        print(adapter.dump_json(table, indent=2).decode())
    elif cmd == "manifest":
        out = Path(rest[0])
        text = manifest(out, rest[1:]).model_dump_json(indent=2)
        _ = (out / "manifest.json").write_text(text + "\n")
        print(text)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
