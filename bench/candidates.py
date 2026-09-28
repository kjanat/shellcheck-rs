#!/usr/bin/env python3
"""Small helper around bench/candidates.toml for the shell scripts.

    candidates.py names                 -> one candidate name per line
    candidates.py get <name> <field>    -> one field (empty line if unset)
    candidates.py json                  -> the whole table as JSON
    candidates.py manifest <out-dir> key=value ...
                                        -> write <out-dir>/manifest.json, adding the
                                           binary's sha256, its --version output and
                                           the builder's toolchain.txt
"""

import hashlib
import json
import os
import subprocess
import sys
import tomllib
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load():
    with open(HERE / "candidates.toml", "rb") as f:
        return tomllib.load(f)["candidates"]


def main(argv):
    cmd, *rest = argv or ["json"]
    table = load()
    if cmd == "names":
        print("\n".join(table))
    elif cmd == "get":
        name, field = rest
        value = table[name].get(field, "")
        print(value if not isinstance(value, bool) else str(value).lower())
    elif cmd == "json":
        print(json.dumps(table, indent=2))
    elif cmd == "manifest":
        out = Path(rest[0])
        fields = dict(kv.split("=", 1) for kv in rest[1:])
        binary = out / "shellcheck"
        toolchain = out / "toolchain.txt"
        version = subprocess.run(
            [str(binary), "--version"], capture_output=True, text=True, check=False
        )
        manifest = {
            **fields,
            "binary": str(binary),
            "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
            "binary_bytes": binary.stat().st_size,
            "version_output": (version.stdout + version.stderr).strip(),
            "toolchain": toolchain.read_text().strip().splitlines() if toolchain.exists() else [],
            "built_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "built_on": " ".join(os.uname()),
        }
        (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        print(json.dumps(manifest, indent=2))
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
