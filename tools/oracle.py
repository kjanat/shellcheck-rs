"""Fetch and build the exact upstream oracle outside the tracked source tree."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / ".cache"
SOURCE = CACHE / "upstream-shellcheck"
BINARY = CACHE / "shellcheck-oracle"


def run(*args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def prepare():
    pin = json.loads((ROOT / "tools/oracle.json").read_text())
    revision = pin["revision"]
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Oracle revision must be a full commit SHA")
    CACHE.mkdir(exist_ok=True)
    if not SOURCE.exists():
        with tempfile.TemporaryDirectory(prefix="oracle-fetch-", dir=CACHE) as tmp:
            checkout = Path(tmp) / "source"
            run(
                "gh",
                "repo",
                "clone",
                pin["repository"],
                str(checkout),
                "--",
                "--filter=blob:none",
                "--no-checkout",
                "--depth=1",
            )
            run("git", "fetch", "--depth=1", "origin", revision, cwd=checkout)
            run("git", "checkout", "--detach", revision, cwd=checkout)
            checkout.rename(SOURCE)
    if run("git", "rev-parse", "HEAD", cwd=SOURCE) != revision:
        raise ValueError(
            f"{SOURCE} has a different revision; preserve it elsewhere before fetching"
        )
    if run("git", "status", "--porcelain", "--untracked-files=normal", cwd=SOURCE):
        raise ValueError(
            f"{SOURCE} has local changes; refusing to use a modified oracle"
        )
    return pin


def verify(pin):
    metadata = json.loads((CACHE / "shellcheck-oracle.json").read_text())
    expected = {**pin, "sha256": hashlib.sha256(BINARY.read_bytes()).hexdigest()}
    if metadata != expected:
        raise ValueError("Cached oracle does not match pinned source and binary digest")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-only", action="store_true")
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    pin = prepare()
    print(f"Oracle source: {SOURCE} at {pin['revision']}", flush=True)
    if args.fetch_only:
        return
    if args.verify_only:
        verify(pin)
        print("Cached oracle identity verified")
        return
    subprocess.run(["cabal", "build", "exe:shellcheck"], cwd=SOURCE, check=True)
    built = Path(run("cabal", "list-bin", "exe:shellcheck", cwd=SOURCE))
    if f"version: {pin['version']}" not in run(str(built), "--version").splitlines():
        raise ValueError("Built oracle version differs from the pin")
    with tempfile.NamedTemporaryFile(dir=CACHE, delete=False) as tmp:
        temporary = Path(tmp.name)
    try:
        shutil.copy2(built, temporary)
        temporary.replace(BINARY)
    finally:
        temporary.unlink(missing_ok=True)
    metadata = {**pin, "sha256": hashlib.sha256(BINARY.read_bytes()).hexdigest()}
    (CACHE / "shellcheck-oracle.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"Oracle built: {BINARY}")


if __name__ == "__main__":
    main()
