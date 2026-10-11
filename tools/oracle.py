"""Fetch and build the exact upstream oracle outside the tracked source tree."""

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import TypedDict, cast

type JSON = bool | int | float | str | list[JSON] | dict[str, JSON] | None
ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / ".cache"
SOURCE = CACHE / "upstream-shellcheck"
BINARY = CACHE / "shellcheck-oracle"


class Pin(TypedDict):
    repository: str
    revision: str
    version: str


class Args(argparse.Namespace):
    fetch_only: bool = False
    verify_only: bool = False


def run(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def load_json(path: Path) -> JSON:
    return cast(JSON, json.loads(path.read_text()))


def load_pin() -> Pin:
    data = load_json(ROOT / "tools/oracle.json")
    if not isinstance(data, dict):
        raise TypeError("Oracle pin must be a JSON object")
    repository, revision, version = (
        data.get("repository"),
        data.get("revision"),
        data.get("version"),
    )
    if not (
        isinstance(repository, str)
        and isinstance(revision, str)
        and isinstance(version, str)
    ):
        raise TypeError("Oracle pin needs string repository, revision and version")
    return {"repository": repository, "revision": revision, "version": version}


def prepare() -> Pin:
    pin = load_pin()
    revision = pin["revision"]
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Oracle revision must be a full commit SHA")
    CACHE.mkdir(exist_ok=True)
    if not SOURCE.exists():
        with tempfile.TemporaryDirectory(prefix="oracle-fetch-", dir=CACHE) as tmp:
            checkout = Path(tmp) / "source"
            _ = run(
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
            _ = run("git", "fetch", "--depth=1", "origin", revision, cwd=checkout)
            _ = run("git", "checkout", "--detach", revision, cwd=checkout)
            _ = checkout.rename(SOURCE)
    if run("git", "rev-parse", "HEAD", cwd=SOURCE) != revision:
        raise ValueError(
            f"{SOURCE} has a different revision; preserve it elsewhere before fetching"
        )
    if run("git", "status", "--porcelain", "--untracked-files=normal", cwd=SOURCE):
        raise ValueError(
            f"{SOURCE} has local changes; refusing to use a modified oracle"
        )
    return pin


def verify(pin: Pin) -> None:
    metadata = load_json(CACHE / "shellcheck-oracle.json")
    expected = {**pin, "sha256": hashlib.sha256(BINARY.read_bytes()).hexdigest()}
    if metadata != expected:
        raise ValueError("Cached oracle does not match pinned source and binary digest")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("--fetch-only", action="store_true")
    _ = parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args(namespace=Args())
    pin = prepare()
    print(f"Oracle source: {SOURCE} at {pin['revision']}", flush=True)
    if args.fetch_only:
        return
    if args.verify_only:
        verify(pin)
        print("Cached oracle identity verified")
        return
    _ = subprocess.run(["cabal", "build", "exe:shellcheck"], cwd=SOURCE, check=True)
    built = Path(run("cabal", "list-bin", "exe:shellcheck", cwd=SOURCE))
    if f"version: {pin['version']}" not in run(str(built), "--version").splitlines():
        raise ValueError("Built oracle version differs from the pin")
    with tempfile.NamedTemporaryFile(dir=CACHE, delete=False) as tmp:
        temporary = Path(tmp.name)
    try:
        _ = shutil.copy2(built, temporary)
        _ = temporary.replace(BINARY)
    finally:
        temporary.unlink(missing_ok=True)
    metadata = {**pin, "sha256": hashlib.sha256(BINARY.read_bytes()).hexdigest()}
    _ = (CACHE / "shellcheck-oracle.json").write_text(
        json.dumps(metadata, indent=2) + "\n"
    )
    print(f"Oracle built: {BINARY}")


if __name__ == "__main__":
    main()
