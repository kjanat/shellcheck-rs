"""Import the pinned Omarchy shell corpus without running its scripts."""

import hashlib
import re
import tomllib
from pathlib import Path, PurePosixPath

from pydantic import BaseModel

from bench.candidates import STATE, command, git, locked
from bench.schema import CorpusFile, CorpusSource

CONFIG = Path(__file__).with_name("corpora.toml")
CHECKOUT = STATE / "corpora/omarchy-source"


class CorporaFile(BaseModel):
    corpora: dict[str, CorpusSource]


def spec() -> CorpusSource:
    with CONFIG.open("rb") as file:
        return CorporaFile.model_validate(tomllib.load(file)).corpora["omarchy"]


def snapshot(source: Path, out: Path, identity: CorpusSource) -> dict[str, CorpusFile]:
    actual = git(source, "rev-parse", "HEAD")
    if actual != identity.pin:
        raise ValueError(f"Omarchy source is {actual}; expected {identity.pin}")
    if git(source, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError(
            "Omarchy source has local changes; use a clean pinned snapshot"
        )
    entries: dict[str, CorpusFile] = {}
    for name in sorted(filter(None, git(source, "ls-files", "-z").split("\0"))):
        path = source / name
        if path.is_symlink() or not path.is_file():
            continue
        relative_path = PurePosixPath(name)
        if any(relative_path.full_match(pattern) for pattern in identity.exclude_globs):
            continue
        with path.open("rb") as file:
            header = file.readline(256)
        if (
            path.suffix not in (".sh", ".bash", ".ksh", ".zsh")
            and not re.match(rb"^#!.*\b(?:ba|da|k|z)?sh(?:\s|$)", header)
            and not any(
                relative_path.full_match(pattern) for pattern in identity.shell_globs
            )
        ):
            continue
        data = path.read_bytes()
        relative = f"{identity.prefix}/{name}"
        destination = out / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        entries[relative] = CorpusFile(
            sha256=hashlib.sha256(data).hexdigest(),
            lines=len(data.splitlines()),
            bytes=len(data),
        )
    if not entries:
        raise ValueError("Omarchy snapshot contains no shell files")
    if git(source, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError(
            "Omarchy source changed during import; no corpus manifest published"
        )
    return entries


def prepare(
    out: Path, source: Path | None = None
) -> tuple[dict[str, CorpusFile], CorpusSource]:
    identity = spec()
    with locked(STATE, "omarchy-corpus"):
        checkout = source or CHECKOUT
        cached = checkout.exists()
        if source is None:
            if not checkout.exists():
                checkout.parent.mkdir(parents=True, exist_ok=True)
                print(f"fetch Omarchy {identity.pin}", flush=True)
                command([
                    "gh",
                    "repo",
                    "clone",
                    identity.repo,
                    str(checkout),
                    "--",
                    "--no-checkout",
                    "--filter=blob:none",
                ])
                git(checkout, "checkout", "--detach", identity.pin)
            elif git(checkout, "rev-parse", "HEAD") != identity.pin:
                if git(checkout, "status", "--porcelain", "--untracked-files=all"):
                    raise ValueError("cached Omarchy source has local changes")
                git(checkout, "checkout", "--detach", identity.pin)
        entries = snapshot(checkout, out, identity)
    print(
        f"Omarchy {identity.pin[:12]}: {len(entries):,} shell files, "
        f"{sum(entry.lines for entry in entries.values()):,} lines "
        f"({'existing pinned source' if cached else 'fetched pinned source'})",
        flush=True,
    )
    return entries, identity
