"""Prepare exact candidate identities; reuse binaries before invoking build tools."""

import argparse
import fcntl
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import time
import tomllib
from collections.abc import Generator
from contextlib import contextmanager
from pathlib import Path

from pydantic import BaseModel

from bench.schema import CandidatesFile, CandidateSpec, Manifest

ROOT = Path(__file__).resolve().parents[2]
STATE = ROOT / ".bench"
# Bump when the preparation recipe or its artifact contract changes.
RECIPE = 3


class Build(BaseModel):
    name: str
    spec: CandidateSpec
    source: str | None = None
    pin: str = ""
    dirty: bool = False
    source_sha256: str = ""
    binary: str | None = None
    binary_sha256: str | None = None
    managed: bool = False
    key: str
    layers_key: str


class Plan(BaseModel):
    version: int = RECIPE
    baseline: str
    builds: list[Build]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def identity(data: object) -> str:
    return digest(json.dumps(data, sort_keys=True, separators=(",", ":")).encode())


def command(argv: list[str], cwd: Path | None = None) -> str:
    result = subprocess.run(
        argv, cwd=cwd, capture_output=True, text=True, check=False, timeout=120
    )
    if result.returncode:
        raise ValueError(f"{' '.join(argv)} failed:\n{result.stderr.strip()}")
    return result.stdout.strip()


def git(source: Path, *args: str) -> str:
    return command(["git", "-C", str(source), *args])


@contextmanager
def locked(state: Path, name: str) -> Generator[None]:
    directory = state / "locks"
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / f"{name}.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        yield


def write_model(path: Path, value: BaseModel) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(".tmp")
    temp.write_text(value.model_dump_json(indent=2) + "\n")
    temp.replace(path)


def specs(path: Path) -> dict[str, CandidateSpec]:
    with path.open("rb") as file:
        table = CandidatesFile.model_validate(tomllib.load(file)).candidates
    if not table or sum(spec.baseline for spec in table.values()) != 1:
        raise ValueError("candidate configuration needs exactly one baseline")
    for name in table:
        if not name or any(
            c not in "abcdefghijklmnopqrstuvwxyz0123456789-_" for c in name
        ):
            raise ValueError(f"invalid candidate name: {name!r}")
    return table


def selected(table: dict[str, CandidateSpec], names: str) -> list[str]:
    result = names.split(",") if names else list(table)
    unknown = set(result) - table.keys()
    if unknown:
        raise ValueError(f"unknown candidates: {', '.join(sorted(unknown))}")
    return list(dict.fromkeys(result))


def overrides(values: list[str], table: dict[str, CandidateSpec]) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        name, separator, path = value.partition("=")
        if not separator or not path or name not in table or name in result:
            raise ValueError(f"expected a unique configured NAME=PATH, got {value!r}")
        result[name] = Path(path).resolve()
    return result


def source_identity(source: Path) -> tuple[str, bool, str]:
    pin = git(source, "rev-parse", "HEAD")
    dirty = bool(git(source, "status", "--porcelain", "--untracked-files=all"))
    # Include local additions and deletions, not just HEAD. Never print source contents.
    names = git(source, "ls-files", "--cached", "--others", "--exclude-standard", "-z")
    hashes: list[tuple[str, str]] = []
    for name in sorted(set(names.split("\0")) - {""}):
        path = source / name
        if path.name.startswith(".env") or path.suffix.lower() in (
            ".pem",
            ".key",
            ".p12",
            ".pfx",
        ):
            raise ValueError(
                f"protected file in source inputs: {name}; exclude it from the build checkout"
            )
        if path.is_symlink():
            value = digest(os.readlink(path).encode())
        elif path.is_file():
            value = digest(path.read_bytes())
        else:
            value = "deleted"
        mode = str(path.lstat().st_mode & 0o111) if path.exists() else "0"
        hashes.append((name, value + ":" + mode))
    return pin, dirty, identity(hashes)


def checkout(state: Path, name: str, spec: CandidateSpec) -> Path:
    source = state / "checkouts" / name
    fresh = not source.exists()
    if fresh:
        source.parent.mkdir(parents=True, exist_ok=True)
        command([
            "git",
            "clone",
            "--no-checkout",
            "--filter=blob:none",
            str(spec.repo),
            str(source),
        ])
    if not fresh and git(source, "status", "--porcelain"):
        raise ValueError(
            f"managed checkout {source} is dirty; use --source for local work"
        )
    command(["git", "-C", str(source), "fetch", "--no-tags", "origin", spec.ref])
    pin = git(source, "rev-parse", "FETCH_HEAD")
    git(source, "checkout", "--detach", pin)
    return source


def tool_inputs(source: Path, tools: list[str]) -> dict[str, object]:
    config: dict[str, object] = {}
    for filename in ("mise.toml", "mise.lock"):
        path = source / filename
        if path.exists():
            with path.open("rb") as file:
                contents = tomllib.load(file)
            config[filename] = {
                "tools": {
                    name: value
                    for name, value in contents.get("tools", {}).items()
                    if name in tools
                },
                "tool_alias": contents.get("tool_alias", {}),
                "plugins": contents.get("plugins", {}),
            }
    with (ROOT / "mise.lock").open("rb") as file:
        fallback = tomllib.load(file).get("tools", {})
    source_lock = {}
    if (source / "mise.lock").exists():
        with (source / "mise.lock").open("rb") as file:
            source_lock = tomllib.load(file).get("tools", {})
    locked_tools: dict[str, object] = {}
    versions: dict[str, str] = {}
    for name in tools:
        entries = source_lock.get(name) or fallback.get(name)
        if not entries or len(entries) != 1:
            raise ValueError(
                f"{name}: need one locked version in the candidate or harness mise.lock"
            )
        locked_tools[name] = entries
        versions[name] = entries[0]["version"]
    config["locked_tools"] = locked_tools
    config["versions"] = versions
    return config


def cache_keys(
    spec: CandidateSpec, source: Path | None, pin: str, sha: str, binary_sha: str | None
) -> tuple[str, str]:
    host = f"{platform.system().lower()}-{platform.machine()}"
    abi: dict[str, object] = {"libc": platform.libc_ver()}
    if platform.system() == "Linux":
        abi["distribution"] = {
            key: value
            for key, value in platform.freedesktop_os_release().items()
            if key in ("ID", "VERSION_ID")
        }
    tools = tool_inputs(source, spec.tools) if source else {}
    inputs = {
        "recipe": RECIPE,
        "spec": spec.model_dump(),
        "host": host,
        "abi": abi,
        "tools": tools,
        "source": sha,
        "pin": pin,
        "binary": binary_sha,
    }
    layers = {
        "recipe": RECIPE,
        "host": host,
        "abi": abi,
        "tools": tools,
        "cargo_lock": digest((source / "Cargo.lock").read_bytes())
        if source and (source / "Cargo.lock").exists()
        else None,
    }
    return f"{host}-{identity(inputs)}", f"{host}-{identity(layers)}"


def resolve(
    table: dict[str, CandidateSpec],
    names: str,
    binaries: dict[str, Path],
    sources: dict[str, Path],
    state: Path,
) -> Plan:
    builds: list[Build] = []
    for name in selected(table, names):
        spec = table[name]
        with locked(state, name):
            source = sources.get(name)
            binary = binaries.get(name)
            if source is None and binary is None and spec.repo:
                source = checkout(state, name, spec)
            if source:
                pin, dirty, sha = source_identity(source)
            else:
                pin, dirty, sha = "", False, ""
            if binary is None and not spec.repo:
                found = (
                    command(["mise", "which", spec.binary], cwd=ROOT)
                    if spec.tool
                    else shutil.which(spec.binary)
                )
                if found is None:
                    raise ValueError(f"{spec.binary} is missing; run mise install")
                binary = Path(found).resolve()
            if binary:
                sha = digest(binary.read_bytes()) if source is None else sha
            binary_sha = digest(binary.read_bytes()) if binary else None
            key, layers_key = cache_keys(spec, source, pin, sha, binary_sha)
            builds.append(
                Build(
                    name=name,
                    spec=spec,
                    source=str(source) if source else None,
                    pin=pin,
                    dirty=dirty,
                    source_sha256=sha,
                    binary=str(binary) if binary else None,
                    binary_sha256=binary_sha,
                    managed=source is not None and name not in sources,
                    key=key,
                    layers_key=layers_key,
                )
            )
    return Plan(
        baseline=next(name for name, spec in table.items() if spec.baseline),
        builds=builds,
    )


def read_manifest(directory: Path) -> Manifest:
    manifest = Manifest.model_validate_json((directory / "manifest.json").read_text())
    path = Path(manifest.binary)
    path = path if path.is_absolute() else directory / path
    data = path.read_bytes()
    if digest(data) != manifest.binary_sha256 or len(data) != manifest.binary_bytes:
        raise ValueError(
            f"{manifest.name}: prepared binary checksum differs; run bench prepare"
        )
    if not os.access(path, os.X_OK):
        raise ValueError(f"{manifest.name}: prepared binary is not executable")
    return manifest.model_copy(update={"binary": str(path.resolve())})


def publish(binary: Path, build: Build, directory: Path) -> Manifest:
    directory.mkdir(parents=True, exist_ok=True)
    temp = directory / "rshellcheck.tmp"
    shutil.copy2(binary, temp)
    data = temp.read_bytes()
    sha = digest(data)
    if build.binary_sha256 and sha != build.binary_sha256:
        temp.unlink()
        raise ValueError(f"{build.name}: supplied binary changed during publication")
    relative = Path(sha) / "rshellcheck"
    destination = directory / relative
    destination.parent.mkdir(exist_ok=True)
    # A previously prepared revision stays executable while another is published.
    temp.replace(destination)
    version = command([str(destination), "--version"])
    kind = "git" if build.source else "path" if build.spec.repo else "release"
    pin = build.pin
    if kind == "release":
        pin = next(
            (
                line.partition(":")[2].strip()
                for line in version.splitlines()
                if line.startswith("version:")
            ),
            version,
        )
    manifest = Manifest(
        name=build.name,
        kind=kind,
        ref=build.spec.ref if build.source else build.binary or "",
        pin=pin,
        binary=str(relative),
        binary_sha256=digest(data),
        binary_bytes=len(data),
        version_output=version,
        source=build.source,
        dirty=build.dirty,
        source_sha256=build.source_sha256 or None,
        build_key=build.key,
    )
    write_model(directory / "manifest.json", manifest)
    return read_manifest(directory)


def build_candidate(build: Build, state: Path) -> Path:
    if build.binary:
        binary = Path(build.binary)
        if digest(binary.read_bytes()) != build.binary_sha256:
            raise ValueError(f"{build.name}: supplied binary changed after resolution")
        return binary
    if build.source is None:
        raise ValueError(f"{build.name}: missing source")
    source = Path(build.source)
    target = state / "build" / build.name
    environment = os.environ.copy()
    environment.update(
        CI="1",
        MISE_YES="1",
        CARGO_TARGET_DIR=str(target),
        CARGO_BUILD_BUILD_DIR=str(target),
        CARGO_HOME=str(state / "dependencies/cargo"),
        CARGO_BUILD_JOBS=str(build.spec.jobs),
        MISE_EXEC_AUTO_INSTALL="false",
    )
    # Use the recorded recipe, rather than ambient profile/flag overrides.
    for name in list(environment):
        if name.startswith("CARGO_PROFILE_") or name in (
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER",
            "CARGO_BUILD_TARGET",
            "CARGO_BUILD_RUSTFLAGS",
            "CARGO_BUILD_RUSTC",
            "CFLAGS",
            "CXXFLAGS",
            "CPPFLAGS",
            "LDFLAGS",
        ):
            environment.pop(name)
    ghcup = Path.home() / ".ghcup" / "bin"
    if ghcup.is_dir():
        environment["PATH"] = environment.get("PATH", "") + os.pathsep + str(ghcup)

    def run(argv: list[str], cwd: Path = source) -> None:
        subprocess.run(argv, cwd=cwd, env=environment, check=True)

    run(["mise", "trust", "-q"])
    versions = tool_inputs(source, build.spec.tools)["versions"]
    assert isinstance(versions, dict)
    pinned = [f"{name}@{versions[name]}" for name in build.spec.tools]
    source_tools = {}
    if (source / "mise.lock").exists():
        with (source / "mise.lock").open("rb") as file:
            source_tools = tomllib.load(file).get("tools", {})
    for name in build.spec.tools:
        origin = source if source_tools.get(name) else ROOT
        run(["mise", "install", "--locked", name], origin)
    execute = ["mise", "exec", *pinned, "--"]
    if "cabal" in build.spec.tools:
        cache = subprocess.run(
            [*execute, "cabal", "path", "--remote-repo-cache"],
            cwd=source,
            env=environment,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        if not (Path(cache) / "hackage.haskell.org/01-index.tar").exists():
            run([*execute, "cabal", "update"])
        run(
            [
                *execute,
                "cabal",
                "build",
                "--only-dependencies",
                "h2r-plugin",
            ],
            source / "compiler/canary",
        )
    run([
        *execute,
        "cargo",
        "build",
        "--release",
        "--locked",
        "-p",
        build.spec.package,
        "--bin",
        build.spec.binary,
    ])
    return target / "release" / build.spec.binary


def prepare(plan: Plan, state: Path, prepared: Path, names: str = "") -> None:
    if plan.version != RECIPE:
        raise ValueError("preparation plan version differs; resolve it again")
    table = {build.name: build.spec for build in plan.builds}
    for name in selected(table, names):
        build = next(build for build in plan.builds if build.name == name)
        with locked(state, name):
            started = time.monotonic()
            if build.managed and build.source and not Path(build.source).exists():
                source = Path(build.source)
                source.parent.mkdir(parents=True, exist_ok=True)
                command([
                    "git",
                    "clone",
                    "--no-checkout",
                    "--filter=blob:none",
                    str(build.spec.repo),
                    str(source),
                ])
                command([
                    "git",
                    "-C",
                    str(source),
                    "fetch",
                    "--no-tags",
                    "origin",
                    build.pin,
                ])
                git(source, "checkout", "--detach", build.pin)
            if (
                build.binary
                and digest(Path(build.binary).read_bytes()) != build.binary_sha256
            ):
                raise ValueError(f"{name}: supplied binary changed after resolution")
            if build.source and source_identity(Path(build.source)) != (
                build.pin,
                build.dirty,
                build.source_sha256,
            ):
                raise ValueError(
                    f"{name}: source changed after resolution; resolve again"
                )
            expected = cache_keys(
                build.spec,
                Path(build.source) if build.source else None,
                build.pin,
                build.source_sha256,
                build.binary_sha256,
            )
            if expected != (build.key, build.layers_key):
                raise ValueError(
                    f"{name}: plan build inputs or platform differ; resolve again"
                )
            cache = state / "cache" / name / build.key
            manifest = None
            try:
                manifest = read_manifest(cache)
                if manifest.build_key != build.key:
                    manifest = None
            except OSError, ValueError:
                pass
            if manifest:
                print(f"{name}: binary cache hit", file=sys.stderr, flush=True)
                publish(Path(manifest.binary), build, prepared / name)
            else:
                status = (
                    "supplied binary"
                    if build.binary
                    else "incremental build"
                    if (state / "build" / name).exists()
                    else "cold build"
                )
                print(
                    f"{name}: {status}"
                    + (
                        " (h2r can take hours)"
                        if name == "h2r" and not build.binary
                        else ""
                    ),
                    file=sys.stderr,
                    flush=True,
                )
                binary = build_candidate(build, state)
                if build.source and source_identity(Path(build.source)) != (
                    build.pin,
                    build.dirty,
                    build.source_sha256,
                ):
                    raise ValueError(
                        f"{name}: source changed during preparation; binary was not published"
                    )
                publish(binary, build, cache)
                publish(Path(read_manifest(cache).binary), build, prepared / name)
            print(
                f"{name}: ready in {time.monotonic() - started:.1f}s",
                file=sys.stderr,
                flush=True,
            )


def add_arguments(parser: argparse.ArgumentParser, *, selection: bool = True) -> None:
    parser.add_argument(
        "--config", type=Path, default=Path(__file__).with_name("candidates.toml")
    )
    parser.add_argument("--state", type=Path, default=STATE)
    parser.add_argument("--prepared", type=Path, default=STATE / "prepared")
    if selection:
        parser.add_argument(
            "--candidates", default="", help="comma-separated candidate names"
        )
    parser.add_argument(
        "--binary",
        action="append",
        default=[],
        metavar="NAME=PATH",
        help="use an already-built executable",
    )
    parser.add_argument(
        "--source",
        action="append",
        default=[],
        metavar="NAME=PATH",
        help="build a local checkout, preserving its modifications",
    )


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    add_arguments(parser)
    parser.add_argument(
        "--plan",
        type=Path,
        help="consume a resolved plan; with --resolve-only, write it here",
    )
    parser.add_argument("--resolve-only", action="store_true")
    parser.add_argument(
        "--verify",
        action="store_true",
        help="verify prepared checksums without resolving or compiling",
    )
    args = parser.parse_args(argv)
    table = specs(args.config)
    state = args.state.resolve()
    if args.verify:
        for name in selected(table, args.candidates):
            manifest = read_manifest(args.prepared / name)
            if manifest.name != name:
                raise ValueError(f"manifest name differs: {name}")
            print(f"{name}: verified {manifest.binary_sha256[:12]}")
        return
    if args.plan and not args.resolve_only:
        if args.binary or args.source:
            raise ValueError("--plan cannot be combined with --binary or --source")
        plan = Plan.model_validate_json(args.plan.read_text())
    else:
        plan = resolve(
            table,
            args.candidates,
            overrides(args.binary, table),
            overrides(args.source, table),
            state,
        )
    if args.resolve_only:
        write_model(args.plan or state / "plan.json", plan)
    else:
        prepare(plan, state, args.prepared.resolve(), args.candidates)
