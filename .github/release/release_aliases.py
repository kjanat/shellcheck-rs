"""Promote completed stable releases to upstream aliases, never backwards."""

import base64
import json
import os
import subprocess
import tomllib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import TypedDict, cast

from binding_packages import load_record, members
from binding_packages import verify as verify_bindings
from native_packages import load_record as load_native_record
from native_packages import verify as verify_native
from registry_checks import NotVisibleYet, retry_read
from release import TARGETS, metadata, upstream


def output(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


class GitObject(TypedDict):
    type: str
    sha: str


class GitRef(TypedDict):
    ref: str
    object: GitObject


def api(path: str, *args: str) -> object:
    return cast(object, json.loads(output("gh", "api", path, *args)))


def advance(current: str, previous: str | None) -> bool:
    if "-" in current:
        return False
    return previous is None or tuple(map(int, current.split("."))) >= tuple(
        map(int, previous.split("."))
    )


def promote_image(source: str, alias: str) -> None:
    digest = output(
        "docker",
        "buildx",
        "imagetools",
        "inspect",
        source,
        "--format",
        "{{.Manifest.Digest}}",
    )
    if not digest.startswith("sha256:") or len(digest) != 71:
        raise ValueError(f"Invalid image digest: {source}")
    repository = source.rsplit(":", 1)[0]
    _ = subprocess.run(
        [
            "docker",
            "buildx",
            "imagetools",
            "create",
            "--tag",
            alias,
            f"{repository}@{digest}",
        ],
        check=True,
    )
    actual = output(
        "docker",
        "buildx",
        "imagetools",
        "inspect",
        alias,
        "--format",
        "{{.Manifest.Digest}}",
    )
    if actual != digest:
        raise ValueError(f"Image alias digest mismatch: {alias}")


def npm_tags(name: str, timeout: float) -> dict[str, str]:
    try:
        data = subprocess.check_output(
            [
                "npm",
                "view",
                name,
                "dist-tags",
                "--json",
                "--registry=https://registry.npmjs.org",
                "--fetch-retries=0",
            ],
            text=True,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        raise NotVisibleYet("npm tag read timed out") from error
    except subprocess.CalledProcessError as error:
        code = cast(dict[str, dict[str, str]], json.loads(cast(str, error.output)))[
            "error"
        ]["code"]
        if code in {
            "E404",
            "E408",
            "E429",
            "ETIMEDOUT",
            "ESOCKETTIMEDOUT",
            "ECONNRESET",
            "EAI_AGAIN",
        } or (len(code) == 4 and code.startswith("E5") and code[1:].isdigit()):
            raise NotVisibleYet(code) from error
        raise
    return cast(dict[str, str], json.loads(data))


def promote_npm(name: str, version: str, alias: str) -> None:
    tags = retry_read(
        name, lambda timeout, name=name: npm_tags(name, timeout), seconds=60
    )
    if tags.get(alias) == version:
        print(f"{name}: {alias} already points to {version}", flush=True)
        return
    if not advance(version, tags.get(alias)):
        raise ValueError(f"Refusing to replace newer npm alias: {name}")
    _ = subprocess.run(
        [
            "npm",
            "dist-tag",
            "add",
            f"{name}@{version}",
            alias,
            "--registry=https://registry.npmjs.org",
        ],
        check=True,
        timeout=120,
    )

    def verify(timeout: float) -> None:
        actual = npm_tags(name, timeout).get(alias)
        if actual == version:
            return
        if not advance(version, actual):
            raise ValueError(f"npm alias moved to a newer version: {name}")
        raise NotVisibleYet(f"{alias} update not visible yet")

    retry_read(f"{name}:{alias}", verify)


def promote(directory: Path) -> None:
    meta = metadata()
    version = meta["version"]
    if not advance(version, None):
        print("Prerelease: upstream aliases stay unchanged.")
        return
    verify_bindings(directory)
    verify_native(directory)
    repository = os.environ["GITHUB_REPOSITORY"]
    if repository != "kjanat/shellcheck-rs":
        raise ValueError("Release aliases belong to kjanat/shellcheck-rs")
    alias = "upstream-" + upstream()["upstream_version"]
    endpoint = f"repos/{repository}"
    # Inspect the exact existing alias; an API failure is not an absent tag.
    refs = cast(list[GitRef], api(f"{endpoint}/git/matching-refs/tags/{alias}"))
    existing = next((r for r in refs if r["ref"] == f"refs/tags/{alias}"), None)
    if existing:
        if existing["object"]["type"] != "commit":
            raise ValueError("Expected a lightweight upstream alias tag")
        old_sha = existing["object"]["sha"]
        content = cast(
            dict[str, str],
            api(f"{endpoint}/contents/crates/shellcheck-cli/Cargo.toml?ref={old_sha}"),
        )
        previous = cast(
            dict[str, dict[str, str]],
            tomllib.loads(base64.b64decode(content["content"]).decode()),
        )["package"]["version"]
        if not advance(version, previous):
            print(f"Keeping newer upstream alias at {previous}.")
            return
        if version == previous and old_sha != meta["commit"]:
            raise ValueError("Same release version points at a different commit")
    commit = cast(
        dict[str, dict[str, dict[str, bool]]],
        api(f"{endpoint}/commits/{meta['commit']}"),
    )
    if not commit["commit"]["verification"]["verified"]:
        raise ValueError("Refusing to tag an unverified release commit")

    records = load_native_record(directory)["packages"]
    archives = [directory / p["file"] for p in records]
    archives += [
        directory / p["name"]
        for p in load_record(directory)["packages"]
        if p["kind"] == "npm"
    ]
    names = [
        cast(dict[str, str], json.loads(members(archive)["package/package.json"]))[
            "name"
        ]
        for archive in archives
    ]
    # A failed newer promotion may have moved npm aliases before its Git tag.
    # Inspect every package first so retrying an older run cannot undo that work.
    for name in names:
        tags = retry_read(
            name, lambda timeout, name=name: npm_tags(name, timeout), seconds=60
        )
        if not advance(version, tags.get(alias)):
            print(f"Keeping newer npm upstream alias for {name}.")
            return
    with ThreadPoolExecutor(max_workers=8) as pool:
        list(pool.map(lambda name: promote_npm(name, version, alias), names))
    if os.environ.get("REGISTRY") == "npm":
        return
    image = "ghcr.io/kjanat/shellcheck-rs"
    promote_image(f"{image}:{version}", f"{image}:{alias}")
    for target, _, _ in TARGETS:
        promote_image(
            f"{image}/binaries:{version}-{target}", f"{image}/binaries:{alias}-{target}"
        )

    if existing:
        _ = api(
            f"{endpoint}/git/refs/tags/{alias}",
            "--method",
            "PATCH",
            "-f",
            f"sha={meta['commit']}",
            "-F",
            "force=true",
        )
    else:
        _ = api(
            f"{endpoint}/git/refs",
            "--method",
            "POST",
            "-f",
            f"ref=refs/tags/{alias}",
            "-f",
            f"sha={meta['commit']}",
        )
    actual = cast(GitRef, api(f"{endpoint}/git/ref/tags/{alias}"))
    if actual["object"]["sha"] != meta["commit"]:
        raise ValueError("Git upstream alias target mismatch")


if __name__ == "__main__":
    import sys

    promote(Path(sys.argv[1]))
