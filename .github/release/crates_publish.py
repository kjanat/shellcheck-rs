"""Publish one workspace crate to crates.io and verify the uploaded bytes.

A version already on crates.io is skipped when its checksum matches the local
package and is an error when it does not, so a failed release job can be rerun.
"""

import argparse
import hashlib
import json
import re
import subprocess
import time
from datetime import UTC, datetime
from email.utils import parsedate_to_datetime
from http.client import HTTPException, HTTPResponse
from pathlib import Path
from typing import cast
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

from registry_checks import NotVisibleYet, retry_read

ROOT = Path(__file__).resolve().parents[2]
# crates.io refuses API requests without an identifying User-Agent.
USER_AGENT = "rshellcheck-release (https://github.com/kjanat/shellcheck-rs)"
ATTEMPTS = 5
FALLBACK_DELAY = 90.0
RETRY_AFTER = re.compile(
    r"try again after (\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} GMT)"
)
ALREADY_UPLOADED = re.compile(r"already (?:exists|uploaded)")


def registry_checksum(crate: str, version: str, timeout: float = 30) -> str | None:
    """The SHA-256 crates.io records for the version, or `None` when it has none."""
    request = Request(
        f"https://crates.io/api/v1/crates/{crate}/{version}",
        headers={"User-Agent": USER_AGENT},
    )
    try:
        with cast(HTTPResponse, urlopen(request, timeout=timeout)) as response:
            data = cast(dict[str, dict[str, str]], json.load(response))
    except HTTPError as error:
        if error.code == 404:
            return None
        if error.code in {408, 429} or 500 <= error.code <= 599:
            raise NotVisibleYet(f"HTTP {error.code}") from error
        raise
    except (URLError, TimeoutError, ConnectionError, HTTPException) as error:
        raise NotVisibleYet(str(error)) from error
    return data["version"]["checksum"]


def package(crate: str) -> tuple[str, Path]:
    """Package and build the crate; return its version and `.crate` archive."""
    metadata = cast(
        dict[str, object],
        json.loads(
            subprocess.run(
                ["cargo", "metadata", "--locked", "--no-deps", "--format-version", "1"],
                cwd=ROOT,
                check=True,
                capture_output=True,
                text=True,
            ).stdout
        ),
    )
    packages = cast(list[dict[str, str]], metadata["packages"])
    version = next(p["version"] for p in packages if p["name"] == crate)
    _ = subprocess.run(
        ["cargo", "package", "--locked", "-p", crate], cwd=ROOT, check=True
    )
    target = Path(cast(str, metadata["target_directory"]))
    return version, target / "package" / f"{crate}-{version}.crate"


def retry_delay(output: str, now: datetime | None = None) -> float | None:
    """Seconds to wait before retrying a refused upload, or `None` if a retry cannot help."""
    if match := RETRY_AFTER.search(output):
        retry_at = parsedate_to_datetime(match.group(1))
        return max((retry_at - (now or datetime.now(UTC))).total_seconds() + 5, 0)
    if "429" in output or "Too Many Requests" in output:
        return FALLBACK_DELAY
    return None


def wait_for_checksum(crate: str, version: str, expected: str) -> None:
    def check(timeout: float) -> None:
        actual = registry_checksum(crate, version, timeout)
        if actual is None:
            raise NotVisibleYet("version not visible yet")
        if actual != expected:
            raise ValueError(
                f"{crate} {version}: crates.io checksum differs from the package"
            )

    retry_read(f"{crate} {version}", check)


def publish(crate: str) -> None:
    version, archive = package(crate)
    expected = hashlib.sha256(archive.read_bytes()).hexdigest()
    label = f"{crate} {version}"
    existing = retry_read(
        label, lambda timeout: registry_checksum(crate, version, timeout)
    )
    if existing is not None:
        if existing != expected:
            raise ValueError(
                f"{label} already exists on crates.io with different contents"
            )
        print(f"{label}: identical package already published", flush=True)
        return
    for attempt in range(1, ATTEMPTS + 1):
        result = subprocess.run(
            ["cargo", "publish", "--locked", "--no-verify", "-p", crate],
            check=False,
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        output = result.stdout + result.stderr
        print(output, end="", flush=True)
        if result.returncode == 0 or ALREADY_UPLOADED.search(output):
            break
        delay = retry_delay(output)
        if delay is None or attempt == ATTEMPTS:
            raise subprocess.CalledProcessError(result.returncode, result.args, output)
        print(
            f"{label}: crates.io refused the upload, retrying in {delay:.0f}s",
            flush=True,
        )
        time.sleep(delay)
    wait_for_checksum(crate, version, expected)
    print(f"{label}: published and verified", flush=True)


class Args(argparse.Namespace):
    crate: str = ""


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("crate")
    publish(parser.parse_args(namespace=Args()).crate)
