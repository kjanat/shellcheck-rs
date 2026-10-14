"""Bounded retries for read-only registry verification."""

import json
import time
from collections.abc import Callable
from http.client import HTTPException, HTTPResponse
from typing import TypedDict, cast
from urllib.error import HTTPError, URLError
from urllib.request import urlopen


class NotVisibleYet(Exception):
    pass


def retry_read[T](label: str, read: Callable[[float], T], seconds: float = 600) -> T:
    deadline = time.monotonic() + seconds
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError(f"{label}: registry verification exceeded {seconds:g}s")
        try:
            return read(min(30, remaining))
        except NotVisibleYet as error:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"{label}: {error}") from error
            print(f"{label}: {error}; retrying registry check", flush=True)
            time.sleep(min(10, remaining))


class PublishedFile(TypedDict):
    filename: str
    digests: dict[str, str]


def verify_pypi(project: str, version: str, expected: dict[str, str]) -> None:
    def check(timeout: float) -> None:
        try:
            with cast(
                HTTPResponse,
                urlopen(
                    f"https://pypi.org/pypi/{project}/{version}/json", timeout=timeout
                ),
            ) as response:
                data = cast(dict[str, list[PublishedFile]], json.load(response))
        except HTTPError as error:
            if error.code not in {404, 408, 429} and not 500 <= error.code <= 599:
                raise
            raise NotVisibleYet(f"HTTP {error.code}") from error
        except (URLError, TimeoutError, ConnectionError, HTTPException) as error:
            raise NotVisibleYet(str(error)) from error
        hashes = {p["filename"]: p["digests"]["sha256"] for p in data["urls"]}
        for name, digest in expected.items():
            if name in hashes and hashes[name] != digest:
                raise ValueError(f"PyPI digest mismatch: {name}")
        if expected.keys() - hashes.keys():
            raise NotVisibleYet("uploaded files not yet visible")

    retry_read(f"{project}=={version}", check)
