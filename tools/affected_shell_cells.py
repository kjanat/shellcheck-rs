#!/usr/bin/env python3
"""Plan validity image builds from changed inputs and registry availability.

The selector deliberately works from the checked-in matrix and the matrix at
the merge base.  This keeps a matrix refresh from accidentally dropping an
old cell from the build, while the output itself always contains current
cells (deleted cells therefore disappear naturally). Cells without a resolved
OCI digest are always selected.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import NotRequired, TypedDict, cast

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MATRIX = "validity/matrix.toml"


class SelectorError(RuntimeError):
    pass


class Cell(TypedDict):
    shell: str
    version: str
    image: str
    base: str
    dockerfile: str
    source: object
    digest: NotRequired[str]
    vm: NotRequired[bool]


def git(*args: str, cwd: Path = ROOT) -> str:
    result = subprocess.run(
        ["git", *args], cwd=cwd, text=True, capture_output=True, check=False
    )
    if result.returncode:
        raise SelectorError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def load_matrix(text: str, label: str) -> list[Cell]:
    try:
        data = cast(dict[str, object], tomllib.loads(text))
    except tomllib.TOMLDecodeError as exc:
        raise SelectorError(f"{label}: invalid TOML: {exc}") from exc
    cells = data.get("cell")
    if not isinstance(cells, list):
        raise SelectorError(f"{label}: expected a [[cell]] array")
    cells = cast(list[object], cells)
    required = ("shell", "version", "image", "base", "dockerfile", "source")
    result: list[Cell] = []
    seen: set[str] = set()
    for n, cell in enumerate(cells):
        if not isinstance(cell, dict) or any(key not in cell for key in required):
            raise SelectorError(f"{label}: cell {n} is missing required fields")
        raw_cell = cast(dict[str, object], cell)
        if not isinstance(raw_cell["shell"], str) or not isinstance(
            raw_cell["version"], str
        ):
            raise SelectorError(f"{label}: cell {n} has a non-string id")
        if not all(
            isinstance(raw_cell[key], str) for key in ("image", "base", "dockerfile")
        ):
            raise SelectorError(f"{label}: cell {n} has invalid build fields")
        cell = cast(Cell, cast(object, raw_cell))
        cell_id = f"{cell['shell']}:{cell['version']}"
        if cell_id in seen:
            raise SelectorError(f"{label}: duplicate cell {cell_id}")
        seen.add(cell_id)
        result.append(cell)
    return result


def cell_id(cell: Cell) -> str:
    return f"{cell['shell']}:{cell['version']}"


def show_matrix(
    base: str, matrix_path: str, cwd: Path = ROOT
) -> tuple[str | None, bool]:
    """Return the base matrix and whether it existed.

    A missing path at a valid merge base is expected for a newly introduced
    matrix.  Other git errors (including an invalid base SHA) are failures.
    """
    try:
        return git("show", f"{base}:{matrix_path}", cwd=cwd), True
    except SelectorError as exc:
        if "exists on disk, but not in" in str(exc) or "does not exist in" in str(exc):
            return None, False
        raise


def changed_paths(base: str, cwd: Path = ROOT) -> list[str]:
    return [
        p
        for p in git("diff", "--name-only", "-z", f"{base}...HEAD", cwd=cwd).split("\0")
        if p
    ]


def merge_base(base: str, cwd: Path = ROOT) -> str:
    return git("merge-base", base, "HEAD", cwd=cwd).strip()


def changed_source_shells(
    base: str, current_path: str, cwd: Path = ROOT
) -> set[str] | None:
    """Return changed shell sections, or None when the whole source is affected."""
    try:
        current_text = Path(cwd, current_path).read_text()
        old_text = git("show", f"{base}:validity/sources.toml", cwd=cwd)
    except FileNotFoundError:
        return None
    except SelectorError as exc:
        if "does not exist in" in str(exc) or "exists on disk, but not in" in str(exc):
            return None
        raise
    try:
        current = cast(dict[str, object], tomllib.loads(current_text))
        old = cast(dict[str, object], tomllib.loads(old_text))
    except tomllib.TOMLDecodeError as exc:
        raise SelectorError(f"validity/sources.toml: invalid TOML: {exc}") from exc
    current_shells = current.get("shell")
    old_shells = old.get("shell")
    if not isinstance(current_shells, dict) or not isinstance(old_shells, dict):
        raise SelectorError("validity/sources.toml: expected [shell.NAME] tables")
    current_shells = cast(dict[str, object], current_shells)
    old_shells = cast(dict[str, object], old_shells)
    if current.get("defaults") != old.get("defaults"):
        return None
    return {
        shell
        for shell in set(current_shells) | set(old_shells)
        if current_shells.get(shell) != old_shells.get(shell)
    }


def build_inputs(cell: Cell) -> dict[str, object]:
    """Fields which change the image build; omit digest and runtime metadata."""
    return {
        key: cell[key]
        for key in ("shell", "version", "image", "base", "dockerfile", "source")
    }


def affected(
    base: str | None, matrix_path: str = DEFAULT_MATRIX, cwd: Path = ROOT
) -> list[str]:
    current_text = Path(cwd, matrix_path).read_text()
    current = load_matrix(current_text, matrix_path)
    selected = {cell_id(cell) for cell in current if not cell.get("digest", "").strip()}
    if base is None:
        return [cell_id(cell) for cell in current if cell_id(cell) in selected]

    ancestor = merge_base(base, cwd)
    old_text, old_exists = show_matrix(ancestor, matrix_path, cwd)
    old = (
        load_matrix(old_text, f"{ancestor}:{matrix_path}")
        if old_exists and old_text is not None
        else []
    )
    current_by_id = {cell_id(cell): cell for cell in current}
    old_by_id = {cell_id(cell): cell for cell in old}
    selected.update(
        ident
        for ident, cell in current_by_id.items()
        if ident not in old_by_id
        or build_inputs(old_by_id[ident]) != build_inputs(cell)
    )
    paths = changed_paths(ancestor, cwd)

    for path in paths:
        if path == matrix_path:
            selected.update(
                ident
                for ident, cell in current_by_id.items()
                if ident not in old_by_id
                or build_inputs(old_by_id[ident]) != build_inputs(cell)
            )
        elif path == "validity/sources.toml":
            shells = changed_source_shells(ancestor, path, cwd)
            if shells is None:
                selected.update(current_by_id)
            else:
                selected.update(
                    ident
                    for ident, cell in current_by_id.items()
                    if cell["shell"] in shells
                )
        elif path == "docker/shells/fetch.sh":
            selected.update(current_by_id)
        elif path.startswith("docker/shells/vm/"):
            selected.update(
                ident for ident, cell in current_by_id.items() if cell.get("vm", False)
            )
        elif path.startswith("docker/shells/"):
            parts = path.split("/")
            if len(parts) >= 3:
                dockerfile = parts[2]
                selected.update(
                    ident
                    for ident, cell in current_by_id.items()
                    if cell["dockerfile"] == dockerfile
                )
        elif (
            path.startswith(("validity/specs/", "docs/", "doc/"))
            or path in {"validity/outcomes.toml", "validity/REPORT.md"}
            or path.endswith((".md", ".svg", ".png"))
        ):
            continue
        elif path == "crates/conformance/src/validity/docker.rs":
            selected.update(current_by_id)

    return [cell_id(cell) for cell in current if cell_id(cell) in selected]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("--base", help="commit to compare for changed build inputs")
    _ = parser.add_argument(
        "--matrix", default=DEFAULT_MATRIX, help="current matrix path"
    )
    args = parser.parse_args(argv)
    base = cast(str | None, args.base)
    matrix = cast(str, args.matrix)
    try:
        print(json.dumps(affected(base, matrix)))
    except (OSError, SelectorError) as exc:
        print(f"affected_shell_cells: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
