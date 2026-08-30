#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the declaration atlas bound to the committed Lean source authority.

The atlas is a generated projection, so a checkout may contain unrelated
uncommitted Lean edits while this contract still needs to answer one precise
question: does the tracked projection describe ``HEAD``?  The builder's own
path order and digest framing are reused, while Git supplies the committed
bytes.  No transient declaration count, roster order, or top-N sample is
encoded here.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ATLAS = ROOT / "docs" / "declaration_atlas.json"


def require(condition: bool, message: str) -> None:
    """Keep source-currentness failures active under ``python -O``."""
    if not condition:
        raise AssertionError(message)


def load_builder():
    spec = importlib.util.spec_from_file_location(
        "build_declaration_atlas", ROOT / "scripts" / "build_declaration_atlas.py"
    )
    require(spec is not None and spec.loader is not None, "could not load atlas builder")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def committed_source_fingerprint(builder) -> str:
    """Hash ``HEAD`` Lean blobs in exactly the builder's source-path order."""
    paths = [path.relative_to(ROOT).as_posix() for path in builder.source_paths()]
    request = "".join(f"HEAD:{relative}\n" for relative in paths).encode("utf-8")
    completed = subprocess.run(
        ["git", "cat-file", "--batch"],
        cwd=ROOT,
        input=request,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    require(
        completed.returncode == 0,
        "git cat-file could not read committed Lean source: "
        + completed.stderr.decode("utf-8", errors="replace").strip(),
    )

    digest = hashlib.sha256()
    output = completed.stdout
    offset = 0
    for relative in paths:
        newline = output.find(b"\n", offset)
        require(newline >= 0, f"missing git object header for {relative}")
        header = output[offset:newline].split()
        require(len(header) >= 3 and header[1] == b"blob", f"{relative} is not a blob")
        try:
            size = int(header[2])
        except ValueError as exc:
            raise AssertionError(f"invalid git object size for {relative}") from exc
        start = newline + 1
        end = start + size
        data = output[start:end]
        require(len(data) == size, f"truncated git object for {relative}")
        require(output[end : end + 1] == b"\n", f"missing git object terminator for {relative}")
        builder._update_source_digest(digest, relative, data.decode("utf-8"))
        offset = end + 1
    return f"sha256:{digest.hexdigest()}"


def test_atlas_tracks_committed_source() -> None:
    builder = load_builder()
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    expected = committed_source_fingerprint(builder)
    require(
        atlas.get("source_fingerprint") == expected,
        "declaration atlas source fingerprint is stale relative to committed HEAD",
    )


def test_atlas_module_and_coordinate_identity() -> None:
    builder = load_builder()
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    source_paths = {
        path.relative_to(ROOT).as_posix() for path in builder.source_paths()
    }
    modules = {row["path"] for row in atlas["modules"]}
    require(modules == source_paths, "atlas module set diverges from builder source authority")

    declarations = atlas["declarations"]
    coordinates = {(row["module"], row["line"], row["name"]) for row in declarations}
    require(len(coordinates) == len(declarations), "atlas declaration coordinates are not unique")
    require(
        all(row["module"] in source_paths and row["line"] >= 1 for row in declarations),
        "atlas declaration row escapes a registered source module",
    )
    require(
        atlas["summary"]["module_count"] == len(modules)
        and atlas["summary"]["declaration_count"] == len(declarations),
        "atlas summary does not describe its complete registered rows",
    )


if __name__ == "__main__":
    test_atlas_tracks_committed_source()
    test_atlas_module_and_coordinate_identity()
    print("declaration atlas source-currentness: ok")
