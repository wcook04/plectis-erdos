#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the public checkout from silently regressing into a giant clone."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
MIB = 1024 * 1024
FULL_CHECKOUT_LIMIT_BYTES = 420 * MIB
LEAN_CHECKOUT_LIMIT_BYTES = 160 * MIB
SINGLE_BLOB_LIMIT_BYTES = 100 * MIB
MINIMUM_LEAN_CHECKOUT_REDUCTION = 0.50
LEAN_LIBRARY_PREFIXES = ("Erdos249257/", "ErdosProblems/")
LEAN_CLONE_COMMAND = (
    "git clone --filter=blob:none --sparse "
    "https://github.com/wcook04/plectis-lean-erdos249-257.git"
)
LEAN_SPARSE_COMMAND = (
    "git -C plectis-lean-erdos249-257 sparse-checkout set "
    "Erdos249257 ErdosProblems"
)
FULL_CLONE_COMMAND = (
    "git clone --filter=blob:none "
    "https://github.com/wcook04/plectis-lean-erdos249-257.git"
)


def committed_entries(root: Path = ROOT, revision: str = "HEAD") -> list[dict[str, Any]]:
    """Read checkout-relevant blob sizes without opening their contents."""

    result = subprocess.run(
        ["git", "-C", str(root), "ls-tree", "-r", "-l", "-z", revision],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    entries: list[dict[str, Any]] = []
    for raw_record in result.stdout.split(b"\0"):
        if not raw_record:
            continue
        metadata, raw_path = raw_record.split(b"\t", 1)
        mode, object_type, object_id, raw_size = metadata.split()
        if object_type != b"blob":
            continue
        entries.append(
            {
                "mode": mode.decode("ascii"),
                "object_id": object_id.decode("ascii"),
                "size_bytes": 0 if raw_size == b"-" else int(raw_size),
                "path": raw_path.decode("utf-8"),
            }
        )
    return entries


def belongs_to_lean_cone(path: str) -> bool:
    """Match what Git cone-mode sparse checkout materializes for two roots."""

    return "/" not in path or path.startswith(LEAN_LIBRARY_PREFIXES)


def build_report(entries: Iterable[dict[str, Any]]) -> dict[str, Any]:
    rows = list(entries)
    full_bytes = sum(int(row["size_bytes"]) for row in rows)
    lean_bytes = sum(
        int(row["size_bytes"])
        for row in rows
        if belongs_to_lean_cone(str(row["path"]))
    )
    largest = max(rows, key=lambda row: int(row["size_bytes"]), default=None)
    reduction = (full_bytes - lean_bytes) / full_bytes if full_bytes else 0.0
    return {
        "schema": "plectis_clone_footprint_v1",
        "full_checkout_bytes": full_bytes,
        "full_checkout_limit_bytes": FULL_CHECKOUT_LIMIT_BYTES,
        "lean_sparse_checkout_bytes": lean_bytes,
        "lean_sparse_checkout_limit_bytes": LEAN_CHECKOUT_LIMIT_BYTES,
        "lean_sparse_omitted_bytes": full_bytes - lean_bytes,
        "lean_sparse_reduction_fraction": round(reduction, 6),
        "minimum_lean_sparse_reduction_fraction": MINIMUM_LEAN_CHECKOUT_REDUCTION,
        "single_blob_limit_bytes": SINGLE_BLOB_LIMIT_BYTES,
        "largest_blob": largest,
        "tracked_blob_count": len(rows),
        "scope": "committed_tree_checkout_bytes_not_network_pack_bytes",
    }


def contract_errors(report: dict[str, Any], readme: str) -> list[str]:
    errors: list[str] = []
    if int(report["full_checkout_bytes"]) > FULL_CHECKOUT_LIMIT_BYTES:
        errors.append("committed full checkout exceeds the 420 MiB clone budget")
    if int(report["lean_sparse_checkout_bytes"]) > LEAN_CHECKOUT_LIMIT_BYTES:
        errors.append("advertised Lean sparse checkout exceeds the 160 MiB budget")
    largest = report.get("largest_blob")
    if isinstance(largest, dict) and int(largest["size_bytes"]) > SINGLE_BLOB_LIMIT_BYTES:
        errors.append(
            f"committed blob exceeds the 100 MiB budget: {largest['path']}"
        )
    if float(report["lean_sparse_reduction_fraction"]) < MINIMUM_LEAN_CHECKOUT_REDUCTION:
        errors.append("Lean sparse checkout no longer omits at least half the full tree")
    for command in (LEAN_CLONE_COMMAND, LEAN_SPARSE_COMMAND, FULL_CLONE_COMMAND):
        if command not in readme:
            errors.append(f"README is missing optimized clone command: {command}")
    lean_position = readme.find(LEAN_CLONE_COMMAND)
    full_position = readme.find(FULL_CLONE_COMMAND, lean_position + len(LEAN_CLONE_COMMAND))
    if lean_position < 0 or full_position < 0 or lean_position > full_position:
        errors.append("README must offer the Lean sparse checkout before the full checkout")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail when a clone budget regresses")
    parser.add_argument("--revision", default="HEAD")
    args = parser.parse_args(argv)
    report = build_report(committed_entries(ROOT, args.revision))
    errors = contract_errors(report, (ROOT / "README.md").read_text(encoding="utf-8"))
    report["status"] = "pass" if not errors else "fail"
    report["errors"] = errors
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if args.check and errors else 0


if __name__ == "__main__":
    sys.exit(main())
