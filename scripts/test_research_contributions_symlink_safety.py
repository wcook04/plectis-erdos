#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Reject symlink substitution in research-return source inputs."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

import build_research_contribution_recognition as recognition
import build_research_contributions as contributions


ROOT = Path(__file__).resolve().parents[1]
NEGATIVE = ROOT / "docs/research-commons/returns/negative-example.json"


def require(condition: bool, message: object) -> None:
    """Keep symlink-boundary checks active under ``python3 -O``."""
    if not condition:
        raise AssertionError(message)


def check_schema_contract_rejects_symlink_components() -> None:
    original_root = recognition.ROOT
    with tempfile.TemporaryDirectory(prefix="recognition-schema-safety-") as temporary:
        root = Path(temporary) / "release"
        outside = Path(temporary) / "outside"
        root.mkdir()
        outside.mkdir()
        (root / "docs" / "research-commons").mkdir(parents=True)
        (outside / "schema").mkdir()
        (root / "docs" / "research-commons" / "schema").symlink_to(
            outside / "schema", target_is_directory=True
        )
        recognition.ROOT = root
        try:
            try:
                recognition.load_schema_contract()
            except ValueError as error:
                require("symbolic link" in str(error), error)
            else:
                raise AssertionError("recognition schema loader followed a symlink")
        finally:
            recognition.ROOT = original_root


def main() -> int:
    check_schema_contract_rejects_symlink_components()
    with tempfile.TemporaryDirectory(prefix="contribution-symlink-safety-") as temporary:
        root = Path(temporary)
        receipt_directory = root / "returns"
        receipt_directory.mkdir()
        (receipt_directory / "negative.json").symlink_to(NEGATIVE)
        try:
            contributions.load_receipts(receipt_directory)
        except ValueError as exc:
            require("symbolic link" in str(exc), exc)
        else:
            raise AssertionError("receipt loader followed a symlinked source")

        outside = root / "outside"
        outside.mkdir()
        linked_directory = root / "linked-returns"
        linked_directory.symlink_to(outside, target_is_directory=True)
        try:
            contributions.load_receipts(linked_directory)
        except ValueError as exc:
            require("symbolic links" in str(exc), exc)
        else:
            raise AssertionError("receipt loader followed a symlinked directory")

        safe_directory = root / "safe-returns"
        safe_directory.mkdir()
        (safe_directory / NEGATIVE.name).write_bytes(NEGATIVE.read_bytes())
        loaded = contributions.load_receipts(safe_directory)
        require(not loaded, "negative fixture became an accepted source")
        projection = recognition.build_recognition(loaded)
        recognition.validate_projection(projection)
        require(
            projection["accepted_receipt_count"] == 0,
            "safe negative source produced an accepted recognition row",
        )

    print(
        json.dumps(
            {
                "schema": "research-contribution-symlink-safety-test/1",
                "passed": True,
                "adversarial_rejections": [
                    "receipt_source_symlink",
                    "receipt_directory_parent_symlink",
                    "schema_directory_symlink",
                ],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
