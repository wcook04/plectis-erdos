#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Expected, observed, and licensed publication PDFs stay three distinct inputs."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

from publication_contract import (
    contract_publication_pdfs,
    publication_census_errors,
    publication_role,
    tracked_publication_pdfs,
)
from test_license_map_contract import rendered_artifacts


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def write_contract(root: Path, storage_paths: list[str]) -> None:
    (root / "docs").mkdir(exist_ok=True)
    artifacts = [
        {
            "id": f"artifact_{index}",
            "artifact_class": "problem_note",
            "storage_path": path,
            "rendered_path": Path(path).name,
        }
        for index, path in enumerate(storage_paths)
    ]
    (root / "docs/publication_contract.json").write_text(
        json.dumps({"artifacts": artifacts}, indent=2) + "\n", encoding="utf-8"
    )


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="publication-census-") as raw:
        root = Path(raw)
        write_contract(root, ["paper/68/example.pdf"])
        (root / "paper/68").mkdir(parents=True)
        (root / "paper").mkdir(exist_ok=True)
        (root / "paper/example.pdf").write_bytes(b"temporary-build-output")
        extra = root / "paper/68/unregistered.pdf"
        extra.write_bytes(b"unregistered-rendered-bytes")
        expected = contract_publication_pdfs(
            json.loads((root / "docs/publication_contract.json").read_text(encoding="utf-8"))
        )
        observed = tracked_publication_pdfs(root)
        require(
            "paper/68/example.pdf" in expected,
            f"contract lost its registered PDF: {expected}",
        )
        require(
            "paper/68/example.pdf" not in observed,
            f"census invented a missing registered PDF: {observed}",
        )
        require(
            "paper/68/unregistered.pdf" in observed,
            f"census hid an unregistered tracked PDF: {observed}",
        )
        require(
            "paper/example.pdf" not in observed,
            f"census treated Makefile build output as a publication: {observed}",
        )
        helper = rendered_artifacts(root)
        require(
            "paper/68/example.pdf" not in helper,
            "rendered_artifacts still reported a registered PDF that does not exist",
        )
        require(
            "paper/68/unregistered.pdf" in helper,
            "rendered_artifacts still omitted an unexpected PDF that exists",
        )
        errors = publication_census_errors(expected, observed)
        require(
            any("missing registered PDFs" in error for error in errors),
            f"missing registered PDF was not detected: {errors}",
        )
        require(
            any("unregistered tracked PDFs" in error for error in errors),
            f"additional unregistered PDF was not detected: {errors}",
        )

    require(publication_role({"artifact_class": "problem_note"}) == "short", "short role drifted")
    require(
        publication_role({"artifact_class": "mathematical_companion"}) == "long",
        "long role drifted",
    )
    require(
        publication_role({"artifact_class": "archival_joint_manuscript"})
        == "archival_joint_manuscript",
        "archival role drifted",
    )
    print(
        "test_publication_artifact_census: missing registered and extra "
        "unregistered PDFs are both detected; build outputs stay excluded"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
