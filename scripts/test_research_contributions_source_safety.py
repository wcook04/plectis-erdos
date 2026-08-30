#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep research-return source inputs inside the public receipt boundary."""

from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from unittest.mock import patch

import build_research_contribution_recognition as recognition
import build_research_contributions as builder


ROOT = Path(__file__).resolve().parents[1]
NEGATIVE = ROOT / "docs/research-commons/returns/negative-example.json"
GITHUB_UNACCEPTED = ROOT / ".github/fixtures/unaccepted-research-return.json"


def require(condition: bool, message: object) -> None:
    """Keep source-boundary checks active under ``python3 -O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    hostile = {
        "GIT_DIR": "/foreign/.git",
        "GIT_WORK_TREE": "/foreign",
        "GIT_NAMESPACE": "foreign-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/foreign/",
        "GIT_ASKPASS": "/foreign/askpass",
        "GIT_OPTIONAL_LOCKS": "1",
        "GIT_NO_REPLACE_OBJECTS": "0",
        "PATH": "/foreign/bin",
    }
    with patch.dict(os.environ, hostile, clear=False):
        environment = builder.git_environment()
    for key in builder.GIT_CONTEXT_KEYS | builder.GIT_PROCESS_CONTROL_KEYS:
        require(key not in environment, f"ambient Git state leaked into source loader: {key}")
    require(environment["GIT_ASKPASS"] == "/bin/false", "Git askpass was not disabled")
    require(environment["GIT_OPTIONAL_LOCKS"] == "0", "optional Git locks were not disabled")
    require(environment["GIT_NO_REPLACE_OBJECTS"] == "1", "replacement objects were not disabled")
    require(environment["PATH"] == os.defpath, "ambient helper PATH was retained")

    unsafe_link = builder.receipt_link(
        {
            "receipt_path": "docs/research-commons/returns/accepted) [redirect] % escape.json",
            "return_id": "return-safe",
        }
    )
    require(
        unsafe_link
        == "[receipt:return-safe](returns/accepted%29%20%5Bredirect%5D%20%25%20escape.json)",
        "receipt link did not escape a hostile filename",
    )

    with tempfile.TemporaryDirectory(prefix="contribution-source-safety-") as temporary:
        root = Path(temporary)
        external = root / "external-receipts"
        external.mkdir()
        (external / "negative.json").write_bytes(NEGATIVE.read_bytes())
        substituted = root / "returns"
        substituted.symlink_to(external, target_is_directory=True)
        try:
            builder.load_receipts(substituted)
        except ValueError as exc:
            require(
                "receipt directory path must not traverse symbolic links" in str(exc),
                exc,
            )
        else:
            raise AssertionError("symlinked receipt directory became source authority")
        require(
            (external / "negative.json").read_bytes() == NEGATIVE.read_bytes(),
            "external receipt changed during source rejection",
        )

        regular = root / "regular-receipts"
        regular.mkdir()
        (regular / "negative.json").write_bytes(NEGATIVE.read_bytes())
        (regular / "github.json").write_bytes(GITHUB_UNACCEPTED.read_bytes())
        loaded = builder.load_receipts(regular)
        require(not loaded, "unaccepted source records entered attribution authority")
        projection = builder.build_projection(loaded)
        require(not projection["chronological"], "unaccepted source entered the JSON view")
        human = builder.human_projection(projection).decode("utf-8")
        require(
            "rr-fixture-valid-negative" not in human
            and "rr-fixture-github-unaccepted-return" not in human,
            "unaccepted source entered the human view",
        )
        recognition_projection = recognition.build_recognition(loaded)
        recognition.validate_projection(recognition_projection)
        require(
            recognition_projection["accepted_receipt_count"] == 0,
            "unaccepted source entered recognition authority",
        )

    print(
        json.dumps(
            {
                "schema": "research-contribution-source-safety-test/1",
                "passed": True,
                "adversarial_rejections": [
                    "receipt_directory_symlink",
                    "receipt_filename_markdown_target_injection",
                    "unaccepted_receipt_sources",
                ],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
