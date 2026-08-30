#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# Apache-2.0
"""Keep contribution projections bound to the current committed source set."""

from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path

import build_research_contribution_recognition as recognition
import build_research_contributions as builder
import repository_identity as repository_identity_contract


NEGATIVE = builder.RETURNS / "negative-example.json"
GITHUB_UNACCEPTED = builder.ROOT / ".github/fixtures/unaccepted-research-return.json"


def require(condition: bool, message: object) -> None:
    """Keep committed-source checks active under ``python3 -O``."""
    if not condition:
        raise AssertionError(message)


def git_show(commit: str, relative: str) -> subprocess.CompletedProcess[bytes]:
    """Keep committed-source lookup bounded and environment-neutral."""
    try:
        return subprocess.run(
            ["git", "show", f"{commit}:{relative}"],
            cwd=builder.ROOT,
            env=builder.git_environment(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=builder.GIT_LOOKUP_TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(
            "committed source lookup timed out after "
            f"{builder.GIT_LOOKUP_TIMEOUT_SECONDS} seconds"
        ) from exc


def test_git_show_timeout_is_bounded() -> None:
    original_run = subprocess.run
    captured: dict[str, object] = {}

    def timeout(command: list[str], **kwargs: object) -> subprocess.CompletedProcess[bytes]:
        captured.update(kwargs)
        raise subprocess.TimeoutExpired(command, kwargs["timeout"])

    subprocess.run = timeout  # type: ignore[assignment]
    try:
        try:
            git_show("0" * 40, "docs/research-commons/returns/receipt.json")
        except RuntimeError as exc:
            require("timed out" in str(exc), exc)
        else:
            raise AssertionError("timed-out source lookup was accepted")
    finally:
        subprocess.run = original_run
    require(
        captured.get("timeout") == builder.GIT_LOOKUP_TIMEOUT_SECONDS,
        captured,
    )


def main() -> int:
    test_git_show_timeout_is_bounded()
    committed_paths = builder.committed_receipt_paths(builder.RETURNS)
    require(NEGATIVE in committed_paths, "current negative fixture is missing from HEAD")
    committed = builder.committed_receipt_payload(NEGATIVE)
    require(committed == NEGATIVE.read_bytes(), "tracked negative fixture differs from HEAD")

    tracked = builder.load_receipts(builder.RETURNS, require_committed=True)
    require(not tracked, "a non-accepted current receipt entered attribution authority")
    recognition_projection = recognition.build_recognition(
        builder.load_receipts(
            builder.RETURNS,
            require_committed=True,
            repository_identity=repository_identity_contract.load_identity(),
        )
    )
    recognition.validate_projection(recognition_projection)
    require(
        recognition_projection["accepted_receipt_count"] == 0,
        "committed source set entered accepted recognition authority",
    )
    github_return_id = json.loads(GITHUB_UNACCEPTED.read_text(encoding="utf-8"))["return_id"]
    require(
        github_return_id
        not in {row["return_id"] for row in recognition_projection["chronological"]},
        "GitHub submitted return entered committed recognition",
    )

    with tempfile.TemporaryDirectory(prefix="contribution-committed-source-") as temporary:
        external = Path(temporary)
        uncommitted = external / "negative-uncommitted.json"
        uncommitted.write_bytes(NEGATIVE.read_bytes())
        try:
            builder.committed_receipt_payload(uncommitted)
        except ValueError as exc:
            require("receipt source must be committed in HEAD" in str(exc), exc)
        else:
            raise AssertionError("uncommitted receipt became source authority")

    print(
        json.dumps(
            {
                "schema": "research-contribution-committed-source-test/1",
                "passed": True,
                "adversarial_rejections": ["uncommitted_receipt_source"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
