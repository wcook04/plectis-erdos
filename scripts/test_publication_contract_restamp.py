#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Contract: a digest restamp follows a rebuilt pair and refuses a stale PDF.

Every publication artifact is a ``.tex`` and the ``.pdf`` built from it, both
pinned by digest in ``docs/publication_contract.json``. Revising a manuscript
therefore makes the registry stale, and until this route existed a contributor
could only hand-edit sha256 strings or leave the contract check permanently
red. Both of those are ways a published digest stops meaning anything.

So the route carries an obligation, and this is where it is tested. The
dangerous restamp is the one that stamps a new source onto a PDF nobody
rebuilt: the registry would then name a manuscript the released artifact does
not print, and the digest would certify the mismatch instead of catching it.
That case must be refused by name, and the restamp must never reach a title,
claim scope, or authority posture, which are human judgments about what an
artifact asserts rather than facts about its bytes.
"""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

from publication_contract import (
    CONTRACT_PATH,
    RepositoryReader,
    apply_artifact_digest_restamps,
    artifact_digest_restamp_plan,
    sha256,
)


OLD_SOURCE = b"\\documentclass{article}\\begin{document}old\\end{document}\n"
NEW_SOURCE = b"\\documentclass{article}\\begin{document}new\\end{document}\n"
OLD_RENDER = b"%PDF-1.5 old\n"
NEW_RENDER = b"%PDF-1.5 new\n"


def require(condition: bool, message: str) -> None:
    """Keep restamp-guard failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def sample_contract() -> dict:
    """One registry row pinned to ``OLD_SOURCE`` and ``OLD_RENDER``."""
    return {
        "artifacts": [
            {
                "id": "sample_note",
                "title": "A Sample Note",
                "claim_scope": "The problem remains open.",
                "authority_posture": "authored_exposition_not_Lean_proof_authority",
                "source_path": "paper/sample.tex",
                "source_content_digest": sha256(OLD_SOURCE),
                "rendered_path": "sample.pdf",
                "rendered_content_digest": sha256(OLD_RENDER),
            }
        ]
    }


def reader_over(contract: dict, source: bytes, render: bytes) -> RepositoryReader:
    return RepositoryReader(
        Path("/nonexistent"),
        byte_overrides={
            CONTRACT_PATH: json.dumps(contract).encode("utf-8"),
            "paper/sample.tex": source,
            "sample.pdf": render,
        },
    )


def check_matching_pair_needs_no_restamp() -> None:
    """A registry that already describes its files must plan nothing."""
    restamps, refusals = artifact_digest_restamp_plan(
        reader_over(sample_contract(), OLD_SOURCE, OLD_RENDER)
    )
    require(not restamps, f"restamped an artifact that had not moved: {restamps}")
    require(not refusals, f"refused an artifact that was already current: {refusals}")


def check_rebuilt_pair_is_restamped() -> None:
    """Source and PDF that moved together are the case a restamp exists for."""
    restamps, refusals = artifact_digest_restamp_plan(
        reader_over(sample_contract(), NEW_SOURCE, NEW_RENDER)
    )
    require(not refusals, f"refused a properly rebuilt pair: {refusals}")
    moved = {record["field"]: record["actual"] for record in restamps}
    require(
        moved
        == {
            "source_content_digest": sha256(NEW_SOURCE),
            "rendered_content_digest": sha256(NEW_RENDER),
        },
        f"restamp plan did not follow the rebuilt pair: {moved}",
    )


def check_source_without_rebuilt_pdf_is_refused() -> None:
    """The published PDF still prints the old source; stamping it would lie."""
    restamps, refusals = artifact_digest_restamp_plan(
        reader_over(sample_contract(), NEW_SOURCE, OLD_RENDER)
    )
    require(
        not restamps,
        f"restamped a source whose PDF was never rebuilt: {restamps}",
    )
    require(len(refusals) == 1, f"expected one refusal, got {refusals}")
    require(
        "was never rebuilt" in refusals[0] and "make -C paper sample.pdf" in refusals[0],
        f"refusal did not name the rebuild it needs: {refusals[0]}",
    )


def check_rebuilt_pdf_alone_is_restamped() -> None:
    """Rebuilding a PDF from an unchanged source is ordinary, not suspicious."""
    restamps, refusals = artifact_digest_restamp_plan(
        reader_over(sample_contract(), OLD_SOURCE, NEW_RENDER)
    )
    require(not refusals, f"refused a plain rebuild: {refusals}")
    require(
        [record["field"] for record in restamps] == ["rendered_content_digest"],
        f"a plain rebuild moved more than the rendered digest: {restamps}",
    )


def check_unreadable_artifact_is_refused() -> None:
    """A missing file cannot be digested, so it cannot be silently skipped."""
    contract = sample_contract()
    reader = RepositoryReader(
        Path("/nonexistent"),
        byte_overrides={
            CONTRACT_PATH: json.dumps(contract).encode("utf-8"),
            "paper/sample.tex": NEW_SOURCE,
        },
    )
    restamps, refusals = artifact_digest_restamp_plan(reader)
    require(not restamps, f"restamped an artifact it could not read: {restamps}")
    require(
        len(refusals) == 1 and "unreadable" in refusals[0],
        f"missing rendered artifact was not refused: {refusals}",
    )


def check_apply_touches_only_the_digests() -> None:
    """Titles and claim scopes are human judgments; a restamp must not move one."""
    contract = sample_contract()
    with tempfile.TemporaryDirectory(prefix="publication-restamp-") as temporary:
        root = Path(temporary)
        (root / "docs").mkdir()
        original = json.dumps(contract, indent=2) + "\n"
        (root / CONTRACT_PATH).write_text(original, encoding="utf-8")
        restamps, _ = artifact_digest_restamp_plan(
            reader_over(contract, NEW_SOURCE, NEW_RENDER)
        )
        apply_artifact_digest_restamps(root, restamps)
        written = json.loads((root / CONTRACT_PATH).read_text(encoding="utf-8"))
    row = written["artifacts"][0]
    require(
        row["source_content_digest"] == sha256(NEW_SOURCE)
        and row["rendered_content_digest"] == sha256(NEW_RENDER),
        "apply did not write the planned digests",
    )
    kept = {key: value for key, value in row.items() if not key.endswith("_digest")}
    expected = {
        key: value
        for key, value in contract["artifacts"][0].items()
        if not key.endswith("_digest")
    }
    require(kept == expected, f"apply moved a non-digest field: {kept}")


def check_apply_refuses_an_ambiguous_digest() -> None:
    """A digest the plan cannot locate exactly once must not be guessed at."""
    with tempfile.TemporaryDirectory(prefix="publication-restamp-") as temporary:
        root = Path(temporary)
        (root / "docs").mkdir()
        (root / CONTRACT_PATH).write_text("{}\n", encoding="utf-8")
        try:
            apply_artifact_digest_restamps(
                root,
                [
                    {
                        "artifact_id": "sample_note",
                        "field": "source_content_digest",
                        "path": "paper/sample.tex",
                        "expected": sha256(OLD_SOURCE),
                        "actual": sha256(NEW_SOURCE),
                    }
                ],
            )
        except ValueError as error:
            require("appears 0 times" in str(error), str(error))
        else:
            raise AssertionError("apply rewrote a registry that lacked the digest")


def main() -> int:
    check_matching_pair_needs_no_restamp()
    check_rebuilt_pair_is_restamped()
    check_source_without_rebuilt_pdf_is_refused()
    check_rebuilt_pdf_alone_is_restamped()
    check_unreadable_artifact_is_refused()
    check_apply_touches_only_the_digests()
    check_apply_refuses_an_ambiguous_digest()
    print(
        "publication digest restamp guard: PASS; a restamp follows a rebuilt "
        "pair, refuses a source whose PDF was never rebuilt, and moves no "
        "claim-bearing field"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
