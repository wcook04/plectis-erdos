#!/usr/bin/env python3
"""Self-contained fixture coverage for assimilation_surface.py."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

from assimilation_surface import assimilation_card


def _write(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = payload if isinstance(payload, str) else json.dumps(payload, indent=1)
    path.write_text(text, encoding="utf-8")


def _fixture(root: Path) -> tuple[Path, Path]:
    repo_root = root / "repo"
    project_root = repo_root / "formal_math" / "erdos257_period_noncollapse"

    _write(
        project_root / "ErdosProblems" / "assimilation_manifest.json",
        {
            "problems": [
                {
                    "id": "erdos_777",
                    "directory": "ErdosProblems/Erdos777",
                    "packet": "ErdosProblems/Erdos777/research_packet.json",
                    "lean_module": "ErdosProblems.Erdos777.Example",
                }
            ]
        },
    )
    _write(
        project_root / "ErdosProblems" / "Erdos777" / "research_packet.json",
        {
            "problem_id": "erdos_777",
            "top_level_note": "no boundary marker here",
            "exact_results": [
                {
                    "id": "first",
                    "claim_boundary": "The transfer is an ordinary proof, not formalised.",
                },
                {"id": "second", "claim_boundary": "Exact and unconditional."},
            ],
            "landed_formal_source": [
                {"authority_boundary": "Lean checks the finite part; the rest awaits work."}
            ],
        },
    )

    # Two comparator directories: one complete, one missing two required files.
    complete = project_root / "ExternalVerification777Complete"
    for name in ("Challenge.lean", "Solution.lean", "formalization.yaml"):
        _write(complete / name, "-- fixture\n")
    _write(complete / "comparator.json", {"theorem_names": ["A.b", "A.c"]})
    partial = project_root / "ExternalVerification777Partial"
    _write(partial / "Challenge.lean", "-- fixture\n")
    _write(partial / "Solution.lean", "-- fixture\n")

    state = repo_root / "state" / "formal_math"
    _write(
        state / "claim_frontier_v1.json",
        {
            "claims": {
                "erdos777.backed": {
                    "altitude": "no_go",
                    "band": "U",
                    "evidence": {
                        "class": "lean_kernel_checked",
                        "lean": {
                            "status": "all_declarations_located",
                            "verified": [{"declaration": "d"}],
                            "missing": [],
                        },
                    },
                },
                "erdos777.paper_only": {
                    "altitude": "genuine_climb",
                    "band": "P",
                    "evidence": {"class": "ordinary_proof"},
                },
                "erdos888.other_problem": {
                    "altitude": "no_go",
                    "band": "U",
                    "evidence": {"class": "ordinary_proof"},
                },
            }
        },
    )
    _write(
        state / "erdos777" / "probe_receipt.json",
        {
            "mechanism_bindings": {
                "problem_id": "erdos_777",
                "motivated_by": ["first"],
                "supports": ["first"],
                "eliminates": [],
            }
        },
    )
    _write(
        state / "erdos888" / "other_receipt.json",
        {"mechanism_bindings": {"problem_id": "erdos_888", "motivated_by": ["x"]}},
    )

    batches = state / "type_b_return_batches"
    _write(
        batches / "erdos777_wave" / "intake.json",
        {
            "batch_id": "erdos777_wave",
            "campaign": "returns for erdos777",
            "arrival_state": "open",
            "returns": [
                {"return_id": "erdos777_first_return"},
                {"return_id": "shared_context_note"},
            ],
        },
    )
    # A capsule that only mentions the project PATH must not be attributed here.
    _write(
        batches / "unrelated_wave" / "intake.json",
        {
            "batch_id": "unrelated_wave",
            "campaign": "returns for something else",
            "arrival_state": "closed",
            "returns": [
                {
                    "return_id": "other_return",
                    "preserved_source": (
                        "formal_math/erdos257_period_noncollapse/ErdosProblems/"
                        "Erdos777/note.md"
                    ),
                }
            ],
        },
    )
    return project_root, repo_root


def main() -> int:
    with tempfile.TemporaryDirectory() as temporary_directory:
        project_root, repo_root = _fixture(Path(temporary_directory))
        card = assimilation_card(project_root, repo_root, "777")

        assert card["problem_id"] == "erdos_777"
        assert card["supported_lean_module"] == "ErdosProblems.Erdos777.Example"

        # Custody matches on identity fields only, never on a source path that
        # happens to contain the project directory name.
        batch_ids = [row["batch_id"] for row in card["custody"]]
        assert batch_ids == ["erdos777_wave"], batch_ids
        assert card["custody"][0]["returns_naming_this_problem"] == [
            "erdos777_first_return"
        ]
        assert card["custody"][0]["recorded_returns"] == 2
        assert "type_b_return_intake.py verify" in card["custody"][0]["verify_command"]

        # Boundaries are collected from nested fields, and only when the text
        # actually names a gap.
        fields = {row["packet_field"] for row in card["declared_lean_boundary"]}
        assert fields == {
            "exact_results[0].claim_boundary",
            "landed_formal_source[0].authority_boundary",
        }, fields

        claims = card["claims"]
        assert [c["claim_id"] for c in claims["lean_backed"]] == ["erdos777.backed"]
        assert [c["claim_id"] for c in claims["not_lean_backed"]] == [
            "erdos777.paper_only"
        ]
        assert claims["upgrade_candidates"] == ["erdos777.paper_only"]

        entries = {row["directory"]: row for row in card["comparator_entries"]}
        assert set(entries) == {
            "ExternalVerification777Complete",
            "ExternalVerification777Partial",
        }
        assert entries["ExternalVerification777Complete"]["missing_palomar_files"] == []
        assert (
            entries["ExternalVerification777Complete"]["audited_declaration_count"] == 2
        )
        assert entries["ExternalVerification777Partial"]["missing_palomar_files"] == [
            "comparator.json",
            "formalization.yaml",
        ]

        receipts = [row["receipt_ref"] for row in card["probe_receipts"]]
        assert receipts == ["state/formal_math/erdos777/probe_receipt.json"], receipts

        commands = [row["command"] for row in card["downstream_surfaces"]]
        assert any("lean_fast_build.py" in c for c in commands)
        assert any("build_claim_frontier.py" in c for c in commands)
        assert any("check_problem_corpus_index.py" in c for c in commands)

        # The boundary limit is honoured.
        limited = assimilation_card(project_root, repo_root, "erdos_777", 1)
        assert len(limited["declared_lean_boundary"]) == 1

        try:
            assimilation_card(project_root, repo_root, "999")
        except ValueError as error:
            assert "unknown manifest problem id" in str(error)
        else:  # pragma: no cover - fixture guarantees the raise
            raise AssertionError("unknown problem id must raise")

    print("test_assimilation_surface: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
