#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for the Formal Conjectures crosswalk contract."""

from __future__ import annotations

import copy
import importlib.util
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "check_formal_conjectures_crosswalk.py"
SPEC = importlib.util.spec_from_file_location("formal_conjectures_crosswalk", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
crosswalk = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(crosswalk)


class FormalConjecturesCrosswalkTest(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = crosswalk.load_json(crosswalk.CROSSWALK_PATH)
        self.problem_index = crosswalk.load_json(crosswalk.PROBLEM_INDEX_PATH)
        self.projection = crosswalk.render_markdown(
            self.manifest, self.problem_index
        )

    def errors(
        self,
        manifest: dict | None = None,
        problem_index: dict | None = None,
        projection: str | None = None,
    ) -> list[str]:
        return crosswalk.crosswalk_errors(
            self.manifest if manifest is None else manifest,
            self.problem_index if problem_index is None else problem_index,
            self.projection if projection is None else projection,
        )

    def test_live_crosswalk_satisfies_offline_contract(self) -> None:
        self.assertEqual(self.errors(), [])
        self.assertEqual(len(self.manifest["problems"]), 8)
        self.assertEqual(
            {
                row["problem"]
                for row in self.manifest["problems"]
                if row["adapter"]["status"]
                == "candidate_requires_human_semantic_review"
            },
            {257, 1049},
        )

    def test_commit_pin_mutation_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        mutated["upstream"]["commit"] = "0" * 40
        self.assertTrue(any("commit pin" in error for error in self.errors(mutated)))

    def test_source_hash_mutation_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        mutated["problems"][0]["upstream_source"]["sha256"] = "0" * 64
        self.assertTrue(
            any("upstream sha256" in error for error in self.errors(mutated))
        )

    def test_missing_comparison_axis_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        del mutated["problems"][0]["comparison"]["indexing"]
        self.assertTrue(
            any("missing comparison axes" in error for error in self.errors(mutated))
        )

    def test_checked_equivalence_claim_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        mutated["problems"][1]["comparison"]["machine_checked_equivalence"] = (
            "proved"
        )
        self.assertTrue(
            any("must not claim checked equivalence" in error for error in self.errors(mutated))
        )

    def test_non_candidate_cannot_be_promoted(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        mutated["problems"][0]["adapter"]["status"] = (
            "candidate_requires_human_semantic_review"
        )
        self.assertTrue(
            any("only #257 and #1049" in error for error in self.errors(mutated))
        )

    def test_candidate_cannot_be_marked_ready_or_proved(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        row = next(row for row in mutated["problems"] if row["problem"] == 257)
        row["submission_status"] = "ready_to_submit"
        row["adapter"]["candidate_is_a_proof"] = True
        errors = self.errors(mutated)
        self.assertTrue(any("submission status" in error for error in errors))
        self.assertTrue(any("must not be called a proof" in error for error in errors))

    def test_local_problem_must_remain_open(self) -> None:
        mutated = copy.deepcopy(self.problem_index)
        mutated["problems"][0]["status"] = "solved"
        self.assertTrue(
            any("must remain open" in error for error in self.errors(problem_index=mutated))
        )

    def test_projection_drift_is_rejected(self) -> None:
        drifted = self.projection.replace("8/8", "7/8") + "\nmanual edit\n"
        self.assertTrue(
            any("FORMAL_CONJECTURES_CROSSWALK.md drifted" in error for error in self.errors(projection=drifted))
        )

    def test_upstream_byte_anchor_and_coordinate_verification(self) -> None:
        source_text = "namespace Erdos68\ntheorem erdos_68 : True := by trivial\n"
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            path = checkout / "FormalConjectures/ErdosProblems/68.lean"
            path.parent.mkdir(parents=True)
            path.write_text(source_text, encoding="utf-8")
            manifest = {
                "problems": [
                    {
                        "problem": 68,
                        "upstream_source": {
                            "path": "FormalConjectures/ErdosProblems/68.lean",
                            "sha256": crosswalk.sha256_bytes(source_text.encode()),
                            "primary_declaration": "Erdos68.erdos_68",
                            "declaration_line": 2,
                            "signature_anchors": ["theorem erdos_68 : True"],
                            "related_declarations": [],
                        },
                    }
                ]
            }
            completed = SimpleNamespace(
                returncode=0, stdout=crosswalk.UPSTREAM_COMMIT + "\n"
            )
            with patch.object(crosswalk.subprocess, "run", return_value=completed):
                self.assertEqual(
                    crosswalk.upstream_checkout_errors(manifest, checkout), []
                )
                path.write_text(source_text.replace("True", "False"), encoding="utf-8")
                errors = crosswalk.upstream_checkout_errors(manifest, checkout)
            self.assertTrue(any("SHA-256" in error for error in errors))
            self.assertTrue(any("lost signature anchor" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
