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
                if row["adapter"]["status"] == "checked_against_upstream_statement"
            },
            {257, 1049},
        )
        # The adapter discharges upstream's stated variants. Both problems
        # themselves remain open, and the crosswalk must keep saying so.
        #
        # This previously asserted that no row had reached SUBMITTED, which
        # was true only while nothing had been offered upstream; as a contract
        # it forbade the very outcome the ladder exists to record. What must
        # actually hold is that offering a variant upstream never becomes a
        # claim on the open problem, and that a submission names the pull
        # request carrying it.
        for row in self.manifest["problems"]:
            self.assertFalse(
                row["adapter"].get("candidate_is_a_proof", False),
                f"problem {row['problem']} must not claim to prove the open problem",
            )
            self.assertTrue(row["human_semantic_review_required"])
            if row["submission_status"] == crosswalk.SUBMITTED:
                submission = row.get("submission")
                self.assertIsInstance(submission, dict)
                self.assertIsInstance(submission["pull_request"], int)
                self.assertTrue(
                    submission["url"].startswith(crosswalk.UPSTREAM_PR_PREFIX)
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

    def test_bare_checked_equivalence_string_is_rejected(self) -> None:
        """A claim that carries no evidence at all is still refused.

        The earlier contract refused every checked-equivalence claim outright.
        That was right while no adapter existed, but it also made the true
        state unrecordable once one did, so the rule is now that a claim must
        be evidenced rather than that it must be absent.  This test pins the
        half that must not weaken.
        """
        mutated = copy.deepcopy(self.manifest)
        mutated["problems"][1]["comparison"]["machine_checked_equivalence"] = "proved"
        self.assertTrue(
            any(
                "must be 'none' or an object" in error
                for error in self.errors(mutated)
            )
        )

    def test_checked_equivalence_needs_an_adapter_module_on_disk(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        claim = mutated["problems"][4]["comparison"]["machine_checked_equivalence"]
        claim["adapter_module"] = "adapters/DoesNotExist.lean"
        self.assertTrue(
            any("is absent from this repository" in e for e in self.errors(mutated))
        )

    def test_checked_equivalence_needs_the_named_theorem(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        claim = mutated["problems"][4]["comparison"]["machine_checked_equivalence"]
        claim["adapter_declaration"] = (
            "Erdos249257.FormalConjecturesAdapter.theorem_that_was_never_written"
        )
        self.assertTrue(
            any("does not state theorem" in e for e in self.errors(mutated))
        )

    def test_checked_equivalence_needs_the_named_namespace(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        claim = mutated["problems"][4]["comparison"]["machine_checked_equivalence"]
        claim["adapter_declaration"] = (
            "Some.Other.Namespace.erdos_257_variants_tsum_top"
        )
        self.assertTrue(
            any("does not open namespace" in e for e in self.errors(mutated))
        )

    def test_sorry_ax_in_the_axiom_budget_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        claim = mutated["problems"][4]["comparison"]["machine_checked_equivalence"]
        claim["axioms"] = list(claim["axioms"]) + ["sorryAx"]
        self.assertTrue(
            any("axiom budget contains sorryAx" in e for e in self.errors(mutated))
        )

    def test_ladder_cannot_be_climbed_without_evidence(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        row = mutated["problems"][0]
        self.assertEqual(row["comparison"]["machine_checked_equivalence"], "none")
        row["submission_status"] = "adapter_checked_pending_external_process"
        self.assertTrue(
            any(
                "requires a verified machine-checked equivalence" in e
                for e in self.errors(mutated)
            )
        )

    def test_submitted_without_a_pull_request_is_rejected(self) -> None:
        """SUBMITTED asserts an outward act; it must name what carries it.

        Without a reference the status is unfalsifiable -- a reader has
        nothing to open and nothing to disagree with.
        """
        mutated = copy.deepcopy(self.manifest)
        row = next(
            r for r in mutated["problems"]
            if r["submission_status"] == crosswalk.SUBMITTED
        )
        row.pop("submission", None)
        errors = self.errors(mutated)
        self.assertTrue(
            any("submission block" in e for e in errors), errors
        )

    def test_submitted_pointing_off_upstream_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        row = next(
            r for r in mutated["problems"]
            if r["submission_status"] == crosswalk.SUBMITTED
        )
        row["submission"]["url"] = "https://example.com/pull/1"
        errors = self.errors(mutated)
        self.assertTrue(any("submission.url" in e for e in errors), errors)

    def test_invented_submission_status_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        mutated["problems"][0]["submission_status"] = "accepted_by_deepmind"
        self.assertTrue(
            any("must be one of the ladder rungs" in e for e in self.errors(mutated))
        )

    def test_cross_index_section_cannot_be_dropped(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        del mutated["cross_index_matches"]
        self.assertTrue(
            any("must carry a cross_index_matches" in e for e in self.errors(mutated))
        )

    def test_cross_index_match_cannot_be_invented(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        invented = copy.deepcopy(mutated["cross_index_matches"][0])
        invented["upstream_declaration"] = "Erdos999.erdos_999.variants.imagined"
        mutated["cross_index_matches"].append(invented)
        self.assertTrue(
            any("unrecognised entries" in e for e in self.errors(mutated))
        )

    def test_cross_index_ladder_also_needs_evidence(self) -> None:
        mutated = copy.deepcopy(self.manifest)
        mutated["cross_index_matches"][0]["machine_checked_equivalence"] = "none"
        self.assertTrue(
            any(
                "requires a verified machine-checked equivalence" in e
                for e in self.errors(mutated)
            )
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
