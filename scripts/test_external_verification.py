#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial contract checks for the external-verification packet."""

from __future__ import annotations

import json
import re
import subprocess
import unittest
from copy import deepcopy
from pathlib import Path

from build_external_verification import imports_in_text, load_owner, validate
from run_external_verification import (
    EXPECTED_1049_MISMATCH,
    EXPECTED_MISMATCH,
    is_expected_negative_rejection,
)

ROOT = Path(__file__).resolve().parent.parent


class ExternalVerificationContractTest(unittest.TestCase):
    def test_projection_and_statement_isolation_are_current(self) -> None:
        subprocess.run(
            ["python3", "scripts/build_external_verification.py", "--check"],
            cwd=ROOT,
            check=True,
        )
        packet = json.loads(
            (ROOT / "docs/external_verification_packet.json").read_text(encoding="utf-8")
        )
        index = packet["problem_index"]
        self.assertEqual(index["problem_count"], 8)
        self.assertEqual(
            [row["erdos_number"] for row in index["problems"]],
            [68, 243, 249, 251, 257, 269, 1041, 1049],
        )
        self.assertEqual({row["status"] for row in index["problems"]}, {"open"})
        self.assertIn("not_a_reviewed_claim_registry", index["authority_posture"])
        self.assertEqual(
            packet["challenge_import_closure"]["internal_paths"],
            ["ExternalVerification/Challenge.lean", "ExternalVerification/Statements.lean"],
        )
        self.assertEqual(
            packet["challenge_import_closure"]["proof_bearing_internal_import_count"], 0
        )
        self.assertEqual(len(packet["main_results"]), 19)
        self.assertEqual(
            {row["problem"] for row in packet["main_results"]},
            {68, 243, 249, 251, 257, 269, 1041, 1049},
        )
        self.assertEqual(len(packet["review_matrix"]), 8)
        family_ids = {
            (problem["problem"], family["id"])
            for problem in packet["review_matrix"]
            for family in problem["families"]
        }
        self.assertTrue(all(
            (result["problem"], result["review_family"]) in family_ids
            for result in packet["main_results"]
        ))
        registered = [row for row in packet["main_results"] if row.get("claim_id")]
        unregistered = [row for row in packet["main_results"] if not row.get("claim_id")]
        self.assertEqual(len(registered), 5)
        self.assertEqual(len(unregistered), 14)
        self.assertTrue(all(
            row["canonical_claim_status"].startswith("supports_registered_claim_family:")
            for row in registered
        ))
        self.assertEqual(
            {row["canonical_claim_status"] for row in unregistered},
            {"comparator_interface_not_registered_as_canonical_claim"},
        )
        self.assertEqual(
            {row["novelty_status"] for row in packet["main_results"]},
            {"unassessed_no_priority_claim"},
        )
        human = (ROOT / "docs/EXTERNAL_VERIFICATION.md").read_text(encoding="utf-8")
        self.assertIn("> [!IMPORTANT]", human)
        self.assertIn("# Plectis verification: eight open Erdős programmes", human)
        self.assertIn("## #68: Factorial-denominator series", human)
        self.assertIn("## #269: Three-prime running least common multiples", human)
        self.assertIn("**Question.** Is the series", human)
        self.assertIn("**Read.** [Programme paper]", human)
        self.assertIn("[Lean source]", human)
        self.assertIn("**Checked frontier.**", human)
        self.assertIn("**Open boundary.**", human)
        self.assertIn("<details>", human)
        self.assertIn("<summary>Representative checked declaration</summary>", human)
        self.assertIn("<summary>Contribution families (5)</summary>", human)
        self.assertIn("<summary>Technical registry and Comparator routing (5)</summary>", human)
        self.assertIn("## Comparator interface appendix", human)
        self.assertIn("<summary>Show all 19 statement-isolated interfaces</summary>", human)
        # Identifiers are emitted verbatim: <wbr> is stripped by GitHub's HTML
        # sanitiser, and zero-width or soft-hyphen breaks survive but corrupt
        # copy-paste of a Lean declaration name.
        self.assertNotIn("<wbr>", human)
        self.assertNotIn("&shy;", human)
        self.assertNotIn("\u00ad", human)
        self.assertNotIn("\u200b", human)
        self.assertNotIn("—", human)
        self.assertIn("Source and priority note", human)
        self.assertIn("Steve Fan", human)
        self.assertIn("**Programmes.**", human)
        self.assertIn("#programme-68", human)
        self.assertIn("- **Factorial carry characterisation**", human)
        self.assertIn("*Evidence.*", human)
        self.assertIn("Exact registry keys and Comparator routing are listed separately.", human)
        # Human-first dossiers: no serial two-pass headings, no snake_case H4s, no table era.
        self.assertNotIn("## Programme disclosure", human)
        self.assertNotIn("## Contribution and evidence matrix", human)
        self.assertNotIn("eight-programme rows", human)
        self.assertNotIn("#### `factorial_carry_characterisation`", human)
        self.assertNotIn("**Contribution.**", human)
        self.assertNotIn("**Class / evidence.**", human)
        self.assertNotIn("cold mathematical reviewer", human)
        self.assertNotIn("cold mathematical reviewer", packet["purpose"])
        self.assertNotIn(
            "| Problem | Representative checked declaration | Checked frontier | Still open |",
            human,
        )
        self.assertNotIn(
            "| Problem | Family | Contribution class | What is contributed | Evidence | Comparator disposition | Boundary |",
            human,
        )
        # Sibling disclosures only: no nested <details>.
        self.assertNotIn("<details>\n<details>", human)
        self.assertNotIn("</details>\n<details>\n<details>", human)
        # Comparator policy appears once at contract level, not inside every family disclosure.
        policy = (
            "Comparator is used only for exact Lean-owned propositions that can be isolated "
            "without importing their proofs"
        )
        self.assertEqual(human.count(policy), 1)
        # Lossless inventory: every family id and disposition once; every interface preserved.
        _, owner, _, _ = load_owner()
        family_rows = [
            family
            for problem in owner["review_matrix"]
            for family in problem["families"]
        ]
        family_ids = [family["id"] for family in family_rows]
        self.assertEqual(len(family_ids), len(set(family_ids)))
        code_spans = re.findall(r"<code>(.*?)</code>", human, flags=re.S)
        for family in family_rows:
            self.assertEqual(code_spans.count(family["id"]), 1, family["id"])
            self.assertIn(family["comparator_disposition"], code_spans)
            self.assertIn(family["boundary"], human)
            self.assertIn(family["summary"], human)
        # Each identifier is a whole code span, so copying it yields a name that
        # still compiles and greps.
        for row in owner["main_results"]:
            self.assertIn(row["wrapper_declaration"], code_spans)
        challenge = (ROOT / "ExternalVerification/Challenge.lean").read_text()
        solution = (ROOT / "ExternalVerification/Solution.lean").read_text()
        self.assertEqual(challenge.count("sorry"), 1)
        self.assertNotIn("sorry", solution)

    def test_multi_module_import_lines_cannot_evade_isolation_parser(self) -> None:
        self.assertEqual(
            imports_in_text(
                "import ExternalVerification.Statements\n"
                "import Erdos249257.TotientMahlerDefect Mathlib\n"
            ),
            [
                "ExternalVerification.Statements",
                "Erdos249257.TotientMahlerDefect",
                "Mathlib",
            ],
        )

    def test_local_proof_provenance_cannot_assert_originality(self) -> None:
        _, packet, source, _ = load_owner()
        adversarial = deepcopy(packet)
        adversarial["main_results"][0]["contribution_class"] = (
            "original theoretical result"
        )
        _, errors = validate(adversarial, source)
        self.assertTrue(any("infers originality" in error for error in errors))

    def test_prior_result_requires_exact_source_mapping(self) -> None:
        _, packet, source, _ = load_owner()
        adversarial = deepcopy(packet)
        adversarial["source_fidelity"].pop("prime_gap_unboundedness")
        _, errors = validate(adversarial, source)
        self.assertIn(
            "prior-result interface prime_gap_unboundedness lacks source fidelity",
            errors,
        )

    def test_unknown_claim_id_cannot_promote_an_interface(self) -> None:
        _, packet, source, _ = load_owner()
        adversarial = deepcopy(packet)
        adversarial["main_results"][0]["claim_id"] = "not_a_registered_claim"
        _, errors = validate(adversarial, source)
        self.assertIn("unknown claim_id: not_a_registered_claim", errors)

    def test_negative_fixture_is_a_real_statement_mismatch(self) -> None:
        positive = json.loads((ROOT / "verification/comparator.json").read_text())
        negative = json.loads(
            (ROOT / "verification/comparator-negative-mismatch.json").read_text()
        )
        self.assertEqual(negative["challenge_module"], positive["challenge_module"])
        self.assertNotEqual(negative["solution_module"], positive["solution_module"])
        text = (ROOT / "ExternalVerification/NegativeSolution.lean").read_text()
        self.assertNotIn("sorry", text)
        self.assertIn("2 ^ e + 2", text)

    def test_1049_programme_packet_is_exactly_scoped(self) -> None:
        positive = json.loads(
            (ROOT / "verification/comparator-1049-numerical-height.json").read_text()
        )
        negative = json.loads(
            (ROOT / "verification/comparator-1049-numerical-height-negative-mismatch.json").read_text()
        )
        metadata = json.loads(
            (ROOT / "verification/comparator-1049-numerical-height.metadata.json").read_text()
        )
        self.assertEqual(positive["challenge_module"], "ExternalVerification1049.Challenge")
        self.assertEqual(positive["solution_module"], "ExternalVerification1049.Solution")
        self.assertEqual(negative["challenge_module"], positive["challenge_module"])
        self.assertNotEqual(negative["solution_module"], positive["solution_module"])
        self.assertFalse(metadata["headline_interface_count_changed"])
        self.assertEqual(metadata["disposition"], "programme_local_comparator_packet")
        statement = (ROOT / "ExternalVerification1049/Statements.lean").read_text()
        challenge = (ROOT / "ExternalVerification1049/Challenge.lean").read_text()
        solution = (ROOT / "ExternalVerification1049/Solution.lean").read_text()
        mismatch = (ROOT / "ExternalVerification1049/NegativeSolution.lean").read_text()
        self.assertEqual(challenge.count("sorry"), 1)
        self.assertNotIn("sorry", solution)
        self.assertNotIn("ErdosProblems", statement)
        self.assertIn("sevenHalves_bundschuhVaananen_margin", solution)
        self.assertIn("≤", mismatch)
        self.assertNotIn("irrational", challenge.lower())

    def test_infrastructure_failure_cannot_masquerade_as_negative_rejection(self) -> None:
        self.assertTrue(is_expected_negative_rejection(1, EXPECTED_MISMATCH))
        self.assertTrue(
            is_expected_negative_rejection(1, EXPECTED_1049_MISMATCH, EXPECTED_1049_MISMATCH)
        )
        self.assertFalse(is_expected_negative_rejection(125, "systemd unavailable"))
        self.assertFalse(is_expected_negative_rejection(127, "landrun: command not found"))

    def test_ci_separates_core_builds_from_external_and_paper_only_changes(self) -> None:
        workflow = (ROOT / ".github/workflows/lean.yml").read_text()
        core_gate = workflow.split("- name: Detect supported-root Lean changes", 1)[1]
        core_gate = core_gate.split("- name: Test pinned proof-environment lock", 1)[0]
        self.assertNotIn("'*.lean'", core_gate)
        self.assertIn("Erdos249257.lean 'Erdos249257/**'", core_gate)
        self.assertIn("ErdosProblems.lean 'ErdosProblems/**'", core_gate)
        self.assertNotIn("ExternalVerification", core_gate)
        self.assertIn("id: external-inputs", workflow)
        self.assertIn("steps.external-inputs.outputs.changed == 'true'", workflow)
        self.assertIn(
            "ref: ${{ github.event.pull_request.head.sha || github.sha }}", workflow
        )
        self.assertIn("--expected-commit", workflow)
        self.assertIn(
            "external-verification-receipt-${{ github.event.pull_request.head.sha || github.sha }}",
            workflow,
        )
        self.assertIn("external-verification-only", workflow)
        self.assertIn("release-surfaces-only", workflow)
        self.assertIn("inputs.scope == 'external-verification-only'", workflow)
        self.assertIn("inputs.scope == 'release-surfaces-only'", workflow)
        self.assertIn("ExternalVerification1049", workflow)
        self.assertIn("comparator-1049-numerical-height.json", workflow)

        prepare = workflow.index("- name: Prepare trusted challenge inputs")
        compare = workflow.index("- name: Run positive and adversarial Comparator checks")
        audit = workflow.index("- name: Print post-verification axiom audit")
        self.assertLess(prepare, compare)
        self.assertLess(compare, audit)
        self.assertNotIn("AxiomAudit", workflow[prepare:compare])


if __name__ == "__main__":
    unittest.main()
