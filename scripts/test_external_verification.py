#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial contract checks for the external-verification packet."""

from __future__ import annotations

import json
import subprocess
import unittest
from pathlib import Path

from build_external_verification import imports_in_text
from run_external_verification import EXPECTED_MISMATCH, is_expected_negative_rejection

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

    def test_infrastructure_failure_cannot_masquerade_as_negative_rejection(self) -> None:
        self.assertTrue(is_expected_negative_rejection(1, EXPECTED_MISMATCH))
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

        prepare = workflow.index("- name: Prepare trusted challenge inputs")
        compare = workflow.index("- name: Run positive and adversarial Comparator checks")
        audit = workflow.index("- name: Print post-verification axiom audit")
        self.assertLess(prepare, compare)
        self.assertLess(compare, audit)
        self.assertNotIn("AxiomAudit", workflow[prepare:compare])


if __name__ == "__main__":
    unittest.main()
