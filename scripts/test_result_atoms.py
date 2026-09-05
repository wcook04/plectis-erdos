#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the public result-atom catalog."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path

from result_atoms import (
    CLAIMS_PATH,
    _write_catalog,
    load_family_display_order,
    load_result_atoms,
    merge_candidate_atoms,
    validate_result_atoms,
)


class ResultAtomCatalogTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.rows = load_result_atoms()
        cls.claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
        cls.family_display_order = load_family_display_order()

    def test_exact_public_census(self) -> None:
        summary = validate_result_atoms(self.rows)
        self.assertEqual(summary["total"], 682)
        self.assertEqual(summary["family_count"], 71)
        self.assertEqual(sum(summary["family_counts"].values()), summary["total"])
        self.assertEqual(len(summary["family_counts"]), summary["family_count"])
        self.assertEqual(
            summary["state_counts"],
            {
                "delegated_agent_editorial_best_attempt": 276,
                "existing_source_linked_reviewer_card": 406,
            },
        )
        self.assertEqual(
            summary["band_counts"],
            {
                "front_door": 10,
                "frontier": 17,
                "major_result": 13,
                "mechanism": 19,
                "technical_support": 12,
            },
        )
        self.assertEqual(summary["promotion_count"], 7)
        self.assertEqual(summary["populated_family_count"], summary["family_count"])
        self.assertEqual(summary["zero_family_ids"], [])
        self.assertEqual(
            set(summary["source_digests"]),
            {
                "claims_review_matrix_sha256",
                "family_display_order_sha256",
                "result_atoms_sha256",
            },
        )

    def test_consistent_future_family_and_atom_need_no_python_literal(self) -> None:
        claims = copy.deepcopy(self.claims)
        display_order = copy.deepcopy(self.family_display_order)
        rows = copy.deepcopy(self.rows)
        family_id = "future_consistent_result_family"

        problem_group = next(
            group
            for group in claims["external_verification_packet"]["review_matrix"]
            if group["problem"] == 68
        )
        family = copy.deepcopy(problem_group["families"][0])
        family["id"] = family_id
        problem_group["families"].append(family)

        display = copy.deepcopy(
            next(row for row in display_order if row["problem_id"] == "erdos_68")
        )
        display["family_id"] = family_id
        display["global_display_order"] = len(display_order) + 1
        display["object_key"] = f"review-family:erdos_68:{family_id}"
        display["display_band"]["within_problem_order"] = len(
            [row for row in display_order if row["problem_id"] == "erdos_68"]
        ) + 1
        display_order.append(display)

        atom = copy.deepcopy(
            next(
                row
                for row in rows
                if row["problem_id"] == "erdos_68" and "interpretation" in row
            )
        )
        atom["result_id"] = "future_consistent_result"
        atom["atom_id"] = "erdos_68:future_consistent_result"
        atom["family_id"] = family_id
        atom.pop("source_ordinal")
        atom["statement_excerpt"] = "A future public result with the same truth boundary."

        rows, summary = merge_candidate_atoms(rows, [atom], claims, display_order)
        self.assertEqual(summary["total"], len(self.rows) + 1)
        self.assertEqual(summary["family_count"], len(self.family_display_order) + 1)
        self.assertEqual(summary["family_ids"][-1], family_id)
        self.assertEqual(summary["family_counts"][family_id], 1)
        self.assertEqual(
            next(row for row in rows if row["atom_id"] == atom["atom_id"])[
                "source_ordinal"
            ],
            1
            + max(
                row["source_ordinal"]
                for row in self.rows
                if row["problem_id"] == "erdos_68"
            ),
        )
        self.assertEqual(
            summary["problem_counts"]["erdos_68"],
            sum(row["problem_id"] == "erdos_68" for row in self.rows) + 1,
        )

    def test_candidate_merge_derives_problem_ordinal_without_mutating_input(self) -> None:
        candidate = copy.deepcopy(
            next(
                row
                for row in self.rows
                if row["problem_id"] == "erdos_68" and "interpretation" in row
            )
        )
        candidate["result_id"] = "future_candidate_result"
        candidate["atom_id"] = "erdos_68:future_candidate_result"
        candidate["source_ordinal"] = 999_999
        merged, summary = merge_candidate_atoms(self.rows, [candidate])
        actual = next(row for row in merged if row["atom_id"] == candidate["atom_id"])
        expected = 1 + max(
            row["source_ordinal"]
            for row in self.rows
            if row["problem_id"] == "erdos_68"
        )
        self.assertEqual(actual["source_ordinal"], expected)
        self.assertEqual(candidate["source_ordinal"], 999_999)
        self.assertEqual(summary["total"], len(self.rows) + 1)

    def test_candidate_merge_rejects_existing_atom(self) -> None:
        with self.assertRaisesRegex(ValueError, "duplicate result atom"):
            merge_candidate_atoms(self.rows, [copy.deepcopy(self.rows[0])])

    def test_atomic_catalog_write_preserves_existing_permissions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "result-atoms.jsonl"
            target.touch(mode=0o644)
            _write_catalog([self.rows[0]], target)
            self.assertEqual(target.stat().st_mode & 0o777, 0o644)

    def test_family_display_global_order_is_structural(self) -> None:
        display_order = copy.deepcopy(self.family_display_order)
        display_order[1]["global_display_order"] = 1
        with self.assertRaisesRegex(ValueError, "global order must be contiguous"):
            validate_result_atoms(self.rows, self.claims, display_order)

    def test_claim_and_display_family_counts_must_agree(self) -> None:
        display_order = copy.deepcopy(self.family_display_order)
        display_order.pop()
        with self.assertRaisesRegex(ValueError, "does not exactly match claims"):
            validate_result_atoms(self.rows, self.claims, display_order)

    def test_private_path_is_rejected(self) -> None:
        rows = copy.deepcopy(self.rows)
        rows[0]["statement_excerpt"] = "/Users/example/private/result.json"
        with self.assertRaisesRegex(ValueError, "private-only path"):
            validate_result_atoms(rows)

    def test_duplicate_atom_is_rejected(self) -> None:
        rows = copy.deepcopy(self.rows)
        rows[1]["atom_id"] = rows[0]["atom_id"]
        rows[1]["problem_id"] = rows[0]["problem_id"]
        rows[1]["result_id"] = rows[0]["result_id"]
        with self.assertRaisesRegex(ValueError, "duplicate result atom"):
            validate_result_atoms(rows)

    def test_truth_boundary_is_required(self) -> None:
        rows = copy.deepcopy(self.rows)
        rows[0]["statement_scope"] = "full_statement"
        with self.assertRaisesRegex(ValueError, "truth boundary"):
            validate_result_atoms(rows)

    def test_editorial_authority_is_not_upgraded(self) -> None:
        rows = copy.deepcopy(self.rows)
        delegated = next(row for row in rows if "interpretation" in row)
        delegated["interpretation"]["review_status"] = "peer_reviewed"
        with self.assertRaisesRegex(ValueError, "review status"):
            validate_result_atoms(rows)

    def test_missing_public_family_is_rejected(self) -> None:
        rows = copy.deepcopy(self.rows)
        rows[0]["family_id"] = "private_successor_family"
        with self.assertRaisesRegex(ValueError, "absent from public claims"):
            validate_result_atoms(rows)

    def test_empty_delegated_explanation_is_rejected(self) -> None:
        rows = copy.deepcopy(self.rows)
        delegated = next(row for row in rows if "interpretation" in row)
        delegated["interpretation"]["why_it_matters"] = ""
        with self.assertRaisesRegex(ValueError, "why_it_matters"):
            validate_result_atoms(rows)

    def test_noncontiguous_source_ordinals_are_rejected(self) -> None:
        rows = copy.deepcopy(self.rows)
        rows[0]["source_ordinal"] = 10_000
        with self.assertRaisesRegex(ValueError, "source ordinals are not contiguous"):
            validate_result_atoms(rows)


if __name__ == "__main__":
    unittest.main()
