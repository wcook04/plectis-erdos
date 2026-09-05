#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the complete public result-atom query routes."""

from __future__ import annotations

import unittest

import query_corpus
from result_atoms import load_result_atoms


class ResultAtomQueryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.rows = load_result_atoms()

    def test_exact_atom_lookup_returns_family_context(self) -> None:
        atom = self.rows[0]
        packet = query_corpus.result_atom_packet(atom["atom_id"])
        self.assertEqual(packet["kind"], "result_atom")
        self.assertEqual(packet["atom"], atom)
        self.assertEqual(packet["family"]["id"], atom["family_id"])
        self.assertEqual(packet["family"]["problem_id"], atom["problem_id"])
        self.assertIn(
            packet["family_display"]["display_band"]["band"],
            {"front_door", "major_result", "mechanism", "frontier", "technical_support"},
        )
        self.assertEqual(
            packet["family_interface_metadata"]["atom_level_proof"],
            "not_asserted",
        )
        self.assertEqual(
            packet["registered_claim_coverage"]["atom_linkage"],
            "not_asserted",
        )

    def test_unknown_atom_fails_closed(self) -> None:
        with self.assertRaisesRegex(KeyError, "unknown result atom"):
            query_corpus.result_atom_packet("erdos_257:not_a_public_atom")

    def test_family_listing_is_bounded_and_omission_explicit(self) -> None:
        family_id = max(
            {row["family_id"] for row in self.rows},
            key=lambda candidate: sum(
                row["family_id"] == candidate for row in self.rows
            ),
        )
        expected = sorted(
            [row for row in self.rows if row["family_id"] == family_id],
            key=query_corpus.result_atom_sort_key,
        )
        packet = query_corpus.family_result_atoms_packet(family_id, 3)
        self.assertEqual(packet["atom_count"], len(expected))
        self.assertEqual(packet["family_display"]["family_id"], family_id)
        self.assertEqual(len(packet["atoms"]), 3)
        self.assertEqual(
            packet["omission_receipt"]["omitted_atom_count"], len(expected) - 3
        )
        self.assertEqual(
            {row["atom_id"] for row in packet["atoms"]},
            {row["atom_id"] for row in expected[:3]},
        )

    def test_every_family_is_populated_and_visible(self) -> None:
        populated = {row["family_id"] for row in self.rows}
        displayed = set(query_corpus.result_family_display_lookup())
        self.assertEqual(populated, displayed)
        smallest_family = min(
            populated,
            key=lambda family_id: sum(
                row["family_id"] == family_id for row in self.rows
            ),
        )
        packet = query_corpus.family_result_atoms_packet(smallest_family, 3)
        self.assertGreaterEqual(packet["atom_count"], 1)
        self.assertGreaterEqual(len(packet["atoms"]), 1)
        self.assertEqual(packet["omission_receipt"]["omitted_atom_count"], 0)
        self.assertEqual(packet["family_display"]["family_id"], smallest_family)

    def test_family_listing_is_strongest_first_with_stable_tiebreak(self) -> None:
        family_id = next(
            family_id
            for family_id in {row["family_id"] for row in self.rows}
            if len(
                {row["display_tier"] for row in self.rows if row["family_id"] == family_id}
            )
            > 1
        )
        packet = query_corpus.family_result_atoms_packet(family_id, 100)
        emitted = packet["atoms"]
        keys = [query_corpus.result_atom_sort_key(row) for row in emitted]
        self.assertEqual(keys, sorted(keys))
        self.assertEqual(
            query_corpus.result_atom_sort_key(
                {"display_tier": "compact", "source_ordinal": 4, "atom_id": "b"}
            ),
            (1, 4, "b"),
        )
        tied = [
            {"display_tier": "compact", "source_ordinal": 4, "atom_id": "b"},
            {"display_tier": "compact", "source_ordinal": 4, "atom_id": "a"},
        ]
        self.assertEqual(
            [row["atom_id"] for row in sorted(tied, key=query_corpus.result_atom_sort_key)],
            ["a", "b"],
        )

    def test_card_routes_preserve_truthful_state(self) -> None:
        delegated = next(row for row in self.rows if "interpretation" in row)
        packet = query_corpus.result_atom_packet(delegated["atom_id"])
        card = query_corpus.render_card(packet)
        self.assertIn(delegated["atom_id"], card)
        self.assertIn("delegated_agent_editorial_best_attempt", card)
        self.assertIn("family hook |", card)
        self.assertIn("why it matters |", card)
        self.assertIn("boundary |", card)
        self.assertIn("atom-level proof and execution not asserted", card)

    def test_family_card_leads_with_reader_hook_and_boundary(self) -> None:
        family_id = self.rows[0]["family_id"]
        packet = query_corpus.family_result_atoms_packet(family_id, 1)
        card = query_corpus.render_card(packet)
        self.assertIn(
            f"band={packet['family_display']['display_band']['band']}", card
        )
        self.assertIn("reader hook |", card)
        self.assertIn("family boundary |", card)
        self.assertIn("atom-level proof and execution not asserted", card)

    def test_cli_dispatches_both_atom_routes(self) -> None:
        atom = self.rows[0]
        packet, output_format = query_corpus.query_args_packet(
            ["--result-atom", atom["atom_id"]]
        )
        self.assertEqual(output_format, "json")
        self.assertEqual(packet["kind"], "result_atom")
        family_packet, _ = query_corpus.query_args_packet(
            ["--family-atoms", atom["family_id"], "--limit", "1"]
        )
        self.assertEqual(family_packet["kind"], "result_family_atoms")
        self.assertEqual(len(family_packet["atoms"]), 1)


if __name__ == "__main__":
    unittest.main()
