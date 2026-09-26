#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial checks for the source-bound interestingness profile."""

from __future__ import annotations

import unittest
from pathlib import Path

from run import _closure_bitsets, closure_cost, code_mask, declaration_spans, spearman


class ProfileTests(unittest.TestCase):
    def test_lean_mask_respects_nested_comments_strings_and_axiom_prints(self) -> None:
        source = "\n".join(
            [
                "-- theorem ghost : False := by contradiction",
                "/- outer",
                "   /- theorem nested : False := by contradiction -/",
                "   still commented -/",
                'def literal : String := "-- /- theorem ghost -/"',
                "private theorem helper : True := by",
                "  trivial -- theorem inline : False := by contradiction",
                "#print axioms helper",
                "theorem publicClaim : True := by",
                "  exact helper",
            ]
        )
        self.assertEqual(
            code_mask(source),
            [False, False, False, False, True, True, True, False, True, True],
        )

    def test_span_separates_private_helper_and_does_not_charge_audit_command(self) -> None:
        source = "\n".join(
            [
                "private theorem helper : True := by",
                "  trivial",
                "",
                "theorem publicClaim : True := by",
                "  exact helper",
                "",
                "#print axioms publicClaim",
            ]
        )
        declarations = [
            {
                "id": "Tiny.lean:1:helper",
                "name": "helper",
                "kind": "theorem",
                "module": "Tiny.lean",
                "line": 1,
                "signature": "private theorem helper : True",
            },
            {
                "id": "Tiny.lean:4:publicClaim",
                "name": "publicClaim",
                "kind": "theorem",
                "module": "Tiny.lean",
                "line": 4,
                "signature": "theorem publicClaim : True",
            },
        ]
        spans = declaration_spans(Path("Tiny.lean"), declarations, source)
        private = spans["Tiny.lean:1:helper"]
        public = spans["Tiny.lean:4:publicClaim"]
        self.assertTrue(private["private"])
        self.assertFalse(public["private"])
        self.assertLess(private["end_line"], public["start_line"])
        self.assertEqual(private["proof_lines"], 2)
        self.assertEqual(public["proof_lines"], 2)

    def test_diamond_expansion_counts_shared_ancestor_once(self) -> None:
        # A cites B and C, both cite D. The cost is a set union, not a sum of
        # paths; D must be charged once. A context with B available removes
        # B and its proof ancestry without removing the independent C route.
        edges = {0: {1, 2}, 1: {3}, 2: {3}, 3: set()}
        lines = {0: 1, 1: 2, 2: 3, 3: 5}
        self.assertEqual(closure_cost(0, edges, lines), 11)
        self.assertEqual(closure_cost(0, edges, lines, available={1}), 9)
        self.assertEqual(closure_cost(0, edges, lines, available={1, 2}), 1)

    def test_cycle_terminates_and_charges_each_node_once(self) -> None:
        edges = {0: {1}, 1: {0}}
        self.assertEqual(closure_cost(0, edges, {0: 2, 1: 3}), 5)

    def test_profile_reachability_matches_independent_small_graph_oracle(self) -> None:
        # The full profile uses SCC-compressed bitsets, while the transfer
        # helper uses a direct traversal. They must agree for diamonds,
        # cycles, disconnected nodes and a source with no dependencies.
        adjacency = [[1, 2], [3], [3], [4], [3], []]
        lines = [1, 2, 3, 5, 7, 11]
        bitsets = _closure_bitsets(adjacency)
        for node in range(len(adjacency)):
            observed = sum(lines[i] for i in range(len(adjacency)) if bitsets[node] >> i & 1)
            expected = closure_cost(node, adjacency, lines)
            self.assertEqual(observed, expected, msg=f"source node {node}")

    def test_rank_correlation_uses_mid_ranks_for_ties(self) -> None:
        self.assertEqual(spearman([0, 1, 1, 3], [3, 1, 1, 0]), -1.0)
        self.assertEqual(spearman([1, 2, 2, 4], [1, 2, 2, 4]), 1.0)
        self.assertIsNone(spearman([1, 1, 1], [1, 2, 3]))

    def test_shared_proof_cost_alone_can_make_perfect_interest_utility_rho(self) -> None:
        # Every theorem has the same one direct user. No variation in reuse
        # exists, yet I=V/L and U=degree*V rank identically when L is fixed.
        proof_costs = [2, 5, 11, 23]
        description_chars = [10] * len(proof_costs)
        direct_users = [1] * len(proof_costs)
        interest = [100 * v / length for v, length in zip(proof_costs, description_chars)]
        utility = [v * degree for v, degree in zip(proof_costs, direct_users)]
        self.assertEqual(spearman(interest, utility), 1.0)
        self.assertIsNone(spearman(interest, direct_users))


if __name__ == "__main__":
    unittest.main()
