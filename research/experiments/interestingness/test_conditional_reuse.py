#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Falsifiers for context cuts, overlap and complementary premises."""

import unittest
from itertools import combinations

from conditional_reuse import marginal, pair_interaction, reachable, workload_cost


class ConditionalReuseTests(unittest.TestCase):
    def setUp(self):
        # t -> a,b; a,b -> shared. Cutting only a must retain shared via b.
        self.adjacency = [[1, 2], [3], [3], []]
        self.costs = [1, 2, 3, 100]

    def test_diamond_counts_shared_once(self):
        self.assertEqual(workload_cost([0], self.adjacency, self.costs), 106)
        self.assertEqual(marginal([0], 1, self.adjacency, self.costs), 2)
        self.assertEqual(reachable([0], self.adjacency, {1}), {0, 2, 3})

    def test_complementary_cuts_disprove_diminishing_returns(self):
        self.assertEqual(marginal([0], 2, self.adjacency, self.costs), 3)
        self.assertEqual(marginal([0], 2, self.adjacency, self.costs, {1}), 103)
        self.assertEqual(pair_interaction([0], 1, 2, self.adjacency, self.costs), 100)
        self.assertEqual(workload_cost([0], self.adjacency, self.costs, {1, 2}), 1)

    def test_independent_targets_are_a_different_workload(self):
        self.assertEqual(workload_cost([1, 2], self.adjacency, self.costs), 105)
        self.assertEqual(workload_cost([1, 2], self.adjacency, self.costs,
                                       mode="independent"), 205)
        self.assertEqual(marginal([1, 2], 3, self.adjacency, self.costs), 100)
        self.assertEqual(marginal([1, 2], 3, self.adjacency, self.costs,
                                  mode="independent"), 200)

    def test_nested_candidates_have_overlap(self):
        adjacency, costs = [[1], [2], []], [1, 2, 3]
        self.assertEqual(pair_interaction([0], 1, 2, adjacency, costs), -3)
        self.assertEqual(marginal([0], 2, adjacency, costs, {1}), 0)

    def test_cycle_and_already_available(self):
        adjacency, costs = [[1], [2], [1]], [1, 2, 3]
        self.assertEqual(workload_cost([0], adjacency, costs), 6)
        self.assertEqual(workload_cost([0], adjacency, costs, {2}), 3)
        self.assertEqual(marginal([0], 2, adjacency, costs, {2}), 0)

    def test_unrelated_candidate_and_empty_workload(self):
        self.assertEqual(marginal([1], 2, self.adjacency, self.costs), 0)
        self.assertEqual(workload_cost([], self.adjacency, self.costs), 0)
        with self.assertRaises(ValueError):
            workload_cost([0], self.adjacency, self.costs, mode="unknown")

    def test_nonnegative_cost_cuts_are_monotone_in_every_diamond_context(self):
        for size in range(5):
            for context in combinations(range(4), size):
                for candidate in range(4):
                    self.assertGreaterEqual(
                        marginal([0], candidate, self.adjacency, self.costs, context), 0)


if __name__ == "__main__":
    unittest.main()
