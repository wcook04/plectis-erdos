#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Fast regression checks for the two-tail illustrations (a few seconds).

The tests recompute the fast subset of two_tail.py in exact arithmetic and
compare it with the committed full receipt two_tail.json.  They check the
finite facts the papers quote about the proof that D_P is irrational for every
finite P with |P| >= 2; the proof itself is in the papers and uses none of them.
"""

from __future__ import annotations

import hashlib
import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import two_tail as tt  # noqa: E402


def load(name: str) -> dict:
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def digest(name: str) -> str:
    return hashlib.sha256((HERE / name).read_bytes()).hexdigest()


class Receipt(unittest.TestCase):
    def test_receipt_matches_program(self):
        receipt = load("two_tail.json")
        self.assertEqual(receipt["run"]["mode"], "full")
        self.assertEqual(receipt["run"]["program_sha256"], digest("two_tail.py"))
        self.assertEqual(receipt["run"]["library_sha256"], digest("certificate.py"))

    def test_receipt_statements(self):
        receipt = load("two_tail.json")
        two, three, four = receipt["injectivity"]
        self.assertEqual((two["collisions"], three["collisions"]), (0, 0))
        self.assertEqual((four["sets"], four["collisions"]), (2380, 30))
        self.assertEqual(four["examples"][0], [[5, 7, 3, 2], [7, 2, 3, 5], 51])
        self.assertEqual(receipt["reversal"]["examples"][0], [[43, 13, 3, 53], [53, 3, 13, 43], 2280])
        ident = receipt["identity2357"]
        self.assertTrue(ident["four_block_maps_equal"] and ident["same_end_state_everywhere"])
        self.assertEqual((ident["occurrences_w1"], ident["occurrences_w2"]), (12, 40))
        for row in receipt["chains"]:
            self.assertEqual(row["f_collisions"], 0, row["primes"])
            self.assertLessEqual(max(int(k) for k in row["chain_sizes"]), len(row["primes"]))
        rows = {tuple(r["primes"]): r for r in receipt["chains"]}
        self.assertEqual((rows[(2, 3, 5, 7)]["rearranged_chains"],
                          rows[(2, 3, 5, 7)]["rearranged_transpositions"]), (39, 35))
        pair = receipt["close_pair"]
        self.assertEqual(pair["best_return_found"], 2547450)
        self.assertEqual((pair["rearranged_segments"], pair["f_collisions"]), (9, 0))
        self.assertEqual(pair["log10_difference"], pair["log10_predicted_leading_term"])
        self.assertLessEqual(receipt["euler"]["max_sum_k_minus_3"], 0)


class Recompute(unittest.TestCase):
    def test_identity_and_adjacent_swap(self):
        self.assertEqual(tt.check_identity(300, 500)["identity_checks"], 300)

    def test_f_on_small_orderings(self):
        self.assertEqual(tt.injectivity(60, 2)["collisions"], 0)
        self.assertEqual(tt.injectivity(60, 3)["collisions"], 0)
        four = tt.injectivity(60, 4)
        self.assertEqual(four["collisions"], 30)
        self.assertEqual(tt.f((5, 7, 3, 2)), tt.f((7, 2, 3, 5)))
        self.assertEqual(tt.f((43, 13, 3, 53)), 2280)
        self.assertEqual(tt.f((53, 3, 13, 43)), 2280)
        self.assertEqual(tt.f((2, 3)) - tt.f((3, 2)), 3 - 2)

    def test_identical_block_maps_for_2357(self):
        ident = tt.identity_2357(20000)
        self.assertEqual(ident["two_block_map"], "(103 + y)/420")
        self.assertTrue(ident["four_block_maps_equal"])
        self.assertEqual([r["start"] for r in ident["common_start_states"]], [[1, 2, 2], [1, 2, 3]])
        self.assertTrue(all(r["end_w1"] == [2, 1, 1] for r in ident["common_start_states"]))
        self.assertEqual((ident["occurrences_w1"], ident["occurrences_w2"]), (12, 40))

    def test_chains_at_a_return(self):
        row = tt.chain_simulation((2, 3, 5), 3, 30, 20000, 1500)
        self.assertEqual(row["n"], 9975)
        self.assertEqual(row["rearranged_chains"], row["rearranged_transpositions"])
        self.assertGreater(row["rearranged_chains"], 0)
        self.assertEqual(row["f_collisions"], 0)

    def test_close_pair_leading_term(self):
        pair = tt.close_pair_2357(2547450, 60, 1200)
        self.assertEqual(pair["first_rearranged"], [1005, [5, 2], [2, 5], 3, 6])
        self.assertTrue(pair["difference_exceeds_truncation_error"])
        self.assertEqual(pair["log10_difference"], -501.1234)
        self.assertEqual(pair["log10_predicted_leading_term"], -501.1234)

    def test_torus_arrangements(self):
        self.assertEqual(tt.euler_check(40, 4)["square_with_diagonals"],
                         {"sum_k_minus_3": 0, "two_line_vertices": 1})

    def test_single_prime_subsums(self):
        ident = tt.ep_identities(trials=300, box=8)
        self.assertEqual(set(map(tuple, ident["three_prime_carry_values"].values())), {(0, 1)})
        self.assertEqual(ident["four_prime_carry_values"], [0, 1, 2])
        pair = tt.ep_close_pair((2, 3, 5), 2, 20, 65, 300)
        self.assertEqual(pair["first_rearranged"], [131, [2, 3], [3, 2], 3, 1])
        self.assertTrue(pair["difference_exceeds_truncation_error"])
        self.assertEqual(pair["log10_difference"], -58.098)
        receipt = load("two_tail.json")
        self.assertEqual(receipt["ep_close_pair"], pair)
        self.assertEqual(receipt["ep_identities"]["four_prime_carry_values"], [0, 1, 2])

    def test_negative_control_three_families(self):
        # The two-wall lemma needs four families.  For three families with
        # unimodular pairs the only vertex is the origin, on all three lines.
        self.assertEqual(tt.arrangement([(1, 0), (0, 1), (1, 1)]), (0, 0))
        self.assertNotEqual(tt.f((5, 7, 3, 2)), tt.f((2, 3, 5, 7)))


if __name__ == "__main__":
    unittest.main()
