#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Fast regression checks for the distinct-height certificates (a few seconds).

These tests recompute finite exact facts and compare them with the committed
receipts.  They check the programs and the receipts; they do not, and cannot,
check the infinite argument that turns a passing certificate into an
irrationality theorem.  That argument is in the paper.
"""

from __future__ import annotations

import hashlib
import json
import sys
import unittest
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import separation_235 as sep  # noqa: E402
from certificate import (  # noqa: E402
    build_automaton,
    check_actual_paths,
    decode,
    exact_envelopes,
    first_passing_depth,
    outer_envelopes,
)


def load(name: str) -> dict:
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def digest(name: str) -> str:
    return hashlib.sha256((HERE / name).read_bytes()).hexdigest()


class ProofConstants(unittest.TestCase):
    def test_constants_of_the_235_proof(self):
        c = sep.proof_constants()
        self.assertTrue(all(c["checks"].values()), c["checks"])
        self.assertEqual(c["lower_bound"], Fraction(3, 10))
        self.assertEqual(c["upper_bound"], Fraction(13, 15))
        self.assertEqual([tau for tau, _ in c["images_in_increasing_order"]],
                         ["53", "5", "35", "3", ""])
        self.assertEqual(c["gaps"], [Fraction(1, 900), Fraction(17, 300),
                                     Fraction(79, 900), Fraction(1, 180)])

    def test_separation_needs_upper_bound_below_nine_tenths(self):
        # The empty block and the block with one power of 3 separate exactly
        # when the largest tail is less than three times the smallest.
        m = Fraction(3, 10)
        for upper, separated in ((Fraction(13, 15), True), (Fraction(9, 10), False),
                                 (Fraction(1), False)):
            self.assertEqual(sep.G("3", upper) < sep.G("", m), separated, upper)

    def test_first_blocks_from_the_heights(self):
        types, pairs = sep.block_data(12)
        self.assertEqual(types, ["", "3", "5", "3", "53", "", "35", "3", "", "53", "", "35"])
        self.assertEqual(pairs[:7], [(2, 1), (6, 3), (10, 3), (6, 3), (30, 9), (2, 1), (30, 13)])
        self.assertEqual([sep.height(t) for t in (2, 3, 4, 5, 8, 9, 16, 25, 27, 32)],
                         [2, 6, 12, 60, 120, 360, 720, 3600, 10800, 21600])

    def test_receipt_235(self):
        receipt = load("separation_235.json")
        self.assertEqual(receipt["run"]["program_sha256"], digest("separation_235.py"))
        self.assertTrue(all(receipt["proof_constants"]["checks"].values()))
        observed = receipt["finite_observations"]
        self.assertEqual(observed["tails_decoded_by_own_type"], observed["blocks"])
        self.assertTrue(observed["D_lower"].startswith("1.77961698329474905045919"))


class Certificates(unittest.TestCase):
    def test_triple_receipt_is_reproduced_exactly(self):
        receipt = load("triple_sweep.json")
        self.assertEqual(receipt["run"]["program_sha256"], digest("sweep.py"))
        self.assertEqual(receipt["run"]["library_sha256"], digest("certificate.py"))
        self.assertEqual(receipt["summary"]["passing"], 165)
        self.assertEqual(receipt["summary"]["by_first_passing_depth"],
                         {"1": 141, "2": 17, "3": 4, "4": 3})
        for row in receipt["sets"]:
            aut = build_automaton(row["primes"])
            result = first_passing_depth(aut, exact_envelopes(aut), 4)
            self.assertIsNotNone(result, row["primes"])
            gap = result["least_gap"]
            self.assertEqual(result["depth"], row["first_passing_depth"], row["primes"])
            self.assertEqual(f"{gap.numerator}/{gap.denominator}", row["least_gap"], row["primes"])
            self.assertTrue(row["methods_agree"], row["primes"])

    def test_outer_certificate_on_the_deepest_triples(self):
        for primes, depth in (((2, 3, 7), 3), ((2, 17, 31), 4), ((2, 29, 31), 4)):
            aut = build_automaton(primes)
            result = first_passing_depth(aut, outer_envelopes(aut), 4)
            self.assertIsNotNone(result, primes)
            self.assertEqual(result["depth"], depth, primes)

    def test_outer_envelopes_contain_exact_ones(self):
        aut = build_automaton((2, 3, 5))
        outer, exact = outer_envelopes(aut), exact_envelopes(aut)
        for state in aut.states:
            self.assertLessEqual(outer[state][0], exact[state][0])
            self.assertGreaterEqual(outer[state][1], exact[state][1])

    def test_2357_is_undecided_and_the_clash_is_empty_versus_three(self):
        receipt = load("primes_2357.json")
        self.assertEqual(receipt["run"]["program_sha256"], digest("certificate.py"))
        for method in ("outer", "exact"):
            self.assertIsNone(receipt["methods"][method]["first_passing_depth"])
            self.assertEqual(len(receipt["methods"][method]["depths"]), 7)
        aut = build_automaton((2, 3, 5, 7))
        env = exact_envelopes(aut)
        for depth in (1, 2, 3):
            result = decode(aut, env, depth)
            self.assertFalse(result["passed"])
            (first, second), _ = result["overlaps"][0]
            self.assertEqual({first, second}, {(), (3,)})

    def test_four_prime_receipt(self):
        receipt = load("four_prime_sweep.json")
        self.assertEqual(receipt["run"]["program_sha256"], digest("sweep.py"))
        self.assertEqual(receipt["run"]["library_sha256"], digest("certificate.py"))
        summary = receipt["summary"]
        self.assertEqual(summary["sets"], 330)
        self.assertEqual(summary["passing"] + summary["undecided_through_max_depth"], 330)
        self.assertTrue(summary["methods_agree_everywhere"])
        rows = {tuple(row["primes"]): row for row in receipt["sets"]}
        self.assertIsNone(rows[(2, 3, 5, 7)]["first_passing_depth"])
        aut = build_automaton((3, 5, 7, 11))
        self.assertTrue(decode(aut, exact_envelopes(aut), 1)["passed"])
        self.assertEqual(rows[(3, 5, 7, 11)]["first_passing_depth"], 1)

    def test_actual_block_words_are_automaton_paths(self):
        for primes in ((2, 3, 5), (2, 3, 7), (3, 5, 7), (2, 3, 5, 7)):
            aut = build_automaton(primes)
            check = check_actual_paths(aut, exact_envelopes(aut), 300)
            self.assertGreater(check["checked"], 250, primes)
            self.assertEqual(check["violations"], 0, primes)

    def test_a_corrupted_map_is_rejected(self):
        # Negative control: give blocks with one power of 3 the map of an empty
        # block.  Their images then coincide and the test must fail.
        aut = build_automaton((2, 3, 5))
        maps = dict(aut.maps)
        maps[(3,)] = maps[()]
        corrupted = type(aut)(aut.primes, aut.p, aut.others, aut.gaps, aut.states,
                              aut.transitions, maps)
        self.assertFalse(decode(corrupted, outer_envelopes(corrupted), 1)["passed"])

    def test_two_prime_sets_pass(self):
        for primes in ((2, 3), (2, 5), (3, 5), (29, 31)):
            aut = build_automaton(primes)
            self.assertTrue(decode(aut, exact_envelopes(aut), 1)["passed"], primes)


if __name__ == "__main__":
    unittest.main()
