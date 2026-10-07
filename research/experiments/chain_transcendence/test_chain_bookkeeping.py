#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Fast checks of the exact bookkeeping behind the divisibility-chain theorem."""
import math
import unittest
from fractions import Fraction

from chain_bookkeeping import (
    analyse_row,
    chain_from_ratios,
    cleared_partial_sum,
    divisor_count_form,
    millin_boundary,
    minimal_k,
    ratio_word,
    run_default,
    subspace_vector,
    tail_coefficients,
    tail_remainder,
    tail_upper_bound,
    term,
    truncation_index,
)

BASES = ((4, 3), (5, 4), (3, 2), (9, 7), (2, 1))
EXACT_KEYS = (
    "coefficient_bound_holds",
    "P_j_integer_matches_divisor_form",
    "identity_exact",
    "tail_positive_and_bounded",
    "s_unit_coordinates",
    "exponent_condition",
    "monomials_distinct_below_Kr",
)


class ChainBookkeepingTests(unittest.TestCase):
    def test_cleared_partial_sums_are_integers(self):
        # P_j = (a^N - b^N) S_j must be an integer on every chain, and it must
        # agree with the divisor-count expansion used in the paper.
        for a, b in BASES:
            for word in ("squares", "fibonacci", "thue_morse"):
                ns = chain_from_ratios(1, ratio_word(word, 12))
                for j in range(1, 6):
                    p_j = cleared_partial_sum(a, b, ns, j)
                    self.assertGreater(p_j, 0)
                    self.assertEqual(p_j, divisor_count_form(a, b, ns, j))

    def test_non_chain_prefix_is_not_cleared(self):
        # Without divisibility the denominator a^N - b^N does not clear the sum:
        # 1/((4/3)^2 - 1) + 1/((4/3)^3 - 1) has a denominator not dividing 4^3 - 3^3.
        value = (4 ** 3 - 3 ** 3) * (term(4, 3, 2) + term(4, 3, 3))
        self.assertNotEqual(value.denominator, 1)

    def test_every_row_satisfies_the_exact_formulas(self):
        for a, b in BASES:
            for word in ("squares", "fibonacci", "doubling"):
                ns = chain_from_ratios(1, ratio_word(word, 20))
                for j in range(1, 6):
                    r = ns[j] // ns[j - 1]
                    row = analyse_row(a, b, ns, j, minimal_k(a, b, r))
                    for key in EXACT_KEYS:
                        self.assertTrue(row[key], (a, b, word, j, key))

    def test_minimal_exponent_choice(self):
        # K is least with K r log(a/b) > log a.
        self.assertEqual(minimal_k(4, 3, 2), 3)
        self.assertEqual(minimal_k(4, 3, 3), 2)
        self.assertEqual(minimal_k(3, 2, 2), 2)
        self.assertEqual(minimal_k(3, 2, 3), 1)
        self.assertEqual(minimal_k(5, 4, 2), 4)
        self.assertEqual(minimal_k(9, 7, 2), 5)
        self.assertEqual(minimal_k(2, 1, 2), 1)
        for a, b in BASES:
            for r in (2, 3, 5):
                k = minimal_k(a, b, r)
                self.assertGreater(k * r * math.log(a / b), math.log(a))
                self.assertLessEqual((k - 1) * r * math.log(a / b), math.log(a))

    def test_only_the_third_coordinate_leaves_the_s_units(self):
        ns = chain_from_ratios(1, ratio_word("squares", 12))
        coords = subspace_vector(4, 3, ns, 4, 2)
        self.assertEqual(len(coords), 5)
        for i, value in enumerate(coords):
            reduced = value
            for p in (2, 3):
                while reduced % p == 0:
                    reduced //= p
            if i == 2:
                self.assertGreater(reduced, 1)
            else:
                self.assertEqual(reduced, 1)

    def test_observed_exponent_tracks_prediction_at_four_thirds(self):
        # The S-adic product is a negative power of the height with the exponent
        # predicted in the paper; this is the inequality the Subspace Theorem needs.
        ns = chain_from_ratios(1, ratio_word("squares", 20))
        for j in range(5, 8):
            r = ns[j] // ns[j - 1]
            row = analyse_row(4, 3, ns, j, minimal_k(4, 3, r))
            self.assertLess(row["log_product_over_log_height"], 0)
            self.assertLess(row["predicted_limit"], 0)
            self.assertLess(abs(row["log_product_over_log_height"] - row["predicted_limit"]), 0.01)

    def test_one_term_liouville_estimate_fails_where_the_theorem_is_new(self):
        # At 4/3 with ratio 2 the cleared tail D_j T_j grows (positive exponent),
        # so the Liouville argument of the a^2 > b^3 theorem cannot apply there.
        ns = chain_from_ratios(1, ratio_word("doubling", 20))
        row = analyse_row(4, 3, ns, 6, 3)
        self.assertGreater(row["liouville_exponent_per_N"], 0.8)
        # At 3/2 with ratio 3 (a^2 > b^3) the same quantity decays.
        ns = chain_from_ratios(1, [3] * 12)
        row = analyse_row(3, 2, ns, 4, 1)
        self.assertLess(row["liouville_exponent_per_N"], 0)

    def test_wrong_coefficients_leave_a_large_tail(self):
        # E_j is of order rho^(KM) only with the true counts c_k; changing one
        # count leaves a term of order rho^(kM), k < K, or makes E_j negative.
        ns = chain_from_ratios(1, ratio_word("squares", 20))
        j, k = 5, 3
        big = truncation_index(ns, j, k)
        true = tail_coefficients(ns, j, k, big)
        bound = tail_upper_bound(4, 3, ns[j], k)
        self.assertTrue(0 < tail_remainder(4, 3, ns, j, big, true) <= bound)
        for index in range(len(true)):
            for delta in (-1, 1):
                wrong = list(true)
                wrong[index] += delta
                value = tail_remainder(4, 3, ns, j, big, wrong)
                self.assertFalse(0 < value <= bound, (index, delta))

    def test_exponent_below_threshold_gives_no_inequality(self):
        # At 4/3 with ratio 2, K = 2 fails K r log(a/b) > log a, and the
        # S-adic product is then a positive power of the height.
        ns = chain_from_ratios(1, [2] * 20)
        row = analyse_row(4, 3, ns, 7, 2)
        self.assertFalse(row["exponent_condition"])
        self.assertGreater(row["log_product_over_log_height"], 0)

    def test_tail_coefficients_are_bounded(self):
        ns = chain_from_ratios(1, [2] * 30)
        row = analyse_row(4, 3, ns, 3, 6)
        # doubling chain: c_k counts the powers of two dividing k, plus one
        self.assertEqual(row["coefficients"], [1, 2, 1, 3, 1])
        self.assertTrue(row["coefficient_bound_holds"])

    def test_rational_boundary_identity(self):
        # sum_j z^(2^j)/(1 - z^(2^(j+1))) = z/(1-z) is rational.  The first tail
        # exponent equals the denominator exponent (ratio 1), two coordinates
        # coincide, and the distinct-monomial step is unavailable.
        boundary = millin_boundary(4, 3, 7)
        self.assertTrue(boundary["telescoping_identity_exact"])
        self.assertTrue(boundary["second_and_fourth_coordinates_coincide"])
        self.assertEqual(Fraction(boundary["value"]), Fraction(3))
        r, k = 1, 3
        exponents = [0, 1] + [i * r for i in range(1, k)] + [1 + i * r for i in range(1, k)]
        self.assertLess(len(set(exponents)), len(exponents))
        with self.assertRaises(ValueError):
            chain_from_ratios(1, [2, 1, 2])

    def test_default_run_passes(self):
        self.assertTrue(run_default()["all_exact_checks_pass"])


if __name__ == "__main__":
    unittest.main()
