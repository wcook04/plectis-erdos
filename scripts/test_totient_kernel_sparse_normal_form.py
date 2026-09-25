#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Mathematical regression checks for the sparse all-base reader command."""

from __future__ import annotations

import totient_kernel_normal_form as finite_six
import totient_kernel_sparse_normal_form as sparse


def test_composite_base_and_large_sparse_level() -> None:
    assert sparse.prime_divisors(12) == (2, 3)
    assert sparse.reduce_channel(12, (8, 29_859_840), (2, 3)) == ((2, 10), 1_990_656)
    result = sparse.normalize(12, {(8, 29_859_840): 1, (2, 10): -1_990_656})
    assert result["identity"] is True
    assert result["canonical_coefficients"] == []
    assert result["relation_coefficients"] == [
        {"level": 8, "residue": 29_859_840, "coefficient": 1}
    ]
    for n in (0, 1, 2, 17):
        assert sparse.totient(12**8 * n + 29_859_840) == (
            1_990_656 * sparse.totient(12**2 * n + 10)
        )


def test_zero_residues_repetition_and_nonunit_retained() -> None:
    assert sparse.reduce_channel(12, (4, 0), (2, 3)) == ((1, 0), 12**3)
    assert sparse.reduce_channel(6, (2, 2), (2, 3)) == ((2, 2), 1)
    result = sparse.normalize(12, {(4, 0): 1, (1, 0): -(12**3), (2, 2): 0})
    assert result["identity"] is True
    assert result["relation_coefficients"] == [
        {"level": 4, "residue": 0, "coefficient": 1}
    ]
    assert sparse.normalize(6, {(1, 1): 0})["identity"] is True


def test_decision_is_independent_of_witness_budget_or_prime_modulus() -> None:
    false = sparse.normalize(6, {(1, 1): 101}, witness_budget=1)
    assert false["identity"] is False
    assert false["counterexample"] == {"n": 0, "exact_value": 101}
    assert false["counterexample"]["exact_value"] % 101 == 0
    delayed = sparse.normalize(6, {(0, 0): 1}, witness_budget=1)
    assert delayed["identity"] is False
    assert delayed["counterexample"] is None
    assert delayed["witness_status"] == "not_found_within_budget"
    assert sparse.normalize(6, {(0, 0): 1}, witness_budget=2)["counterexample"] == {
        "n": 1, "exact_value": 1
    }


def test_base_six_matches_existing_certificate_on_sparse_inputs() -> None:
    for terms in (
        {(2, 6): 1, (1, 1): -2},
        {(2, 12): 5, (1, 2): -20},
        {(2, 2): 3, (1, 1): 101},
    ):
        old = finite_six.normalize(terms)
        new = sparse.normalize(6, terms)
        assert new["identity"] == old["identity"]
        actual = {
            (row["level"], row["residue"]): row["coefficient"]
            for row in new["canonical_coefficients"]
        }
        expected = {
            channel: coefficient
            for channel, coefficient in zip(finite_six.RETAINED, old["canonical_coefficients"])
            if coefficient
        }
        assert actual == expected


if __name__ == "__main__":
    test_composite_base_and_large_sparse_level()
    test_zero_residues_repetition_and_nonunit_retained()
    test_decision_is_independent_of_witness_budget_or_prime_modulus()
    test_base_six_matches_existing_certificate_on_sparse_inputs()
    print("all-base sparse totient normal form: exact checks passed")
