#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact checks for the base-six finite normal-form reader."""

from __future__ import annotations

from math import gcd

import totient_kernel_normal_form as normal_form


def test_complete_evaluation_certificate() -> None:
    assert len(normal_form.ALL_CHANNELS) == 43
    assert len(normal_form.RETAINED) == 37
    assert len(normal_form.REDUCTIONS) == 6
    assert (2, 2) in normal_form.RETAINED
    assert (2, 3) in normal_form.RETAINED  # coprimality is not the filter
    assert normal_form.determinant_mod_prime(normal_form.evaluation_matrix(), 101) == 17


def test_totient_values_against_coprime_count() -> None:
    arguments = {
        normal_form.BASE**j * n + r
        for n in range(37)
        for j, r in normal_form.RETAINED
    }
    assert len(arguments) == 1147
    for argument in arguments:
        independent = sum(gcd(argument, m) == 1 for m in range(1, argument + 1))
        assert normal_form.totient(argument) == independent


def test_exact_relations_and_witnesses() -> None:
    for omitted, (retained, multiplier) in normal_form.REDUCTIONS.items():
        result = normal_form.normalize({omitted: 1, retained: -multiplier})
        assert result["identity"] is True
        assert result["counterexample"] is None
        assert result["relation_coefficients"][list(normal_form.REDUCTIONS).index(omitted)] == 1
        for n in (0, 1, 7, 36, 73):
            assert normal_form.value(omitted, n) == multiplier * normal_form.value(retained, n)

    # A mod-101 evaluation alone would incorrectly call this an identity.
    false_identity = normal_form.normalize({(1, 1): 101})
    assert false_identity["identity"] is False
    witness = false_identity["counterexample"]
    assert witness is not None
    assert 0 <= witness["n"] <= 36
    assert witness["exact_value"] == 101 * normal_form.value((1, 1), witness["n"])
    assert witness["exact_value"] % 101 == 0


if __name__ == "__main__":
    test_complete_evaluation_certificate()
    test_totient_values_against_coprime_count()
    test_exact_relations_and_witnesses()
    print("base-six totient normal form: exact checks passed")
