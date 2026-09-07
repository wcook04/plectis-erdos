#!/usr/bin/env python3
"""Exact low-index checker for the Erdős #1049 adjacent exterior product.

This reproduces the finite Fraction arithmetic in the 2026-07-23 research
return.  It is evidence for the displayed low-index valuations, not a proof of
their all-n formulas or of the analytic asymptotics.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
import json
import math

import sympy as sp


X = sp.symbols("x")
P = Fraction(3, 2)


@lru_cache(None)
def qbinom(n: int, k: int) -> Fraction:
    if k < 0 or k > n:
        return Fraction(0)
    k = min(k, n - k)
    value = Fraction(1)
    for i in range(1, k + 1):
        value *= (P ** (n - k + i) - 1) / (P**i - 1)
    return value


@lru_cache(None)
def cyclotomic_value(ell: int) -> Fraction:
    polynomial = sp.Poly(sp.cyclotomic_poly(ell, X), X, domain=sp.ZZ)
    value = Fraction(0)
    for coefficient in polynomial.all_coeffs():
        value = value * P + int(coefficient)
    return value


def nu(n: int, ell: int) -> int:
    return max(
        0,
        (14 * n) // ell
        + (13 * n) // ell
        - (12 * n) // ell
        - (15 * n) // ell,
        2 * ((14 * n) // ell) - (13 * n) // ell - (15 * n) // ell,
    )


def parameters(n: int) -> tuple[int, int, int]:
    m = 266 * n * n + 34 * n + 1
    k = (1091 * n * n + 81 * n + 2) // 2
    degree_d = sum(int(sp.totient(ell)) for ell in range(1, 15 * n + 1))
    degree_omega = sum(
        nu(n, ell) * int(sp.totient(ell)) for ell in range(2, 15 * n + 1)
    )
    w = k - m + degree_d - degree_omega
    return m, k, w


def forms(n: int) -> tuple[int, int, int, int]:
    a0 = 14 * n + 1
    a1 = 12 * n + 1
    a2 = 14 * n + 1
    b = 27 * n + 2
    m, k, w = parameters(n)

    a = Fraction(0)
    b1 = Fraction(0)
    b2 = Fraction(0)

    for index in range(a2, b):
        exponent = (
            a1 * (a1 - 1)
            - (b - a2) * (b - a2 - 1)
            + (b - index) * (b - index - 1)
        ) // 2
        coefficient = (
            (-1) ** (a1 + a2 + index + 1)
            * P**exponent
            * qbinom(index - 1, a1 - 1)
            * qbinom(b - a2 - 1, b - index - 1)
        )
        base = coefficient * P ** (a0 * index)
        a += base
        b1 += base * sum(
            (
                Fraction(1) / (P**ell - 1)
                for ell in range(1, index - a1 + 1)
            ),
            Fraction(0),
        )
        b2 += sum(
            (
                coefficient
                * P ** (a0 * index - j * (index - a1))
                / (P**j - 1)
                for j in range(1, a0)
            ),
            Fraction(0),
        )

    d = Fraction(1)
    omega = Fraction(1)
    for ell in range(1, 15 * n + 1):
        value = cyclotomic_value(ell)
        d *= value
        if ell >= 2:
            omega *= value ** nu(n, ell)

    factor = P ** (-m) * d / omega
    u = 2**w * factor * a
    v = 2**w * factor * (b1 + b2)
    assert u.denominator == 1
    assert v.denominator == 1
    return int(u), int(v), k, w


def valuation(value: int, prime: int) -> int | float:
    if value == 0:
        return math.inf
    value = abs(value)
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def main() -> None:
    form_rows: dict[int, tuple[int, int]] = {}
    forms_receipt = []
    for n in range(1, 5):
        u, v, k, w = forms(n)
        form_rows[n] = (u, v)
        row = {
            "n": n,
            "W": w,
            "K": k,
            "v2_U": valuation(u, 2),
            "v2_V": valuation(v, 2),
            "v3_U": valuation(u, 3),
            "v3_V": valuation(v, 3),
            "sign_U": 1 if u > 0 else -1,
        }
        assert row["v2_U"] == 0
        assert row["v2_V"] == 1
        assert row["v3_U"] == 2 * n * n
        assert row["v3_V"] == 0
        forms_receipt.append(row)

    exterior_receipt = []
    for n in range(1, 5):
        for m in range(n + 1, 5):
            u, v = form_rows[n]
            um, vm = form_rows[m]
            delta = u * vm - um * v
            row = {
                "n": n,
                "m": m,
                "v2_delta": valuation(delta, 2),
                "v3_delta": valuation(delta, 3),
                "sign_delta": 1 if delta > 0 else -1,
            }
            assert delta != 0
            assert row["v2_delta"] == forms_receipt[n - 1]["K"]
            assert row["v3_delta"] == 2 * n * n
            exterior_receipt.append(row)

    print(
        json.dumps(
            {
                "schema": "erdos1049-adjacent-exterior-check/1",
                "authority": "exact_low_index_computation_not_all_n_proof",
                "forms": forms_receipt,
                "exteriors": exterior_receipt,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
