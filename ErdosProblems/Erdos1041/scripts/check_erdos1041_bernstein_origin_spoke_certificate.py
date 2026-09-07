#!/usr/bin/env python3
"""Exact replay for the Bernstein root-spoke theorem and rational no-go."""

from __future__ import annotations

from math import comb

import sympy as sp


def conversion_replay() -> None:
    t = sp.symbols("t")
    for n in range(2, 10):
        q = sp.symbols(f"q0:{n + 1}")
        controls = [
            sum(q[k] * sp.Rational(comb(j, k), comb(n, k)) for k in range(j + 1))
            for j in range(n + 1)
        ]
        bernstein = sum(
            controls[j] * comb(n, j) * t**j * (1 - t) ** (n - j)
            for j in range(n + 1)
        )
        power = sum(q[k] * t**k for k in range(n + 1))
        assert sp.expand(bernstein - power) == 0


def polarization_replay() -> None:
    z = sp.symbols("z")
    for n in range(2, 8):
        roots = [sp.Rational(j + 1, n + 2) * (-1 if j % 2 else 1) for j in range(n)]
        poly = sp.Poly(sp.prod(z - a for a in roots), z)
        coeff = list(reversed(poly.all_coeffs()))
        for i, a in enumerate(roots):
            q = [coeff[k] * a**k for k in range(n + 1)]
            for j in range(n + 1):
                power_control = sum(
                    q[k] * sp.Rational(comb(j, k), comb(n, k)) for k in range(j + 1)
                )
                subset_total = 0
                for mask in range(1 << n):
                    if mask.bit_count() != j:
                        continue
                    term = sp.Integer(1)
                    for ell in range(n):
                        term *= (a - roots[ell]) if (mask >> ell) & 1 else -roots[ell]
                    subset_total += term
                polarized = subset_total / comb(n, j)
                assert sp.simplify(power_control - polarized) == 0
            penultimate = sum(
                q[k] * sp.Rational(comb(n - 1, k), comb(n, k)) for k in range(n)
            )
            assert sp.simplify(penultimate + a * poly.diff().eval(a) / n) == 0


def first_column_product_replay() -> None:
    """Exact torus identity and centroid-variance product inequality."""

    directions = [
        sp.Integer(1),
        -sp.Integer(1),
        (3 + 4 * sp.I) / 5,
        (3 - 4 * sp.I) / 5,
        (5 + 12 * sp.I) / 13,
        (5 - 12 * sp.I) / 13,
        (8 + 15 * sp.I) / 17,
        (8 - 15 * sp.I) / 17,
    ]
    z = sp.symbols("z")
    for n in range(2, 9):
        roots = directions[:n]
        assert all(sp.factor(sp.re(a * sp.conjugate(a))) == 1 for a in roots)
        poly = sp.Poly(sp.prod(z - a for a in roots), z)
        coeff = list(reversed(poly.all_coeffs()))
        mean = sp.factor(sum(roots) / n)
        controls = [sp.factor(coeff[0] + coeff[1] * a / n) for a in roots]
        d1_values = [sp.factor(a - mean) for a in roots]
        for a, b, d1 in zip(roots, controls, d1_values, strict=True):
            torus_form = sp.factor(coeff[0] * a * sp.conjugate(d1))
            assert sp.simplify(b - torus_form) == 0

        variance = sp.factor(
            sum(sp.re(d * sp.conjugate(d)) for d in d1_values) / n
        )
        assert sp.factor(variance - (1 - sp.re(mean * sp.conjugate(mean)))) == 0
        product_sq = sp.factor(
            sp.prod(sp.re(b * sp.conjugate(b)) for b in controls)
        )
        assert sp.sign(1 - product_sq) >= 0


def exact_rational_no_go() -> None:
    raw = [
        ("0.9954764088478315", "-0.08383149424545093"),
        ("0.14881265879891825", "0.9878541352756472"),
        ("-0.6277869770917356", "0.7771000652387186"),
        ("-0.5684933442778939", "-0.8214720430493883"),
        ("0.26099542375571383", "-0.964304095593592"),
    ]
    roots = [sp.Rational(x) + sp.I * sp.Rational(y) for x, y in raw]
    for a in roots:
        assert sp.sign(1 - sp.re(a * sp.conjugate(a))) == 1

    z = sp.symbols("z")
    poly = sp.Poly(sp.prod(z - a for a in roots), z)
    coeff = list(reversed(poly.all_coeffs()))
    max_indices = [3, 1, 2, 2, 0]
    passing = []
    for i, a in enumerate(roots):
        q = [coeff[k] * a**k for k in range(6)]
        controls = [
            sp.factor(sum(q[k] * sp.Rational(comb(j, k), comb(5, k)) for k in range(j + 1)))
            for j in range(6)
        ]
        gaps = [sp.factor(sp.re(b * sp.conjugate(b)) - 1) for b in controls]
        if i < 4:
            assert sp.sign(gaps[max_indices[i]]) == 1
            passing.append(False)
        else:
            assert all(sp.sign(g) == -1 for g in gaps)
            passing.append(True)
    assert passing == [False, False, False, False, True]

    # Exact penultimate product identity for the witness.
    b4 = [-roots[i] * poly.diff().eval(roots[i]) / 5 for i in range(5)]
    lhs2 = sp.factor(sp.prod(sp.re(x * sp.conjugate(x)) for x in b4))
    cabs2 = sp.factor(sp.re(coeff[0] * sp.conjugate(coeff[0])))
    disc2 = sp.factor(sp.re(poly.discriminant() * sp.conjugate(poly.discriminant())))
    assert sp.simplify(lhs2 - cabs2 * disc2 / 5**10) == 0


def main() -> None:
    conversion_replay()
    polarization_replay()
    first_column_product_replay()
    exact_rational_no_go()
    print("Bernstein origin-spoke certificate: PASS")
    print("exact: convex controls, root polarization, first/penultimate column products")
    print("exact no-go: rational quintic has exactly one certified root")


if __name__ == "__main__":
    main()
