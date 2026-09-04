#!/usr/bin/env python3
"""Exact Newton-sum checks for low-mode critical-value moment rigidity."""

from __future__ import annotations

import sympy as sp


def report(name: str, ok: bool, detail: str = "") -> None:
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""))
    if not ok:
        raise AssertionError(name)


def newton_sums(poly: sp.Poly, limit: int) -> dict[int, sp.Expr]:
    """Power sums of the roots of a monic polynomial, with multiplicity."""
    coeffs = poly.monic().all_coeffs()
    degree = poly.degree()
    sums: dict[int, sp.Expr] = {0: sp.Integer(degree)}
    for m in range(1, limit + 1):
        if m <= degree:
            value = sum(coeffs[j] * sums[m - j] for j in range(1, m))
            value += m * coeffs[m]
        else:
            value = sum(coeffs[j] * sums[m - j] for j in range(1, degree + 1))
        sums[m] = sp.expand(-value)
    return sums


def trace_moment(n: int, kmax: int, moment: int) -> sp.Expr:
    z = sp.Symbol(f"z_{n}_{kmax}_{moment}")
    coeffs = [sp.Symbol(f"b_{n}_{kmax}_{k}") for k in range(1, kmax + 1)]
    H = z**n + sum(coeffs[k - 1] * z**k for k in range(1, kmax + 1))
    critical_poly = sp.Poly(sp.diff(H, z) / n, z)
    reduced_value = sp.rem(H, sp.diff(H, z), domain=sp.QQ.frac_field(*coeffs))
    value_power = sp.Poly(sp.expand(reduced_value**moment), z)
    sums = newton_sums(critical_poly, value_power.degree())
    return sp.factor(
        sum(value_power.coeff_monomial(z**m) * sums[m] for m in range(1, value_power.degree() + 1))
    )


def main() -> int:
    checked: list[tuple[int, int, int]] = []
    for n in range(2, 21):
        for kmax in range(1, n):
            for moment in range(1, 5):
                if (moment + 1) * kmax <= n - 1:
                    checked.append((n, kmax, moment))
                    if trace_moment(n, kmax, moment) != 0:
                        report("CM1 moment-vanishing grid", False, str((n, kmax, moment)))
    report(
        "CM1 moment-vanishing grid n<=20, r<=4",
        bool(checked),
        f"exact triples={len(checked)}",
    )

    square_cases = [(n, kmax) for n in range(4, 21) for kmax in range(1, n) if 3 * kmax <= n - 1]
    report(
        "CM2 square-trace terminal range",
        all(trace_moment(n, kmax, 2) == 0 for n, kmax in square_cases),
        f"exact cases={len(square_cases)}",
    )

    z, b1, b2 = sp.symbols("z b1 b2")
    H5 = z**5 + b2 * z**2 + b1 * z
    critical5 = sp.Poly(sp.diff(H5, z) / 5, z)
    value5 = sp.rem(H5, sp.diff(H5, z), domain=sp.QQ.frac_field(b1, b2))
    value5_sq = sp.Poly(sp.expand(value5**2), z)
    sums5 = newton_sums(critical5, value5_sq.degree())
    trace5 = sp.factor(
        sum(value5_sq.coeff_monomial(z**m) * sums5[m] for m in range(1, value5_sq.degree() + 1))
    )
    expected5 = -sp.Rational(36, 25) * b1 * b2**2
    report(
        "CM3 sharp quintic square-trace obstruction",
        sp.expand(trace5 - expected5) == 0,
        f"trace={trace5}",
    )

    print("ALL PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
