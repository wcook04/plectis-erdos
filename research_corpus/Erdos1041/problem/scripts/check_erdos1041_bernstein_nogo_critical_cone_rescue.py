#!/usr/bin/env python3
"""Exact rational-ball rescue of the Bernstein quintic no-go."""

from __future__ import annotations

from math import comb, isqrt

import sympy as sp


def sqrt_bounds(x: sp.Rational, digits: int = 30) -> tuple[sp.Rational, sp.Rational]:
    assert x >= 0
    scale = 10**digits
    num, den = int(sp.numer(x)), int(sp.denom(x))
    lo_int = isqrt((num * scale * scale) // den)
    while (lo_int + 1) ** 2 * den <= num * scale * scale:
        lo_int += 1
    while lo_int**2 * den > num * scale * scale:
        lo_int -= 1
    return sp.Rational(lo_int, scale), sp.Rational(lo_int + 1, scale)


def norm_bounds(z: sp.Expr, digits: int = 30) -> tuple[sp.Rational, sp.Rational]:
    sq = sp.factor(sp.re(z * sp.conjugate(z)))
    return sqrt_bounds(sq, digits)


def bernstein_controls(poly: sp.Poly, a: sp.Expr) -> list[sp.Expr]:
    coeff = list(reversed(poly.all_coeffs()))
    q = [coeff[k] * a**k for k in range(6)]
    return [
        sp.factor(
            sum(q[k] * sp.Rational(comb(j, k), comb(5, k)) for k in range(j + 1))
        )
        for j in range(6)
    ]


def zero_bernstein_safe_rescue() -> tuple[sp.Rational, sp.Rational]:
    """The canonical torus witness has zero Bernstein-safe roots but a deep cone."""

    r = sp.Rational(99999, 100000)
    roots = [
        r,
        r * (-20 + 99 * sp.I) / 101,
        r * (-20 - 99 * sp.I) / 101,
        r * (-28 + 195 * sp.I) / 197,
        r * (-28 - 195 * sp.I) / 197,
    ]
    z, w = sp.symbols("z w")
    poly = sp.Poly(sp.prod(z - a for a in roots), z)

    # Every root fails at least one exact Bernstein control.
    failure_indices = [3, 1, 1, 1, 1]
    for a, j in zip(roots, failure_indices, strict=True):
        b = bernstein_controls(poly, a)[j]
        gap = sp.factor(sp.re(b * sp.conjugate(b)) - 1)
        assert sp.sign(gap) == 1

    center = sp.Rational("-0.17007015573494415") + sp.I * sp.Rational(
        "0.98440121712080436"
    )
    radius = sp.Rational(1, 10**8)

    # Isolate one upper-half-plane critical point by Rouche.
    shifted_d = sp.Poly(sp.expand(poly.diff().as_expr().subs(z, center + w)), w)
    dc = list(reversed(shifted_d.all_coeffs()))
    a1_lo, _ = norm_bounds(dc[1])
    rhs = sp.Rational(0)
    for k, ak in enumerate(dc):
        if k == 1:
            continue
        rhs += norm_bounds(ak)[1] * radius**k
    assert a1_lo * radius > rhs

    shifted_p = sp.Poly(sp.expand(poly.as_expr().subs(z, center + w)), w)
    pc = list(reversed(shifted_p.all_coeffs()))
    mu_up = sum(norm_bounds(ak)[1] * radius**k for k, ak in enumerate(pc))
    assert mu_up < sp.Rational(1, 200)

    # The roots in upper directions (-20+99i)/101 and (-28+195i)/197
    # are uniformly the two nearest on the critical disk.
    bounds = []
    for a in roots:
        lo, up = norm_bounds(a - center)
        bounds.append((lo - radius, up + radius))
    assert bounds[1][1] < bounds[3][0]
    assert bounds[3][1] < min(bounds[j][0] for j in (0, 2, 4))

    i = 3
    s_up = bounds[i][1] ** 2 * sum(
        1 / bounds[k][0] ** 2 for k in range(5) if k != i
    )
    assert s_up < sp.Rational(3, 2)
    return mu_up, s_up


def main() -> None:
    raw = [
        ("0.9954764088478315", "-0.08383149424545093"),
        ("0.14881265879891825", "0.9878541352756472"),
        ("-0.6277869770917356", "0.7771000652387186"),
        ("-0.5684933442778939", "-0.8214720430493883"),
        ("0.26099542375571383", "-0.964304095593592"),
    ]
    roots = [sp.Rational(x) + sp.I * sp.Rational(y) for x, y in raw]
    z, w = sp.symbols("z w")
    poly = sp.Poly(sp.prod(z - a for a in roots), z)
    deriv = poly.diff()

    center = sp.Rational("-0.21899631614693127") + sp.I * sp.Rational("0.7322132764652212")
    radius = sp.Rational(1, 10**8)

    # Rouche on |w|=radius: the linear Taylor term of P' dominates.
    shifted_d = sp.Poly(sp.expand(deriv.as_expr().subs(z, center + w)), w)
    dc = list(reversed(shifted_d.all_coeffs()))
    a1_lo, _ = norm_bounds(dc[1])
    rhs = sp.Rational(0)
    for k, ak in enumerate(dc):
        if k == 1:
            continue
        _, up = norm_bounds(ak)
        rhs += up * radius**k
    assert a1_lo * radius > rhs

    # The isolated critical value stays strictly below one on the full disk.
    shifted_p = sp.Poly(sp.expand(poly.as_expr().subs(z, center + w)), w)
    pc = list(reversed(shifted_p.all_coeffs()))
    mu_up = sp.Rational(0)
    for k, ak in enumerate(pc):
        _, up = norm_bounds(ak)
        mu_up += up * radius**k
    assert mu_up < 1

    # Distance tubes identify roots a_3 and a_2 (zero-based 2 and 1) as the
    # two nearest throughout the critical disk.
    bounds = []
    for a in roots:
        lo, up = norm_bounds(a - center)
        bounds.append((lo - radius, up + radius))
    assert bounds[2][1] < bounds[1][0]
    assert bounds[1][1] < min(bounds[j][0] for j in (0, 3, 4))

    # For the second-nearest root i=1, S_i=sum_{k!=i}|d_i/d_k|^2 < 3/2.
    i = 1
    s_up = bounds[i][1] ** 2 * sum(
        1 / bounds[k][0] ** 2 for k in range(5) if k != i
    )
    assert s_up < sp.Rational(3, 2)

    # n=5 occupied-cone threshold: S<=3/2 implies the AM-GM row F(t)<=1.
    t = sp.symbols("t", nonnegative=True)
    # The analytic proof uses the positive binomial tail; exact scalar replay
    # below checks the equivalent polynomial after squaring at the threshold.
    f_threshold = sp.expand((1 - t) * (1 + (2 * t + sp.Rational(3, 2) * t**2) / 4) ** 2)
    positive_gap = t**3 * (9 * t**2 + 15 * t + 40) / 64
    assert sp.factor(1 - f_threshold) == positive_gap

    zero_mu_up, zero_s_up = zero_bernstein_safe_rescue()

    print("Bernstein no-go critical-cone rescue: PASS")
    print(f"Rouche radius: {float(radius):.1e}")
    print(f"critical-value upper bound: {float(mu_up):.12f}")
    print(f"second-nearest S upper bound: {float(s_up):.12f}")
    print("zero-Bernstein-safe torus witness: RESCUED")
    print(f"zero-safe critical-value upper bound: {float(zero_mu_up):.12f}")
    print(f"zero-safe second-nearest S upper bound: {float(zero_s_up):.12f}")


if __name__ == "__main__":
    main()
