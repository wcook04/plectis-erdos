#!/usr/bin/env python3
"""Exact replay for the log-geometric pair-tangent collapse obstruction."""

from fractions import Fraction as Q
import hashlib
import sympy as sp


def log_bounds(q: Q, terms: int = 6) -> tuple[Q, Q]:
    """Rational enclosure from log(q)=2*atanh((q-1)/(q+1))."""
    z = (q - 1) / (q + 1)
    a = abs(z)
    partial = 2 * sum(a ** (2 * k + 1) / Q(2 * k + 1) for k in range(terms + 1))
    tail = 2 * a ** (2 * terms + 3) / Q(2 * terms + 3) / (1 - a * a)
    if z >= 0:
        return partial, partial + tail
    return -(partial + tail), -partial


def A(r: Q) -> Q:
    return (1 + r) / (1 - r)


def B(r: Q) -> Q:
    return (1 - r * r) / (1 + r + r * r)


def main() -> None:
    # Symbolic collapse identity (3).
    x = sp.symbols("x", positive=True)
    d = 1 + x + x**2
    assert sp.factor(A(sp.Rational(1, 2)) * B(sp.Rational(1, 2))) == sp.Rational(9, 7)
    assert sp.simplify(((1 + x) / (1 - x)) * ((1 - x**2) / d) - (1 + x / d)) == 0
    u = sp.symbols("u", positive=True)
    h = u - sp.log(1 + u)
    assert sp.simplify(h.subs(u, 0)) == 0
    assert sp.simplify(sp.diff(h, u) - u / (1 + u)) == 0

    # Positive rational witness with rational cube root s.
    r = [Q(1, 8), Q(1, 8), Q(1, 64000)]
    s = Q(1, 160)
    p = r[0] * r[1] * r[2]
    assert s**3 == p
    T = 3 * (1 + p) / (1 - p)
    alpha = A(s) / T
    beta = B(s) / T
    assert alpha + 2 * beta == 1

    R = sum(r)
    d = [1 + q + q * q for q in r]
    a = 2 * r[0] * r[1] * (1 / d[0] + 1 / d[1])
    b = 2 * r[1] * r[2] * (1 / d[1] + 1 / d[2])
    c = 2 * r[2] * r[0] * (1 / d[2] + 1 / d[0])
    assert b == c
    # Reciprocals form a strict triangle, so the stationary formula applies.
    assert 1 / a < 1 / b + 1 / c
    assert 1 / b < 1 / a + 1 / c
    assert 1 / c < 1 / a + 1 / b
    M = -(a * a * b * b + a * a * c * c + b * b * c * c) / (2 * a * b * c)
    assert M == -a - b * b / (2 * a)

    lower = upper = beta * (M + (a + b + c) / 2)
    for i in range(3):
        lo, hi = log_bounds(A(r[i]) / A(s))
        lower += alpha * r[i] * lo
        upper += alpha * r[i] * hi
        lo, hi = log_bounds(B(r[i]) / B(s))
        lower += beta * (R - r[i]) * lo
        upper += beta * (R - r[i]) * hi

    assert lower <= upper < 0
    digest = hashlib.sha256(f"{upper.numerator}/{upper.denominator}".encode()).hexdigest()
    print("Three-exterior endpoint log-geometric pair-tangent obstruction: PASS")
    print(f"witness radii: {r}; s={s}")
    print(f"exact upper bound < {float(upper):.16g}")
    print(f"upper-bound digest: {digest}")
    print("boundary: pair-tangent residual false; untangented log conjecture remains open")


if __name__ == "__main__":
    main()
