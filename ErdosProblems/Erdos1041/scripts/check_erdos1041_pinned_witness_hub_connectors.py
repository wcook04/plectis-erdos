#!/usr/bin/env python3
"""Exact replay of both noncritical-hub connector certificates on the pinned witnesses.

The degree-six and degree-nine configurations stored as
``QC_REFUTATION_WITNESSES`` in
``check_erdos1041_straight_spoke_hub_criterion.py`` were recorded there to
refute the *critical*-hub two-straight-spoke mechanism.  That refutation is
untouched here.  This checker certifies two positive statements about the same
two configurations, both using *noncritical* hubs:

``two_segment``   a_i -> h -> a_j through a fixed Gaussian-rational hub h,
                  contained in {|f| < 99999/100000}, lengths bounded by the
                  dyadic rationals 29471595/2^24 < 1.757 and 12825029/2^23
                  < 1.529.

``three_segment`` a_i -> t a_i -> t a_j -> a_j with rational t, contained in
                  {|f|^2 < 19999/20000}, lengths below 181/100 and 1623/1000.

Containment is decided on each whole segment by the Bernstein coefficients of a
rational polynomial in the segment parameter, so no sampling, subdivision,
floating-point root isolation or numerical integration enters the certificate.
Every arithmetic operation below is on ``fractions.Fraction``.

The hexadecimal root literals are read from the pinned module by AST parsing
(the module itself pulls in ``mpmath`` and ``numpy``, which this stdlib-only
checker does not want to require).  A byte-equality assertion against the
embedded copy runs unconditionally, so this checker fails loudly if the pinned
witness data is ever edited.

The two certificates are positive evidence for noncritical hubs as connector
candidates.  They are two configurations, plus explicit 10^-9 root
neighbourhoods, and they are not a proof of Erdos 1041.
"""

from __future__ import annotations

import ast
import json
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path

PINNED_MODULE = (
    Path(__file__).resolve().parent / "check_erdos1041_straight_spoke_hub_criterion.py"
)
PINNED_SYMBOL = "QC_REFUTATION_WITNESSES"

#: Embedded copy of the pinned witness literals, asserted equal to the module's.
EMBEDDED_WITNESSES: dict[int, tuple[tuple[str, str], ...]] = {
    6: (
        ("0x1.fffffaead1dfdp-1", "-0x1.c7f97b12bedcep-15"),
        ("0x1.004ed623acd87p-1", "0x1.bb3a1b3208ad6p-1"),
        ("-0x1.ffded10fb5c87p-2", "0x1.bb713c92edfe4p-1"),
        ("-0x1.fffff9e87dd68p-1", "-0x1.0766ef919e3d1p-12"),
        ("-0x1.00485f6af598cp-1", "-0x1.bb3dd8051992dp-1"),
        ("0x1.00198d2225a68p-1", "-0x1.bb58e733c06dcp-1"),
    ),
    9: (
        ("0x1.fffffadb279edp-1", "-0x1.54cbe5f38764ep-14"),
        ("0x1.882fdda9ba317p-1", "0x1.4922d6b3868dfp-1"),
        ("0x1.63e8c845cba7bp-3", "0x1.f83590b0811ebp-1"),
        ("-0x1.fffb9be200080p-2", "0x1.bb68ed350eca4p-1"),
        ("-0x1.e121a80180737p-1", "0x1.5e2df749c719cp-2"),
        ("-0x1.e11b7beb2b6bep-1", "-0x1.5e4fe150117d8p-2"),
        ("-0x1.0005816d133a1p-1", "-0x1.bb647aee76a86p-1"),
        ("0x1.637127244f7d2p-3", "-0x1.f83ad6df31cf7p-1"),
        ("0x1.8833eebb49d0cp-1", "-0x1.491f0e2e50785p-1"),
    ),
}


def pinned_witnesses() -> dict[int, tuple[tuple[str, str], ...]]:
    """Read the pinned literal without importing the module's heavy dependencies."""

    tree = ast.parse(PINNED_MODULE.read_text(encoding="utf-8"))
    for node in tree.body:
        target = None
        if isinstance(node, ast.AnnAssign):
            target = node.target
        elif isinstance(node, ast.Assign) and len(node.targets) == 1:
            target = node.targets[0]
        if isinstance(target, ast.Name) and target.id == PINNED_SYMBOL:
            return ast.literal_eval(node.value)
    raise AssertionError(f"{PINNED_SYMBOL} not found in {PINNED_MODULE}")


# --------------------------------------------------------------------------
# exact Gaussian-rational arithmetic
# --------------------------------------------------------------------------

Q = tuple[F, F]


def hex_fraction(text: str) -> F:
    """Decode an IEEE-754 hexadecimal literal as an exact rational."""

    sign = -1 if text.startswith("-") else 1
    mantissa, exponent = text.lstrip("+-").split("p")
    whole, fractional = mantissa[2:].split(".")
    numerator = sign * int(whole + fractional, 16)
    power = int(exponent) - 4 * len(fractional)
    return F(numerator * 2 ** max(power, 0), 2 ** max(-power, 0))


def add(a: Q, b: Q) -> Q:
    return a[0] + b[0], a[1] + b[1]


def sub(a: Q, b: Q) -> Q:
    return a[0] - b[0], a[1] - b[1]


def mul(a: Q, b: Q) -> Q:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(t: F, a: Q) -> Q:
    return t * a[0], t * a[1]


def dot(a: Q, b: Q) -> F:
    return a[0] * b[0] + a[1] * b[1]


def norm2(a: Q) -> F:
    return dot(a, a)


def to_bernstein(coefficients: list[F]) -> list[F]:
    """Ascending monomial coefficients to Bernstein coefficients on [0,1]."""

    degree = len(coefficients) - 1
    return [
        sum(
            (
                coefficients[j] * F(comb(k, j), comb(degree, j))
                for j in range(k + 1)
            ),
            F(0),
        )
        for k in range(degree + 1)
    ]


def segment_value_poly(roots: list[Q], start: Q, finish: Q) -> list[Q]:
    """Ascending coefficients of ``f(start + u*(finish-start))``."""

    direction = sub(finish, start)
    poly: list[Q] = [(F(1), F(0))]
    for root in roots:
        out: list[Q] = [(F(0), F(0)) for _ in range(len(poly) + 1)]
        for k, coefficient in enumerate(poly):
            out[k] = add(out[k], mul(coefficient, sub(start, root)))
            out[k + 1] = add(out[k + 1], mul(coefficient, direction))
        poly = out
    return poly


def squared_modulus_poly(poly: list[Q]) -> list[F]:
    """Ascending coefficients of ``|p(u)|^2`` for real ``u``."""

    out = [F(0) for _ in range(2 * len(poly) - 1)]
    for i, x in enumerate(poly):
        for j, y in enumerate(poly):
            out[i + j] += x[0] * y[0] + x[1] * y[1]
    return out


def sqrt_upper(value: F, bits: int = 24) -> F:
    """Smallest dyadic rational with denominator ``2**bits`` above ``sqrt(value)``."""

    numerator = value.numerator * 2 ** (2 * bits)
    denominator = value.denominator
    root = isqrt(numerator // denominator)
    if root * root * denominator < numerator:
        root += 1
    result = F(root, 2**bits)
    assert result * result >= value
    return result


# --------------------------------------------------------------------------
# certificate A: two straight segments through a noncritical Gaussian hub
# --------------------------------------------------------------------------

TWO_SEGMENT_CASES = (
    # degree, endpoint indices, hub, per-endpoint Bernstein lower bounds / 10^8,
    # certified length, decimal ceiling
    (6, (0, 1), (F(3, 25), F(2, 25)), (7919, 5296), F(29471595, 16777216), F(1757, 1000)),
    (9, (5, 6), (F(-1, 5), F(-4, 25)), (6823, 2543), F(12825029, 8388608), F(1529, 1000)),
)
TWO_SEGMENT_LEVEL = F(99999, 100000)

# --------------------------------------------------------------------------
# certificate B: two radial arms and a chord, all through noncritical points
# --------------------------------------------------------------------------

THREE_SEGMENT_CASES = (
    # degree, endpoint indices, radial factor, chord bound, Bernstein ceilings / 10^6,
    # length ceiling
    (6, (0, 1), F(19, 100), F(1), (999679, 999916, 999876), F(181, 100)),
    (9, (6, 7), F(29, 100), F(7, 10), (999809, 999888, 999865), F(1623, 1000)),
)
THREE_SEGMENT_LEVEL = F(19999, 20000)

DELTA = F(1, 10**9)
ROOT_MODULUS_CEILING = F(9999999, 10**7)


def two_segment_certificate(degree: int, witnesses: dict) -> dict:
    for deg, pair, hub, lower_bounds, length_bound, decimal in TWO_SEGMENT_CASES:
        if deg != degree:
            continue
        roots = [
            (hex_fraction(real), hex_fraction(imaginary))
            for real, imaginary in witnesses[degree]
        ]
        assert all(norm2(root) < ROOT_MODULUS_CEILING**2 for root in roots)
        length = F(0)
        margins = []
        coefficient_count = 0
        for index, lower in zip(pair, lower_bounds):
            poly = segment_value_poly(roots, hub, roots[index])
            # poly[1] = (a_j - h) * f'(h); the direction is nonzero, so a nonzero
            # linear coefficient is an exact proof that the hub is noncritical.
            assert poly[1] != (F(0), F(0)), "hub is critical"
            squared = squared_modulus_poly(poly)
            slack = [-c for c in squared]
            slack[0] += TWO_SEGMENT_LEVEL**2
            bernstein = to_bernstein(slack)
            coefficient_count += len(bernstein)
            assert min(bernstein) > F(lower, 10**8) > 0
            margins.append(str(min(bernstein) - F(lower, 10**8) > 0))
            length += sqrt_upper(norm2(sub(roots[index], hub)))
        assert length == length_bound
        assert length < decimal < 2
        # explicit 10^-9 root neighbourhood
        drift = 2 * degree * DELTA * (2 + 2 * DELTA) ** (degree - 1)
        assert drift < F(1, 100000)
        assert ROOT_MODULUS_CEILING + DELTA < 1
        assert length + 2 * DELTA < 2
        return {
            "degree": degree,
            "endpoints": list(pair),
            "hub": [str(hub[0]), str(hub[1])],
            "hub_noncritical": True,
            "level": str(TWO_SEGMENT_LEVEL),
            "bernstein_coefficients": coefficient_count,
            "length_bound": str(length_bound),
            "length_decimal_ceiling": str(decimal),
            "neighbourhood_radius": str(DELTA),
            "neighbourhood_value_drift_below": "1e-05",
            "neighbourhood_value_drift": f"{float(drift):.6e}",
        }
    raise AssertionError(degree)


def three_segment_certificate(degree: int, witnesses: dict) -> dict:
    for deg, pair, radial, chord_bound, ceilings, length_ceiling in THREE_SEGMENT_CASES:
        if deg != degree:
            continue
        roots = [
            (hex_fraction(real), hex_fraction(imaginary))
            for real, imaginary in witnesses[degree]
        ]
        assert all(norm2(root) < ROOT_MODULUS_CEILING**2 for root in roots)
        first, second = roots[pair[0]], roots[pair[1]]
        assert norm2(sub(first, second)) < (chord_bound - 2 * DELTA) ** 2
        # the whole path sits in an open half-plane missing the origin, which is
        # what Theorem 4's holomorphic m-th root branch needs
        coordinate = (lambda a: a[0]) if degree == 6 else (lambda a: -a[1])
        assert min(coordinate(first), coordinate(second)) > F(1, 2) + DELTA
        nodes = [first, scale(radial, first), scale(radial, second), second]
        coefficient_count = 0
        for start, finish, ceiling in zip(nodes, nodes[1:], ceilings):
            poly = segment_value_poly(roots, start, finish)
            bernstein = to_bernstein(squared_modulus_poly(poly))
            coefficient_count += len(bernstein)
            assert max(bernstein) < F(ceiling, 10**6) < THREE_SEGMENT_LEVEL
        drift = 2 * degree * DELTA * (2 + 2 * DELTA) ** (degree - 1)
        assert drift < (1 - THREE_SEGMENT_LEVEL) / 2
        assert ROOT_MODULUS_CEILING + DELTA < 1
        length_bound = 2 * (1 - radial) + radial * chord_bound
        assert length_bound <= length_ceiling < 2
        return {
            "degree": degree,
            "endpoints": list(pair),
            "radial_factor": str(radial),
            "level_squared": str(THREE_SEGMENT_LEVEL),
            "bernstein_coefficients": coefficient_count,
            "length_bound": str(length_bound),
            "neighbourhood_radius": str(DELTA),
            "neighbourhood_value_drift_below": "2.5e-05",
            "neighbourhood_value_drift": f"{float(drift):.6e}",
        }
    raise AssertionError(degree)


def cyclic_pullback_length(degree: int, power: int) -> F:
    """Upper bound (22) for ``P_d(z^m)``, evaluated as an exact rational at m=1."""

    for deg, _pair, radial, chord_bound, _ceilings, _ceiling in THREE_SEGMENT_CASES:
        if deg == degree and power == 1:
            return 2 * (1 - radial) + radial * chord_bound
    raise AssertionError((degree, power))


def main() -> None:
    module_witnesses = pinned_witnesses()
    assert module_witnesses == EMBEDDED_WITNESSES, (
        "embedded witness data no longer matches "
        f"{PINNED_SYMBOL} in {PINNED_MODULE.name}"
    )
    witnesses = module_witnesses

    two_segment = [two_segment_certificate(degree, witnesses) for degree in (6, 9)]
    three_segment = [three_segment_certificate(degree, witnesses) for degree in (6, 9)]
    assert sum(row["bernstein_coefficients"] for row in three_segment) == 96
    assert sum(row["bernstein_coefficients"] for row in two_segment) == 2 * (
        2 * 6 + 1
    ) + 2 * (2 * 9 + 1)
    # the two-segment connector is the shorter certificate in both degrees
    for short, long in zip(two_segment, three_segment):
        assert F(short["length_bound"]) < F(long["length_bound"])
    # m = 1 of the cyclic pullback family reproduces the base three-segment bound
    for degree in (6, 9):
        assert cyclic_pullback_length(degree, 1) < 2

    print(
        json.dumps(
            {
                "status": "pass",
                "witness_source": str(PINNED_MODULE.name),
                "witness_byte_equality": True,
                "two_segment_certificates": two_segment,
                "three_segment_certificates": three_segment,
                "evidence_class": "exact_rational_bernstein_certificate",
                "universal_authority": "PinnedWitnessNoncriticalHubConnectors.md",
                "claim_boundary": (
                    "two pinned configurations plus explicit 1e-9 root "
                    "neighbourhoods; not a proof of Erdos 1041"
                ),
            }
        )
    )


if __name__ == "__main__":
    main()
