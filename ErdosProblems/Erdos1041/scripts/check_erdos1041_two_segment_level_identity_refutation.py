#!/usr/bin/env python3
"""Exact rational certificate refuting the proposed identity V_E = mu.

The seven roots and every certificate centre/waypoint are dyadic rationals.
All decisive inequalities are therefore checked with ``fractions.Fraction``.
Floating point is used only to print readable decimal projections after the
exact verdict has already been obtained.

Certificate structure:

* the seven listed roots lie strictly in the open unit disk;
* six disjoint radius-10^-12 disks each contain exactly one root of f' by
  Rouche, using the linear Taylor term as comparator, and therefore exhaust
  all critical points;
* interval bounds on |f|^2 make the first disk the unique least-critical one;
* on every one of the seven root spokes, a pinned dyadic parameter has
  |f|^2 strictly above the critical level throughout the first critical disk.

The last topological step -- a level-mu two-arm connection must contain the
unique first-merge point and hence a safe critical-to-root subsegment -- is the
abstract Lean theorem in ``TwoSegmentLevelIdentityRefutation.lean``.
"""
from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path


REPO = Path(__file__).resolve().parents[5]
RECEIPT = (
    REPO
    / "state/formal_math/erdos257_period_noncollapse/"
      "erdos1041_two_segment_level_identity_refutation_receipt.json"
)

ROOTS_HEX = (
    ("0x1.f16d34e653080p-1", "0x1.048db21e8a26ep-11"),
    ("0x1.3611c8c7f123bp-1", "0x1.84f5dd56439d6p-1"),
    ("-0x1.c25ccee7ebf51p-3", "0x1.e484537697ef0p-1"),
    ("-0x1.c0642306615f0p-1", "0x1.aeb6caa028559p-2"),
    ("-0x1.c034b033157f8p-1", "-0x1.af7c2858d4c31p-2"),
    ("-0x1.bb4b3bb78fb9cp-3", "-0x1.e4ec9549d88d0p-1"),
    ("0x1.3601e3b4a2871p-1", "-0x1.8502889213fe9p-1"),
)

CRITICAL_CENTRES_HEX = (
    ("-0x1.31866555b5d14p-2", "-0x1.460aff404e4e0p-8"),
    ("-0x1.215d0e3a23c1ap-3", "-0x1.f7e377ebf0d22p-3"),
    ("-0x1.394c1b2c95069p-3", "0x1.1d05c9490c3d0p-2"),
    ("0x1.0e3b10a53d0ddp-3", "-0x1.fa14c6b57d266p-3"),
    ("0x1.1bbce690da2adp-2", "-0x1.2ca0bac4e142fp-6"),
    ("0x1.6f68192bff498p-3", "0x1.e5ad351cac699p-3"),
)

SPOKE_T_HEX = (
    "0x1.cd7799a72b616p-2",
    "0x1.079b1522d0e59p-1",
    "0x1.dce36ffcdfd75p-2",
    "0x1.867ec05692356p-4",
    "0x1.3f3e9f87968a4p-4",
    "0x1.d7b243d59cb58p-2",
    "0x1.01e1cc3521567p-1",
)


def dyadic(text: str) -> F:
    return F.from_float(float.fromhex(text))


def cplx(re: F | int = 0, im: F | int = 0) -> tuple[F, F]:
    return F(re), F(im)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[0], -a[1]


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(a, s: F):
    return a[0] * s, a[1] * s


def norm_sq(a) -> F:
    return a[0] * a[0] + a[1] * a[1]


def norm_upper_l1(a) -> F:
    return abs(a[0]) + abs(a[1])


def norm_lower_linf(a) -> F:
    return max(abs(a[0]), abs(a[1]))


def poly_eval(p, z):
    out = cplx()
    for coefficient in p:
        out = add(mul(out, z), coefficient)
    return out


def derivative(p):
    degree = len(p) - 1
    return [scale(a, F(degree - i)) for i, a in enumerate(p[:-1])]


def polynomial_from_roots(roots):
    p = [cplx(1)]
    for root in roots:
        out = [cplx() for _ in range(len(p) + 1)]
        for i, coefficient in enumerate(p):
            out[i] = add(out[i], coefficient)
            out[i + 1] = add(out[i + 1], neg(mul(coefficient, root)))
        p = out
    return p


def squared_value_error(value_at_centre, displacement: F, lipschitz: F) -> F:
    eps = lipschitz * displacement
    # If |u-v| <= eps, then ||u|^2-|v|^2| <= 2|v|eps+eps^2.
    return 2 * norm_upper_l1(value_at_centre) * eps + eps * eps


def main() -> int:
    roots = [cplx(dyadic(x), dyadic(y)) for x, y in ROOTS_HEX]
    centres = [cplx(dyadic(x), dyadic(y)) for x, y in CRITICAL_CENTRES_HEX]
    spoke_t = [dyadic(t) for t in SPOKE_T_HEX]
    radius = F(1, 10**12)

    root_norm_sq = [norm_sq(z) for z in roots]
    roots_inside = all(s < 1 for s in root_norm_sq)
    roots_distinct = all(roots[i] != roots[j] for i in range(7) for j in range(i))

    f = polynomial_from_roots(roots)
    fp = derivative(f)

    # On the unit disk enlarged by radius, every factor in f' is below 3.
    # This deliberately crude exact bound is ample for all interval transfers.
    lipschitz = F(7 * 3**6)

    rouche_rows = []
    rouche_ok = True
    for centre in centres:
        derivatives = []
        q = fp
        while q:
            derivatives.append(poly_eval(q, centre))
            q = derivative(q)
        linear_floor = norm_lower_linf(derivatives[1]) * radius
        remainder_ceiling = norm_upper_l1(derivatives[0])
        factorial = 1
        for k in range(2, len(derivatives)):
            factorial *= k
            remainder_ceiling += (
                norm_upper_l1(derivatives[k]) * radius**k / factorial
            )
        ok = linear_floor > remainder_ceiling
        rouche_ok &= ok
        rouche_rows.append(
            {
                "linear_over_remainder": float(linear_floor / remainder_ceiling),
                "ok": ok,
            }
        )

    disks_disjoint = True
    for i in range(len(centres)):
        for j in range(i):
            delta = add(centres[i], neg(centres[j]))
            disks_disjoint &= norm_sq(delta) > (2 * radius) ** 2

    critical_values_sq = [norm_sq(poly_eval(f, c)) for c in centres]
    critical_errors = [
        squared_value_error(poly_eval(f, c), radius, lipschitz) for c in centres
    ]
    unique_minimum = all(
        critical_values_sq[j] - critical_errors[j]
        > critical_values_sq[0] + critical_errors[0]
        for j in range(1, len(centres))
    )

    first_value = poly_eval(f, centres[0])
    first_error = squared_value_error(first_value, radius, lipschitz)
    spoke_rows = []
    all_spokes_unsafe = True
    for root, t in zip(roots, spoke_t, strict=True):
        waypoint = add(scale(centres[0], 1 - t), scale(root, t))
        waypoint_value = poly_eval(f, waypoint)
        waypoint_error = squared_value_error(
            waypoint_value, (1 - t) * radius, lipschitz
        )
        exact_gap_at_centres = norm_sq(waypoint_value) - norm_sq(first_value)
        certified_gap = exact_gap_at_centres - waypoint_error - first_error
        ok = certified_gap > 0
        all_spokes_unsafe &= ok
        spoke_rows.append(
            {
                "t": float(t),
                "exact_squared_gap_at_centres": float(exact_gap_at_centres),
                "interval_error": float(waypoint_error + first_error),
                "certified_squared_gap": float(certified_gap),
                "ok": ok,
            }
        )

    ok = (
        roots_inside
        and roots_distinct
        and rouche_ok
        and disks_disjoint
        and unique_minimum
        and all_spokes_unsafe
    )
    receipt = {
        "schema": "erdos1041_two_segment_level_identity_refutation_receipt_v1",
        "verdict": "pass" if ok else "fail",
        "exact_arithmetic": "fractions.Fraction over dyadic root/centre/waypoint data",
        "degree": 7,
        "critical_disk_radius": float(radius),
        "roots_inside_open_unit_disk": roots_inside,
        "roots_distinct": roots_distinct,
        "rouche_disks": rouche_rows,
        "rouche_disks_disjoint": disks_disjoint,
        "critical_disks_exhaust_derivative_degree": rouche_ok and disks_disjoint,
        "unique_least_critical_disk": unique_minimum,
        "critical_value_modulus_centres": [float(x**F(1, 2)) for x in critical_values_sq],
        "all_seven_spokes_certifiably_unsafe_at_first_level": all_spokes_unsafe,
        "spokes": spoke_rows,
        "claim_boundary": (
            "Refutes V_E=mu and SPOKE>=1. Does not refute the level-one "
            "free-hub conjecture or Erdos #1041."
        ),
    }
    RECEIPT.parent.mkdir(parents=True, exist_ok=True)
    RECEIPT.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
