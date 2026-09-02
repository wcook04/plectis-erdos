#!/usr/bin/env python3
"""Regression guard: the first-merge-hub spoke claim is false at the stored witnesses.

`CriticalBudgetLab.md` carried a conditional theorem for Erdős #1041 assembled at
``c*``, the admissible critical point of least critical value ``T* = |f(c*)|``.  It
rested on two claims measured on random samples:

  claim 2  the two roots the descent branches at ``c*`` reach are the two *nearest*
           roots to ``c*``;
  claim 3  on each spoke ``[z_a, c*]`` the exact maximum of ``|f|`` is ``T*``, so
           ``|f|`` is monotone along the spoke and the spoke lies in the closed cell.

Claim 3 is false.  ``StraightSpokeHubCriterionLab.md`` §3/§5 already records that
the contained-spoke objective restricted to ``c*`` is infinite -- fewer than two
contained spokes at ``c*`` -- at degrees 6, 8, 9 and 12, and stores the degree-6
and degree-9 configurations as exact IEEE-754 hexadecimal literals in
``check_erdos1041_straight_spoke_hub_criterion.QC_REFUTATION_WITNESSES`` precisely
because the margins are near ``1e-5`` and do not survive decimal rounding.

This guard re-reads those exact witnesses and evaluates claim 3 directly at 60
decimal digits.  At both witnesses a nearest-root spoke at ``c*`` rises above
``|f| = 1`` and therefore leaves the target lemniscate:

    degree 6   max |f| = 1.00000933323494222   at t = 0.876281
    degree 9   max |f| = 1.00001038513246428   at t = 0.805549

so the broken line ``z_a -> c* -> z_b`` through the two nearest roots is not
contained, and the conditional theorem's construction fails at those
configurations.  The *length* half is not what fails: ``d1 + d2`` is 1.7166 and
1.4978 there, comfortably inside the global budget theorem's bound of 2.
Containment fails, which is the same conclusion as the packet's "curvature is
forced" negative result.

This script is a falsifier, not a proof of anything.  It fails (exit 1) if a
future edit makes the stored witnesses stop refuting claim 3, which would mean
either the witnesses or this guard has drifted.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any

from mpmath import mp, mpc, mpf

_HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

import check_erdos1041_straight_spoke_hub_criterion as _witness_module  # noqa: E402

#: Working precision.  The recorded margins are near 1e-5; 60 digits is far more
#: than enough and matches the precision the witnesses were verified at.
DEFAULT_DIGITS = 60

#: Segment sampling for the spoke maximum.  The spoke maxima here are interior
#: and smooth, so a dense uniform sweep plus a local refinement is sufficient.
DEFAULT_SAMPLES = 4001


def _roots_of(literals: tuple[tuple[str, str], ...]) -> list[mpc]:
    return [
        mpc(mpf(float.fromhex(real)), mpf(float.fromhex(imag)))
        for real, imag in literals
    ]


def _value(roots: list[mpc], point: mpc) -> mpf:
    acc = mpc(1)
    for root in roots:
        acc *= point - root
    return abs(acc)


def _derivative(roots: list[mpc], point: mpc) -> mpc:
    total = mpc(0)
    for index in range(len(roots)):
        term = mpc(1)
        for other in range(len(roots)):
            if other != index:
                term *= point - roots[other]
        total += term
    return total


def _critical_points(roots: list[mpc]) -> list[mpc]:
    """Numpy seeds relocated by Newton on ``f'`` at working precision."""
    import numpy as np

    coefficients = np.poly(np.array([complex(root) for root in roots]))
    seeds = np.roots(np.polyder(coefficients))
    step_h = mpf(10) ** (-(mp.dps // 2))
    located: list[mpc] = []
    for seed in seeds:
        point = mpc(complex(seed))
        for _ in range(80):
            first = _derivative(roots, point)
            second = (
                _derivative(roots, point + step_h) - _derivative(roots, point - step_h)
            ) / (2 * step_h)
            if abs(second) == 0:
                break
            step = first / second
            point -= step
            if abs(step) < mpf(10) ** (-(mp.dps - 10)):
                break
        located.append(point)
    return located


def _segment_max(
    roots: list[mpc], start: mpc, end: mpc, samples: int
) -> tuple[mpf, mpf]:
    """Maximum of ``|f|`` on ``[start, end]`` with one local refinement pass."""
    best = mpf(0)
    best_t = mpf(0)
    for index in range(samples + 1):
        t = mpf(index) / samples
        current = _value(roots, start + (end - start) * t)
        if current > best:
            best, best_t = current, t
    width = mpf(1) / samples
    lo, hi = max(mpf(0), best_t - width), min(mpf(1), best_t + width)
    for index in range(samples + 1):
        t = lo + (hi - lo) * mpf(index) / samples
        current = _value(roots, start + (end - start) * t)
        if current > best:
            best, best_t = current, t
    return best, best_t


def evaluate_witness(degree: int, literals, samples: int) -> dict[str, Any]:
    roots = _roots_of(literals)
    if len(roots) != degree:
        raise AssertionError(f"degree {degree} witness carries {len(roots)} roots")
    if max(abs(root) for root in roots) >= 1:
        raise AssertionError(f"degree {degree} witness left the open unit disk")

    admissible = [
        (_value(roots, point), point)
        for point in _critical_points(roots)
        if _value(roots, point) < 1
    ]
    if not admissible:
        raise AssertionError(f"degree {degree} witness has no admissible hub")
    admissible.sort(key=lambda row: row[0])
    critical_value, hub = admissible[0]

    ordered = sorted(
        ((abs(hub - root), index, root) for index, root in enumerate(roots)),
        key=lambda row: row[0],
    )
    spokes = []
    worst = mpf(0)
    for rank in (0, 1):
        distance, index, root = ordered[rank]
        maximum, at = _segment_max(roots, root, hub, samples)
        worst = max(worst, maximum)
        spokes.append(
            {
                "rank": rank,
                "root_index": index,
                "distance": mp.nstr(distance, 15),
                "segment_max_abs_f": mp.nstr(maximum, 20),
                "ratio_to_critical_value": mp.nstr(maximum / critical_value, 15),
                "argmax_t": mp.nstr(at, 8),
                "leaves_lemniscate": bool(maximum > 1),
            }
        )

    tolerance = 1 + mpf(10) ** (-12)
    return {
        "degree": degree,
        "admissible_hub_count": len(admissible),
        "critical_value_T_star": mp.nstr(critical_value, 20),
        "max_root_modulus": mp.nstr(max(abs(root) for root in roots), 12),
        "two_nearest_distance_sum": mp.nstr(ordered[0][0] + ordered[1][0], 15),
        "spokes": spokes,
        "claim_3_refuted": bool(worst > critical_value * tolerance),
        "nearest_pair_broken_line_leaves_lemniscate": bool(worst > 1),
        "worst_spoke_max_abs_f": mp.nstr(worst, 20),
    }


def build_payload(digits: int, samples: int) -> dict[str, Any]:
    mp.dps = digits
    rows = [
        evaluate_witness(degree, literals, samples)
        for degree, literals in sorted(
            _witness_module.QC_REFUTATION_WITNESSES.items()
        )
    ]
    return {
        "schema": "erdos1041_first_merge_hub_claim_guard_v0",
        "boundary": (
            "exact stored witnesses evaluated at high precision; a falsifier for "
            "claim 3 of the first-merge-hub conditional theorem, not a proof of "
            "any positive statement about Erdos 1041"
        ),
        "claim_under_test": (
            "on each spoke [z_a, c*] the exact maximum of |f| is T* = |f(c*)|"
        ),
        "digits": digits,
        "segment_samples": samples,
        "witness_source": (
            "check_erdos1041_straight_spoke_hub_criterion.QC_REFUTATION_WITNESSES"
        ),
        "rows": rows,
        "claim_3_refuted_at_every_witness": all(row["claim_3_refuted"] for row in rows),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=DEFAULT_DIGITS)
    parser.add_argument("--samples", type=int, default=DEFAULT_SAMPLES)
    parser.add_argument("--json", action="store_true", help="emit the payload as JSON")
    args = parser.parse_args()

    payload = build_payload(args.digits, args.samples)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        for row in payload["rows"]:
            print(f"=== degree {row['degree']} ===")
            print(f"  admissible hubs      : {row['admissible_hub_count']}")
            print(f"  T* = |f(c*)|         : {row['critical_value_T_star']}")
            print(f"  max root modulus     : {row['max_root_modulus']}")
            print(f"  d1 + d2 at c*        : {row['two_nearest_distance_sum']}")
            for spoke in row["spokes"]:
                marker = "  <-- LEAVES {|f|<1}" if spoke["leaves_lemniscate"] else ""
                print(
                    f"  spoke #{spoke['rank']} -> root {spoke['root_index']}: "
                    f"max|f| = {spoke['segment_max_abs_f']} "
                    f"(ratio to T* {spoke['ratio_to_critical_value']}) "
                    f"at t = {spoke['argmax_t']}{marker}"
                )
            print(f"  claim 3              : {'REFUTED' if row['claim_3_refuted'] else 'holds'}")
            print()

    if not payload["claim_3_refuted_at_every_witness"]:
        print(
            "GUARD FAILED: a stored witness no longer refutes claim 3. Either the "
            "witnesses or this guard has drifted; do not treat claim 3 as revived "
            "without re-deriving the witnesses.",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
