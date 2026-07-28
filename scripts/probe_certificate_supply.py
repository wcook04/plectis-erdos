#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Measure finite #249 endpoint certificates on a fixed, reproducible grid.

For

    R_N = sum_{m >= 1} phi(N + m) / 2^m

the depth-``L`` window discrepancy is the integer

    A(h,N,L) = sum_{m=1}^L
        (phi(N + h + m) - phi(N + m)) * 2^(L-m).

The omitted part of ``R_(N+h) - R_N`` is the difference of two nonnegative
tails.  From ``phi(k) <= k``, the individual scaled tails obey

    0 <= 2^L T(M,L) <= M + L + 2.

Consequently

    -(N + L + 2) <= 2^L (T(N+h,L) - T(N,L))
                    <= N + h + L + 2,

so its absolute value is at most the *larger* one-sided radius
``N + h + L + 2``.  Adding the two tail bounds would also be sound, but would
not reproduce the sharper checked predicate
``TotientTailPeriodKiller.certifiedKill``.

A certificate fires exactly when ``A mod 2^L`` lies strictly between that
radius and its reflection about ``2^L``.  The central interval cannot contain
any residue before the least depth satisfying

    2^L > 2 * (N + h + L + 2).

That arithmetic admissibility floor necessarily grows with the scale
``N+h``.  The measurement therefore records both the raw first-certificate
depth and its excess above this floor.  All arithmetic in this script is
integer arithmetic.  The measurement is finite evidence only: it makes no
asymptotic, equidistribution, or cofinal inference.  In addition to the
rectangular grid, it samples the exact LCM-diagonal pairs

    (N,h) = (lcm(1,...,t), lcm(1,...,t))

for a declared finite range of ``t``.  Every ``t`` remains visible even when
the LCM repeats, so the artifact distinguishes tested indices from distinct
scales.

Usage:

    python3 scripts/probe_certificate_supply.py
    python3 scripts/probe_certificate_supply.py --write
    python3 scripts/probe_certificate_supply.py --check
"""

from __future__ import annotations

import argparse
import json
from math import gcd, lcm
from pathlib import Path
import sys
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs" / "measurements" / "certificate_supply_probe.json"

DEFAULT_N_MIN = 1
DEFAULT_N_MAX = 120
DEFAULT_H_MIN = 1
DEFAULT_H_MAX = 8
DEFAULT_MAX_DEPTH = 400
DEFAULT_SPOT_N = (200, 500, 1000, 2000, 5000)
DEFAULT_DIAGONAL_T_MAX = 16


def totient_sieve(limit: int) -> list[int]:
    """Return ``phi(0), ..., phi(limit)`` using exact integer updates."""
    if limit < 0:
        raise ValueError("totient sieve limit must be nonnegative")
    phi = list(range(limit + 1))
    for prime in range(2, limit + 1):
        if phi[prime] != prime:
            continue
        for multiple in range(prime, limit + 1, prime):
            phi[multiple] -= phi[multiple] // prime
    return phi


def omitted_tail_radius(N: int, h: int, L: int) -> int:
    """Sharp symmetric integer radius used by the checked certificate.

    After multiplication by ``2^L``, the two nonnegative omitted tails have
    upper bounds ``N+h+L+2`` and ``N+L+2``.  Since ``h >= 0``, their difference
    has absolute value at most the first quantity.
    """
    if min(N, h, L) < 0:
        raise ValueError("N, h, and L must be nonnegative")
    return N + h + L + 2


def admissible_depth_floor(N: int, h: int) -> int:
    """Least positive depth at which the central interval is nonempty.

    Since both ``2^L`` and twice the radius are even, the strict inequality
    also guarantees room for an integer residue strictly between the two
    endpoints.
    """
    if N < 0 or h < 0:
        raise ValueError("N and h must be nonnegative")
    depth = 1
    while (1 << depth) <= 2 * omitted_tail_radius(N, h, depth):
        depth += 1
    return depth


def direct_window_discrepancy(
    phi: list[int], N: int, h: int, L: int
) -> int:
    """Compute ``A(h,N,L)`` directly; useful as an independent test oracle."""
    if N + h + L >= len(phi):
        raise ValueError("totient table is too short")
    return sum(
        (phi[N + h + m] - phi[N + m]) << (L - m)
        for m in range(1, L + 1)
    )


def certificate_at_depth(
    discrepancy: int, N: int, h: int, L: int
) -> dict[str, int | bool]:
    """Evaluate the exact central-arc certificate at one depth."""
    modulus = 1 << L
    residue = discrepancy % modulus
    radius = omitted_tail_radius(N, h, L)
    return {
        "depth": L,
        "discrepancy": discrepancy,
        "modulus": modulus,
        "residue": residue,
        "omitted_tail_radius": radius,
        "certified": radius < residue < modulus - radius,
    }


def minimum_certificate(
    phi: list[int], N: int, h: int, max_depth: int
) -> dict[str, int | bool] | None:
    """Return the first certificate for ``1 <= L <= max_depth``, if any.

    The recurrence

        A(h,N,L+1) = 2 A(h,N,L) + phi(N+h+L+1) - phi(N+L+1)

    computes the same integer as the defining sum without rebuilding every
    prefix.  Iterating depths in increasing order makes a success the exact
    minimum inside the declared search range.
    """
    if N < 0 or h < 0 or max_depth < 1:
        raise ValueError("require N >= 0, h >= 0, and max_depth >= 1")
    if N + h + max_depth >= len(phi):
        raise ValueError("totient table is too short")

    discrepancy = 0
    for depth in range(1, max_depth + 1):
        discrepancy = (
            2 * discrepancy
            + phi[N + h + depth]
            - phi[N + depth]
        )
        certificate = certificate_at_depth(discrepancy, N, h, depth)
        if certificate["certified"]:
            return certificate
    return None


def reduced_rational(numerator: int, denominator: int) -> dict[str, int]:
    """Return an exact rational as a reduced numerator/denominator pair."""
    if denominator <= 0:
        raise ValueError("rational denominator must be positive")
    divisor = gcd(abs(numerator), denominator)
    return {
        "numerator": numerator // divisor,
        "denominator": denominator // divisor,
    }


def exact_median(values: Iterable[int]) -> dict[str, int]:
    """Return the exact median as a reduced numerator/denominator pair."""
    ordered = sorted(values)
    if not ordered:
        raise ValueError("median of empty data")
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return {"numerator": ordered[middle], "denominator": 1}
    return reduced_rational(ordered[middle - 1] + ordered[middle], 2)


def excess_depth_summary(values: Iterable[int]) -> dict[str, object]:
    """Return exact finite summary statistics and a rational distribution."""
    ordered = sorted(values)
    if not ordered:
        return {
            "sample_size": 0,
            "minimum": None,
            "median": None,
            "mean": None,
            "maximum": None,
            "distribution": [],
        }
    if ordered[0] < 0:
        raise ValueError("excess depths must be nonnegative")

    counts: dict[int, int] = {}
    for value in ordered:
        counts[value] = counts.get(value, 0) + 1
    sample_size = len(ordered)
    return {
        "sample_size": sample_size,
        "minimum": ordered[0],
        "median": exact_median(ordered),
        "mean": reduced_rational(sum(ordered), sample_size),
        "maximum": ordered[-1],
        "distribution": [
            {
                "excess_depth": value,
                "count": count,
                "proportion": reduced_rational(count, sample_size),
            }
            for value, count in counts.items()
        ],
    }


def lcm_prefix_scales(t_max: int) -> list[int]:
    """Return ``lcm(1,...,t)`` for every ``1 <= t <= t_max``.

    Repeated values are intentionally retained: ``t`` is the sampled index,
    whereas the LCM is the corresponding scale.
    """
    if t_max < 1:
        raise ValueError("diagonal t maximum must be positive")
    scale = 1
    scales = []
    for t in range(1, t_max + 1):
        scale = lcm(scale, t)
        scales.append(scale)
    return scales


def result_row(
    phi: list[int], N: int, h: int, max_depth: int
) -> dict[str, object]:
    """Build one complete success/failure row."""
    depth_floor = admissible_depth_floor(N, h)
    certificate = minimum_certificate(phi, N, h, max_depth)
    if certificate is None:
        return {
            "N": N,
            "h": h,
            "status": "failure_within_search_range",
            "searched_depths": {"minimum": 1, "maximum": max_depth},
            "admissible_depth_floor": depth_floor,
            "excess_depth": None,
            "minimum_certificate": None,
        }
    excess_depth = int(certificate["depth"]) - depth_floor
    if excess_depth < 0:
        raise AssertionError(
            "a certificate cannot precede the nonempty-interval depth floor"
        )
    return {
        "N": N,
        "h": h,
        "status": "success",
        "searched_depths": {"minimum": 1, "maximum": max_depth},
        "admissible_depth_floor": depth_floor,
        "excess_depth": excess_depth,
        "minimum_certificate": certificate,
    }


def lcm_diagonal_rows(
    phi: list[int], t_max: int, max_depth: int
) -> list[dict[str, object]]:
    """Measure every indexed LCM-diagonal pair through ``t_max``.

    ``first_occurrence_t`` makes sequence repetitions explicit.  A repeated
    scale is still emitted as its own ``t`` row, while ``is_new_scale`` lets
    consumers count distinct measured pairs without heuristic deduplication.
    """
    first_t_by_scale: dict[int, int] = {}
    rows = []
    for t, scale in enumerate(lcm_prefix_scales(t_max), start=1):
        first_t = first_t_by_scale.setdefault(scale, t)
        rows.append(
            {
                "t": t,
                "lcm_1_to_t": scale,
                "is_new_scale": first_t == t,
                "first_occurrence_t": first_t,
                **result_row(phi, scale, scale, max_depth),
            }
        )
    return rows


def build_measurement(
    *,
    n_min: int = DEFAULT_N_MIN,
    n_max: int = DEFAULT_N_MAX,
    h_min: int = DEFAULT_H_MIN,
    h_max: int = DEFAULT_H_MAX,
    max_depth: int = DEFAULT_MAX_DEPTH,
    spot_n: tuple[int, ...] = DEFAULT_SPOT_N,
    diagonal_t_max: int = DEFAULT_DIAGONAL_T_MAX,
) -> dict[str, object]:
    """Recompute the complete deterministic measurement."""
    if n_min < 0 or n_max < n_min:
        raise ValueError("require 0 <= n_min <= n_max")
    if h_min < 0 or h_max < h_min:
        raise ValueError("require 0 <= h_min <= h_max")
    if max_depth < 1:
        raise ValueError("max_depth must be positive")
    if any(N < 0 for N in spot_n):
        raise ValueError("spot-probe N values must be nonnegative")

    diagonal_scales = lcm_prefix_scales(diagonal_t_max)
    maximum_endpoint = max(
        n_max + h_max,
        *(N + 1 for N in spot_n),
        *(2 * scale for scale in diagonal_scales),
    )
    phi_limit = maximum_endpoint + max_depth
    phi = totient_sieve(phi_limit)

    pairs = [
        result_row(phi, N, h, max_depth)
        for h in range(h_min, h_max + 1)
        for N in range(n_min, n_max + 1)
    ]

    per_h = []
    for h in range(h_min, h_max + 1):
        h_rows = [row for row in pairs if row["h"] == h]
        successes = [row for row in h_rows if row["status"] == "success"]
        failures = [
            int(row["N"]) for row in h_rows
            if row["status"] == "failure_within_search_range"
        ]
        depths = [
            int(row["minimum_certificate"]["depth"])  # type: ignore[index]
            for row in successes
        ]
        per_h.append(
            {
                "h": h,
                "tested": len(h_rows),
                "successes": len(successes),
                "failures": len(failures),
                "failure_N": failures,
                "minimum_depth": min(depths) if depths else None,
                "median_depth": exact_median(depths) if depths else None,
                "maximum_depth": max(depths) if depths else None,
            }
        )

    spot_rows = [result_row(phi, N, 1, max_depth) for N in spot_n]
    diagonal_rows = lcm_diagonal_rows(phi, diagonal_t_max, max_depth)
    rectangle_successes = [
        row for row in pairs if row["status"] == "success"
    ]
    success_count = len(rectangle_successes)
    failure_pairs = [
        {"N": row["N"], "h": row["h"]}
        for row in pairs
        if row["status"] == "failure_within_search_range"
    ]
    distinct_diagonal_rows = [
        row for row in diagonal_rows if row["is_new_scale"]
    ]
    diagonal_successes = [
        row for row in diagonal_rows if row["status"] == "success"
    ]
    diagonal_failures = [
        row for row in diagonal_rows
        if row["status"] == "failure_within_search_range"
    ]
    distinct_diagonal_failures = [
        row for row in distinct_diagonal_rows
        if row["status"] == "failure_within_search_range"
    ]
    distinct_diagonal_successes = [
        row for row in distinct_diagonal_rows if row["status"] == "success"
    ]
    rectangle_excess_depths = [
        int(row["excess_depth"]) for row in rectangle_successes
    ]
    diagonal_depths = [
        int(row["minimum_certificate"]["depth"])  # type: ignore[index]
        for row in diagonal_successes
    ]
    diagonal_excess_depths = [
        int(row["excess_depth"]) for row in diagonal_successes
    ]
    distinct_diagonal_excess_depths = [
        int(row["excess_depth"]) for row in distinct_diagonal_successes
    ]

    return {
        "schema": "erdos249257-certificate-supply-probe/3",
        "artifact_role": "generated_finite_measurement",
        "generator": "scripts/probe_certificate_supply.py",
        "question": (
            "How often does the exact finite endpoint certificate fire on the "
            "declared rectangular grid and exact finite LCM diagonal, and how "
            "far above arithmetic admissibility is its first success?"
        ),
        "mathematical_object": {
            "tail": "R_N = sum_{m>=1} phi(N+m)/2^m",
            "difference": "D_(N,h) = R_(N+h) - R_N",
            "window_discrepancy": (
                "A(h,N,L) = sum_{m=1}^L "
                "(phi(N+h+m)-phi(N+m))*2^(L-m)"
            ),
            "omitted_tail_bound": {
                "scaled_radius": "N+h+L+2",
                "derivation": (
                    "Each omitted tail is nonnegative; after scaling by 2^L, "
                    "T(N+h,L) <= N+h+L+2 and T(N,L) <= N+L+2. "
                    "Their difference is therefore bounded in absolute value "
                    "by the larger first quantity, not by their sum."
                ),
            },
            "certificate": (
                "N+h+L+2 < A(h,N,L) mod 2^L "
                "< 2^L-(N+h+L+2)"
            ),
            "admissible_depth_floor": (
                "min {L>=1 : 2^L > 2*(N+h+L+2)}"
            ),
            "excess_depth": (
                "minimum_certificate.depth - admissible_depth_floor"
            ),
        },
        "parameters": {
            "grid": {
                "N": {"minimum": n_min, "maximum": n_max},
                "h": {"minimum": h_min, "maximum": h_max},
            },
            "searched_depths": {"minimum": 1, "maximum": max_depth},
            "spot_probes": {"h": 1, "N": list(spot_n)},
            "lcm_diagonal": {
                "t": {"minimum": 1, "maximum": diagonal_t_max},
                "pair": "N=h=lcm(1,...,t)",
                "duplicate_policy": (
                    "Retain every t; mark whether its scale is new and record "
                    "the first t at which each repeated scale occurred."
                ),
            },
            "totient_sieve_limit": phi_limit,
        },
        "summary": {
            "tested_pairs": len(pairs),
            "successes": success_count,
            "failures": len(failure_pairs),
            "failure_pairs": failure_pairs,
            "per_h": per_h,
            "excess_depth": excess_depth_summary(rectangle_excess_depths),
        },
        "spot_probes": spot_rows,
        "lcm_diagonal": {
            "summary": {
                "tested_t": len(diagonal_rows),
                "distinct_scales": len(distinct_diagonal_rows),
                "repeated_t": [
                    row["t"] for row in diagonal_rows
                    if not row["is_new_scale"]
                ],
                "success_rows": len(diagonal_successes),
                "failure_rows": len(diagonal_failures),
                "failure_t": [row["t"] for row in diagonal_failures],
                "distinct_scale_failures": len(distinct_diagonal_failures),
                "failure_scales": [
                    row["lcm_1_to_t"] for row in distinct_diagonal_failures
                ],
                "minimum_depth": (
                    min(diagonal_depths) if diagonal_depths else None
                ),
                "maximum_depth": (
                    max(diagonal_depths) if diagonal_depths else None
                ),
                "excess_depth_indexed_t": excess_depth_summary(
                    diagonal_excess_depths
                ),
                "excess_depth_distinct_scales": excess_depth_summary(
                    distinct_diagonal_excess_depths
                ),
            },
            "rows": diagonal_rows,
        },
        "pairs": pairs,
        "limits": [
            (
                "This is a finite exact-arithmetic measurement, not a proof of "
                "an asymptotic statement or of cofinal certificate supply."
            ),
            (
                "Success on N=1..120 and h=1..8 does not imply success beyond "
                "every cutoff, for every positive h, or at any untested pair."
            ),
            (
                f"The exact LCM-diagonal sample stops at t={diagonal_t_max}. "
                f"It retains {len(diagonal_rows)} indexed rows representing "
                f"{len(distinct_diagonal_rows)} distinct scales; repeated "
                "LCM values do not constitute new measured pairs."
            ),
            (
                "Finite success on the sampled LCM diagonal does not imply a "
                "certificate at any larger t, certificates beyond every "
                "cutoff, or any other asymptotic/cofinal conclusion."
            ),
            (
                "Raw certificate depth necessarily grows with N+h because "
                "the central interval is empty below the recorded arithmetic "
                "admissibility floor. Excess depth is the scale-adjusted "
                "finite statistic reported here."
            ),
            (
                "The finite excess-depth distributions do not establish an "
                "asymptotic law, residue equidistribution, bounded excess at "
                "untested scales, or cofinal certificate supply."
            ),
            (
                "A failure means only that no certificate fired for "
                f"1<=L<={max_depth}; it does not imply that the tail difference "
                "is integral."
            ),
            (
                "A success proves only the corresponding local tail difference "
                "is non-integral; any finite collection leaves Erdos #249 OPEN."
            ),
        ],
    }


def render_measurement(data: dict[str, object]) -> str:
    """Canonical JSON rendering used by stdout, ``--write``, and ``--check``."""
    return json.dumps(data, ensure_ascii=False, indent=1, sort_keys=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write", action="store_true",
        help=f"write the default measurement to {OUTPUT.relative_to(ROOT)}",
    )
    mode.add_argument(
        "--check", action="store_true",
        help="fail if the generated default measurement is absent or stale",
    )
    args = parser.parse_args()

    data = build_measurement()
    rendered = render_measurement(data)
    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(rendered, encoding="utf-8")
        print(
            "probe_certificate_supply: wrote "
            f"{OUTPUT.relative_to(ROOT)}"
        )
        return 0
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != rendered:
            print(
                "probe_certificate_supply: generated measurement is stale",
                file=sys.stderr,
            )
            return 1
        print("probe_certificate_supply: current")
        return 0

    sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
