#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Attach two independent evidence classes to the checked diagonal depth roster.

``scripts/build_checked_diagonal_depth_roster.py`` extracts, from Lean source,
the checked working depth at every distinct LCM-diagonal scale through
``t = 82``, together with the arithmetic admissibility floor

    L0(t) = least L >= 1 with 2^L > 2 * (2H + L + 2),      H = periodLcm t

so that ``checked working depth - L0`` is the excess.  That roster is the
source-backed authority and this script does not restate it.  Two questions it
cannot answer on its own are answered here.

**Is the checked depth the least depth?**  The roster marks a row exact only
when a Lean theorem excludes every smaller depth, which currently holds at five
scales.  Every other row carries an upper bound on the least-depth excess.  An
exhaustive integer search decides the question outright wherever the totients
are reachable: deterministic Miller-Rabin plus Brent's rho factor ``H + m`` and
``2H + m`` exactly, and the depth recurrence is walked from depth ``1``.  This
is a **computational** verification and is recorded as its own evidence class.
It is not kernel proof and must never be merged into the roster's Lean-proved
column.

**Is the diagonal special?**  The roster has no comparison population, so it
cannot say whether diagonal excess differs from a generic point of the same
size.  For each scale this script draws control points ``N = h`` uniformly from
``[H, 2H)``, which preserves magnitude while removing the lcm structure, and
computes their exact least depths.  Controls are matched *within* scale, so the
test permutes within scale and never across: the governing sample size is the
number of scales, not the number of control points.

The comparison is a difference test.  Failing to reject does not establish
equivalence, genericity, or any asymptotic law, and no practical margin was
prespecified.  Both additions are finite and calibration-only.  Erdos 249
remains open.

Usage:

    python3 scripts/join_diagonal_excess_evidence.py
    python3 scripts/join_diagonal_excess_evidence.py --write
    python3 scripts/join_diagonal_excess_evidence.py --check
"""

from __future__ import annotations

import argparse
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
ROSTER = ROOT / "docs" / "measurements" / "checked_diagonal_depth_roster.json"
OUTPUT = ROOT / "docs" / "measurements" / "diagonal_excess_evidence_join.json"

# Scales whose totients are reachable by exact factorisation in seconds.
REACHABLE_MAX_T = 49
# A magnitude-matched control is only meaningful when [H, 2H) is large enough to
# sample from. At t = 1 that interval holds exactly one integer, and it is the
# diagonal point itself, so the "control" is the diagonal and the contrast is
# zero by construction; t = 2 holds two integers and t = 3 holds six. Scales
# below this threshold are excluded from the comparison while still carrying
# their least-depth verification, which control diversity does not affect.
CONTROL_MIN_INTERVAL = 1000
# Ten controls per scale left the p-value swinging between realisations. Forty
# holds it inside a narrow band across seeds, so it is the default: --check
# recomputes the payload and would report a spurious staleness if it ran at a
# different control count from the one --write used.
DEFAULT_CONTROLS_PER_SCALE = 40
DEFAULT_SEED = 20260726
DEPTH_SEARCH_MARGIN = 40
PERMUTATION_DRAWS = 200_000

# The p-value from any single control draw is NOT stable, so the artifact
# records the spread rather than letting one realisation stand as the result.
# These are recorded observations, each from a full run at 40 controls per scale
# over the same 17 non-degenerate scales, differing only in seed. Reproduce any
# row with `--controls 40 --seed <seed>`. Recomputing all four inside the payload
# would quadruple a --check run for no additional evidence.
ESTIMATE_STABILITY = {
    "controls_per_scale": 40,
    "scales": 17,
    "realisations": [
        {"seed": 20260726, "contrast": "-0.5735", "two_sided_p": "0.151"},
        {"seed": 40, "contrast": "-0.4765", "two_sided_p": "0.258"},
        {"seed": 41, "contrast": "-0.4029", "two_sided_p": "0.263"},
        {"seed": 42, "contrast": "-0.4162", "two_sided_p": "0.278"},
    ],
    "contrast_range": ["-0.5735", "-0.4029"],
    "two_sided_p_range": ["0.151", "0.278"],
    "reading": (
        "Every realisation gives a negative contrast, meaning diagonal excess depth slightly below "
        "magnitude-matched controls, and none approaches significance at any conventional threshold. "
        "The p itself moves by nearly a factor of two across seeds, so the range is the result and a "
        "single realisation's p must not be quoted on its own."
    ),
}

_MILLER_RABIN_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin; exact for every n below 3.3 * 10 ** 24."""
    if n < 2:
        return False
    for base in _MILLER_RABIN_BASES:
        if n % base == 0:
            return n == base
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for base in _MILLER_RABIN_BASES:
        x = pow(base, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _brent_factor(n: int, rng: random.Random) -> int:
    """Brent's improvement on Pollard rho; returns a proper factor of composite n."""
    if n % 2 == 0:
        return 2
    while True:
        y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
        g = q = r = 1
        x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = gcd(abs(x - ys), n)
        if g != n:
            return g


def prime_factors(n: int, rng: random.Random) -> set[int]:
    factors: set[int] = set()
    for base in _MILLER_RABIN_BASES:
        if n % base == 0:
            factors.add(base)
            while n % base == 0:
                n //= base
    pending = [n] if n > 1 else []
    while pending:
        value = pending.pop()
        if value == 1:
            continue
        if is_prime(value):
            factors.add(value)
            continue
        divisor = _brent_factor(value, rng)
        pending.extend([divisor, value // divisor])
    return factors


def totient(n: int, rng: random.Random) -> int:
    if n <= 1:
        return max(n, 0)
    result = n
    for prime in prime_factors(n, rng):
        result -= result // prime
    return result


def omitted_tail_radius(N: int, h: int, L: int) -> int:
    """The radius used by the checked predicate, reproduced exactly."""
    return N + h + L + 2


def floor_depth(N: int, h: int) -> int:
    depth = 1
    while (1 << depth) <= 2 * omitted_tail_radius(N, h, depth):
        depth += 1
    return depth


def least_certifying_depth(N: int, h: int, rng: random.Random) -> int | None:
    """Exhaustive least ``L`` with ``certifiedKill h N L``, searched from depth 1.

    ``A(h,N,L+1) = 2 A(h,N,L) + phi(N+h+L+1) - phi(N+L+1)`` keeps the search to
    one totient pair per depth. Depths below the floor are accumulated but not
    tested, since the central arc there is empty.
    """
    start = floor_depth(N, h)
    discrepancy = 0
    for depth in range(1, start + DEPTH_SEARCH_MARGIN + 1):
        discrepancy = (
            2 * discrepancy + totient(N + h + depth, rng) - totient(N + depth, rng)
        )
        if depth < start:
            continue
        modulus = 1 << depth
        residue = discrepancy % modulus
        radius = omitted_tail_radius(N, h, depth)
        if radius < residue < modulus - radius:
            return depth
    return None


def exact_mean(values: list[int]) -> dict[str, int]:
    """Mean as a reduced numerator/denominator pair, so no float is recorded."""
    total, count = sum(values), len(values)
    divisor = gcd(total, count) or 1
    return {"numerator": total // divisor, "denominator": count // divisor}


def stratified_permutation_p(
    paired: list[tuple[int, list[int]]], rng: random.Random
) -> dict[str, object]:
    """Two-sided p for the mean within-scale contrast, permuting inside scales only.

    Pooling every diagonal and control excess into one bag and permuting
    globally would treat scales spanning tens of orders of magnitude as
    exchangeable and would inflate the effective sample size from the number of
    scales to the number of points.
    """

    def contrast(diag: int, controls: list[int]) -> float:
        return diag - sum(controls) / len(controls)

    observed = sum(contrast(d, c) for d, c in paired) / len(paired)
    hits = 0
    for _ in range(PERMUTATION_DRAWS):
        total = 0.0
        for diag, controls in paired:
            pool = [diag, *controls]
            picked = rng.randrange(len(pool))
            others = pool[:picked] + pool[picked + 1:]
            total += pool[picked] - sum(others) / len(others)
        if abs(total / len(paired)) >= abs(observed):
            hits += 1
    return {
        "statistic": "mean over scales of (diagonal excess - mean control excess)",
        "observed": f"{observed:.4f}",
        "two_sided_p": f"{hits / PERMUTATION_DRAWS:.3f}",
        "draws": PERMUTATION_DRAWS,
        "design": "permutation within scale only; scales are the governing sample size",
    }


def load_roster() -> dict[str, object]:
    if not ROSTER.exists():
        raise SystemExit(
            f"missing {ROSTER.relative_to(ROOT)}; run "
            "scripts/build_checked_diagonal_depth_roster.py --write first"
        )
    return json.loads(ROSTER.read_text(encoding="utf-8"))


def build_payload(controls_per_scale: int, seed: int) -> dict[str, object]:
    roster = load_roster()
    roster_bytes = ROSTER.read_bytes()
    rng = random.Random(seed)

    rows: list[dict[str, object]] = []
    paired: list[tuple[int, list[int]]] = []
    paired_all: list[tuple[int, list[int]]] = []
    degenerate: list[int] = []
    diagonal_excess: list[int] = []
    control_excess: list[int] = []
    agreements = comparisons = 0
    upgraded: list[int] = []

    for entry in roster["rows"]:
        t = int(entry["scale_index_t"])
        if t > REACHABLE_MAX_T:
            continue
        modulus = int(entry["period_lcm"])
        recorded_floor = int(entry["arithmetic_admissibility_floor"])
        checked = int(entry["checked_working_depth"])

        least = least_certifying_depth(modulus, modulus, rng)
        if least is None:
            rows.append({"scale_index_t": t, "status": "no_certificate_within_margin"})
            continue

        comparisons += 1
        agrees = least == checked
        agreements += int(agrees)
        if agrees and entry.get("proved_least_depth") is None:
            upgraded.append(t)
        diagonal_excess.append(least - recorded_floor)

        controls: list[int] = []
        for _ in range(controls_per_scale):
            sample = rng.randrange(modulus, 2 * modulus)
            found = least_certifying_depth(sample, sample, rng)
            if found is not None:
                controls.append(found - floor_depth(sample, sample))
        control_excess.extend(controls)
        if controls:
            paired_all.append((least - recorded_floor, controls))
            if modulus >= CONTROL_MIN_INTERVAL:
                paired.append((least - recorded_floor, controls))
            else:
                degenerate.append(t)

        rows.append(
            {
                "scale_index_t": t,
                "status": "success",
                "roster_arithmetic_admissibility_floor": recorded_floor,
                "roster_checked_working_depth": checked,
                "computationally_verified_least_depth": least,
                "computationally_verified_least_depth_excess": least - recorded_floor,
                "agrees_with_roster_checked_depth": agrees,
                "roster_had_lean_proved_least_depth": entry.get("proved_least_depth")
                is not None,
                "control_excess_depths": controls,
                "control_population_meaningful": modulus >= CONTROL_MIN_INTERVAL,
            }
        )

    return {
        "schema": "erdos249257-diagonal-excess-evidence-join/1",
        "artifact_role": "attached_independent_evidence_over_a_source_backed_roster",
        "generator": "scripts/join_diagonal_excess_evidence.py",
        "joined_roster": {
            "path": str(ROSTER.relative_to(ROOT)),
            "sha256": f"sha256:{sha256(roster_bytes).hexdigest()}",
            "authority": (
                "The roster is the source-backed authority for checked working depths and "
                "Lean-proved least depths. This artifact adds evidence classes and restates none."
            ),
        },
        "parameters": {
            "reachable_max_t": REACHABLE_MAX_T,
            "controls_per_scale": controls_per_scale,
            "control_min_interval": CONTROL_MIN_INTERVAL,
            "seed": seed,
            "control_construction": (
                "N = h drawn uniformly from [periodLcm t, 2 * periodLcm t), preserving magnitude "
                "while removing the lcm structure"
            ),
        },
        "rows": rows,
        "summary": {
            "scales_reached": comparisons,
            "roster_checked_depths_reproduced": agreements,
            "rows_upgraded_from_upper_bound_to_computationally_verified": sorted(upgraded),
            "all_reached_scales": {
                "diagonal_sample_size": len(diagonal_excess),
                "diagonal_mean_excess": exact_mean(diagonal_excess) if diagonal_excess else None,
                "note": "includes scales whose control interval is degenerate",
            },
            "matched_test_population": {
                "diagonal_sample_size": len(paired),
                "diagonal_mean_excess": (
                    exact_mean([d for d, _ in paired]) if paired else None
                ),
                "control_sample_size": sum(len(c) for _, c in paired),
                "control_mean_excess": (
                    exact_mean([x for _, c in paired for x in c]) if paired else None
                ),
                "note": "the population the reported p-value actually describes",
            },
            "matched_test": stratified_permutation_p(paired, rng) if paired else None,
            "matched_test_scales": len(paired),
            "scales_excluded_for_degenerate_control_interval": sorted(degenerate),
            "sensitivity_including_degenerate_scales": (
                stratified_permutation_p(paired_all, rng) if paired_all else None
            ),
            "estimate_stability": ESTIMATE_STABILITY,
        },
        "evidence_classes": {
            "computationally_verified_least_depth": (
                "An exhaustive integer search from depth 1 found no smaller certifying depth. This "
                "is not kernel proof and is deliberately kept in a separate column from the "
                "roster's lean_proved_least_depth."
            ),
            "matched_control_result": (
                "A magnitude-matched experimental comparison. Calibration only; it licenses no "
                "claim transition."
            ),
        },
        "limits": [
            "A difference test that fails to reject does not establish equivalence, genericity, or "
            "that the diagonal behaves like a random point. No practical margin was prespecified.",
            "Scales are the governing sample size. Additional control points sharpen each "
            "within-scale estimate but do not create additional independent diagonal comparisons.",
            "This payload's matched_test is ONE realisation. Across seeds at the same control count "
            "the p moves by nearly a factor of two, so quote summary.estimate_stability's range and "
            "never this single p. Three seeds happened to agree closely and a fourth did not; a "
            "narrow spread over a few draws is not evidence of a stable estimate.",
            "Scales whose control interval [H, 2H) holds fewer than the stated minimum integers are "
            "excluded from the comparison: at the smallest of them the only available control IS the "
            "diagonal point, so the contrast is zero by construction rather than by evidence. Their "
            "least-depth verification is unaffected and is retained.",
            "Computational verification of a least depth is not a Lean proof and must not be "
            "reported in the roster's Lean-proved column.",
            "Every result here is finite. Nothing bears on cofinal certificate supply, "
            "equidistribution, an asymptotic depth law, or irrationality. Erdos 249 remains OPEN.",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true", help="rewrite the joined artifact")
    parser.add_argument("--check", action="store_true", help="fail if the artifact is stale")
    parser.add_argument("--controls", type=int, default=DEFAULT_CONTROLS_PER_SCALE)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    args = parser.parse_args(argv)

    payload = build_payload(args.controls, args.seed)
    summary = payload["summary"]

    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0

    if args.check:
        if not OUTPUT.exists():
            print(f"missing {OUTPUT.relative_to(ROOT)}", file=sys.stderr)
            return 1
        if json.loads(OUTPUT.read_text(encoding="utf-8")) != payload:
            print(f"{OUTPUT.relative_to(ROOT)} is stale; rerun with --write", file=sys.stderr)
            return 1
        print(f"{OUTPUT.relative_to(ROOT)} reproduces exactly")
        return 0

    reached = summary["scales_reached"]
    reproduced = summary["roster_checked_depths_reproduced"]
    upgraded = summary["rows_upgraded_from_upper_bound_to_computationally_verified"]
    print(f"scales reached                     : {reached}")
    print(f"roster checked depths reproduced   : {reproduced}/{reached}")
    print(f"upper-bound rows now verified      : {len(upgraded)} {upgraded}")
    test = summary["matched_test"]
    if test:
        print(f"matched test on {summary['matched_test_scales']} scales: "
              f"contrast {test['observed']}, two-sided p = {test['two_sided_p']}")
    excluded = summary["scales_excluded_for_degenerate_control_interval"]
    if excluded:
        print(f"excluded, degenerate control interval : {excluded}")
    sens = summary["sensitivity_including_degenerate_scales"]
    if sens:
        print(f"sensitivity incl. degenerate scales   : p = {sens['two_sided_p']}")
    if reproduced != reached:
        print("a roster checked depth was NOT reproduced", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
