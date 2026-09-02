#!/usr/bin/env python3
"""What do the canonical factorial digits of the Erdos #68 series actually do?

Upstream analytic state
-----------------------
Three of the packet's families were tracked as separate obstructions:

* `cofinal_exact_prefix_strict_successor_miss` -- Lean proves `Irrational S` is
  *exactly* cofinally many `m` with `m` not dividing `N_m`, i.e. cofinally many
  non-unit carries;
* `cofinal_tailfree_predecessor_gap_threshold` -- a pure integer inequality
  whose cofinal supply is sufficient for irrationality;
* the canonical-digit machinery of `CanonicalFactorialDigits.lean` and
  `FactorialZeroPlateau.lean`, where `S` is rational exactly when the canonical
  factorial digits `d_m(S)` are eventually zero.

The GMP certificate settled one predicate of the first family -- the nine unit
carries below 300000 -- and discarded the digits that produced it.  The
exact-Fraction probe settled the second to `m = 210`.  Nobody had computed
`d_m(S)`.

Probe
-----
Take the digit `D_m = m N_(m-1) - N_m` from the certificate stream and read all
three families off it.  Writing `A_m = N_m - m! P_m` in `(0,1]` for the scaled
predecessor gap, `G_m = N_m/m! - S`, and `f_m = 1` when `G_m > 0` and `0`
otherwise (`f_m` is Lean's `factorialGapEndpointFlag`), the arithmetic is

    A_m = m A_(m-1) - 1 - 1/(m!-1) - D_m
    G_m = sum_(j>m) D_j / j!                    so  f_m is the sign of the
                                                first nonzero digit past m
    d_m(S) = m f_(m-1) - f_m - D_m .

`f_m` is therefore computable from the same stream by one backward scan, and so
is `d_m(S)`.  The tail-free threshold at `m` reads `m A_(m-1) >= 1 + 1/(m!-1) +
2/m`, and substituting the recurrence turns it into `D_m + A_m >= 2/m`: it
fails outright when `D_m = -1`, holds outright when `D_m >= 1`, and at `D_m = 0`
reduces to `A_m >= 2/m`, decided by `D_(m+1)` because
`A_m > (D_(m+1)+1)/(m+1)`.

Predeclared falsifier
---------------------
The null model is a generic real: `(D_m+1)/m` uniform on `[0,1)` and
independent across `m`, giving `sum 1/m ~ log M` occurrences of each of
`D_m = -1`, `D_m = 0`, `D_m = m-2`.  The probe reports Kolmogorov-Smirnov
against that null, the first two moments, the lag-one correlation, and the mean
stratified by primality, parity and small residue classes.

* Any stratum at `|z| > 4`, or `sqrt(n) * KS > 1.95`, falsifies the null.  Then
  the digits carry an arithmetic bias, a *construction* route is live, and the
  prime-indexed producers have a lever.
* Uniformity across every stratum eliminates the construction route: the three
  families are level sets of one scalar with no exploitable arithmetic, and the
  only surviving analytic input is non-concentration for `A_m` at scale `1/m`.

Also asserted, as an internal consistency check rather than a statistic: every
reconstructed `d_m(S)` must lie in `[0, m-1]`.  That is a nontrivial constraint
on roughly 50000 independent reconstructions and would fail loudly if the flag
rule or the digit identity were wrong.

Claim boundary
--------------
Finite computation.  It fixes the finite arithmetic of `S` in a stated range and
routes attention; it does not settle any cofinal quantifier.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Sequence

from formal_math.probes import erdos68_engine as engine

FIRST_M = 3


def _sieve(limit: int) -> bytearray:
    flags = bytearray([1]) * (limit + 1)
    flags[0] = flags[1] = 0
    for value in range(2, int(limit**0.5) + 1):
        if flags[value]:
            flags[value * value :: value] = bytearray(
                len(flags[value * value :: value])
            )
    return flags


def _z_of_mean(sample: Sequence[float]) -> tuple[int, float, float]:
    """Mean of a putative uniform sample and its z-score against mean 1/2."""
    count = len(sample)
    if count == 0:
        return 0, float("nan"), float("nan")
    mean = sum(sample) / count
    return count, mean, (mean - 0.5) / math.sqrt(1.0 / 12.0 / count)


def endpoint_flags(digits: list[int]) -> dict[int, int]:
    """`f_m = 1` exactly when `G_m = sum_(j>m) D_j/j! > 0`.

    One backward scan: the sign of `G_m` is the sign of the first nonzero digit
    past `m`, because `|sum_(j>k) D_j k!/j!| < 1` for every `k` while a single
    nonzero digit at `k+1` contributes at least `1/(k+1)` in absolute value.
    """
    last = FIRST_M + len(digits) - 1
    flags: dict[int, int] = {}
    positive = 0  # all-zero tail past the end of the stream: G = 0, flag 0
    for m in range(last - 1, FIRST_M - 1, -1):
        nxt = digits[m + 1 - FIRST_M]
        positive = 1 if (nxt > 0 or (nxt == 0 and positive == 1)) else 0
        flags[m] = positive
    return flags


def run(max_m: int = 50000, *, guard_bits: int = 96,
        verify_m: int = 200, cache: str | None = None) -> dict:
    cache_path = Path(cache) if cache else None
    backend_check = engine.verify_backends(verify_m)
    digits, meta = engine.stream_digits(
        max_m, guard_bits=guard_bits, cache_path=cache_path
    )
    flags = endpoint_flags(digits)
    primes = _sieve(max_m)

    normalized = {}
    for offset, digit in enumerate(digits):
        m = FIRST_M + offset
        normalized[m] = (digit + 1) / m

    zero_carry = engine.unit_carry_indices(digits)
    threshold_fail = engine.threshold_failure_indices(digits)
    maximal_digit = [
        FIRST_M + i for i, d in enumerate(digits) if d == FIRST_M + i - 2
    ]

    # Canonical factorial digits of S, reconstructed from the same stream.
    canonical: dict[int, int] = {}
    range_violations = []
    for m in range(FIRST_M + 1, FIRST_M + len(digits) - 1):
        if m - 1 not in flags or m not in flags:
            continue
        value = m * flags[m - 1] - flags[m] - digits[m - FIRST_M]
        canonical[m] = value
        if not 0 <= value <= m - 1:
            range_violations.append({"m": m, "digit": value})
    canonical_zero = sorted(m for m, d in canonical.items() if d == 0)
    canonical_max = sorted(m for m, d in canonical.items() if d == m - 1)

    # The threshold at a unit carry reduces to A_m >= 2/m, and
    # A_m > (D_(m+1)+1)/(m+1).  Record the decisive margin at each one.
    unit_carry_threshold = []
    for m in zero_carry:
        if m - FIRST_M + 1 >= len(digits):
            continue
        succ = digits[m - FIRST_M + 1]
        unit_carry_threshold.append({
            "m": m,
            "next_digit": succ,
            "gap_lower_bound": (succ + 1) / (m + 1),
            "threshold": 2 / m,
            "fires": (succ + 1) / (m + 1) >= 2 / m,
        })

    values = [normalized[m] for m in sorted(normalized)]
    count, mean, mean_z = _z_of_mean(values)
    variance = sum((v - mean) ** 2 for v in values) / count
    ordered = sorted(values)
    ks = max(
        max(abs((i + 1) / count - v), abs(i / count - v))
        for i, v in enumerate(ordered)
    )

    keys = sorted(normalized)
    left = [normalized[m] for m in keys[:-1]]
    right = [normalized[m] for m in keys[1:]]
    pair_n = len(left)
    mean_left = sum(left) / pair_n
    mean_right = sum(right) / pair_n
    covariance = sum(
        (a - mean_left) * (b - mean_right) for a, b in zip(left, right)
    ) / pair_n
    sd_left = math.sqrt(sum((a - mean_left) ** 2 for a in left) / pair_n)
    sd_right = math.sqrt(sum((b - mean_right) ** 2 for b in right) / pair_n)
    lag_one = covariance / (sd_left * sd_right)

    strata = {}
    for label, selector in (
        ("prime_index", lambda m: bool(primes[m])),
        ("composite_index", lambda m: not primes[m]),
        ("even_index", lambda m: m % 2 == 0),
        ("odd_index", lambda m: m % 2 == 1),
    ):
        sample = [normalized[m] for m in normalized if selector(m)]
        n, mu, z = _z_of_mean(sample)
        strata[label] = {"count": n, "mean": mu, "z": z}
    for modulus in (5, 6):
        for residue in range(modulus):
            sample = [normalized[m] for m in normalized if m % modulus == residue]
            n, mu, z = _z_of_mean(sample)
            strata[f"index_mod_{modulus}_eq_{residue}"] = {
                "count": n, "mean": mu, "z": z,
            }

    expected_rare = sum(1.0 / m for m in range(FIRST_M, max_m + 1))
    worst = max(abs(v["z"]) for v in strata.values())
    null_survives = worst <= 4.0 and ks * math.sqrt(count) <= 1.95

    return {
        "backend_check": backend_check,
        "stream": {
            "max_m": max_m,
            "digit_count": count,
            "gmp_version": meta.get("gmp_version"),
            "precision_bits": meta.get("precision_bits"),
            "guard_bits": guard_bits,
            "digit_min": min(digits),
            "digit_max": max(digits),
        },
        "rare_families": {
            "expected_each_under_null": expected_rare,
            "threshold_failure_D_eq_minus_one": threshold_fail,
            "unit_carry_D_eq_zero": zero_carry,
            "top_digit_D_eq_m_minus_two": maximal_digit,
            "families_are_disjoint": not (
                set(threshold_fail) & set(zero_carry)
            ),
        },
        "canonical_digits": {
            "reconstructed": len(canonical),
            "range_violations": range_violations,
            "zero_digit_indices": canonical_zero,
            "maximal_digit_indices": canonical_max,
            "zero_set_equals_threshold_failure_set":
                canonical_zero == sorted(
                    m for m in threshold_fail if m in canonical),
            "maximal_set_equals_unit_carry_set":
                canonical_max == sorted(m for m in zero_carry if m in canonical),
            "unit_carry_threshold_margins": unit_carry_threshold,
            "all_unit_carries_fire_threshold": all(
                row["fires"] for row in unit_carry_threshold
            ),
        },
        "null_model": {
            "statistic": "(D_m + 1) / m against Uniform[0,1)",
            "mean": mean,
            "mean_z": mean_z,
            "variance": variance,
            "variance_expected": 1 / 12,
            "ks": ks,
            "ks_times_sqrt_n": ks * math.sqrt(count),
            "ks_critical_0p1_percent": 1.95,
            "lag_one_correlation": lag_one,
            "lag_one_sd_under_independence": 1 / math.sqrt(pair_n),
            "strata": strata,
            "worst_abs_z": worst,
            "null_survives": null_survives,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=50000)
    parser.add_argument("--guard-bits", type=int, default=96)
    parser.add_argument("--cache", default=None)
    args = parser.parse_args()
    print(json.dumps(run(args.max_m, guard_bits=args.guard_bits,
                         cache=args.cache), indent=2, default=str))
    return 0


if __name__ == "__main__":
    import sys

    REPO_ROOT = Path(__file__).resolve().parents[2]
    if str(REPO_ROOT) not in sys.path:
        sys.path.insert(0, str(REPO_ROOT))
    raise SystemExit(main())
