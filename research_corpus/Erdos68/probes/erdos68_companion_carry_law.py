#!/usr/bin/env python3
"""Falsify the exact companion-constant carry law for Erdős #68.

Let ``C = sum_(n>=2) 1/(n!(n!-1))`` be the fixed companion constant, let
``d_m(C) = floor(m! C) - m floor((m-1)! C)`` be its canonical factorial digit,
let ``delta_m = m! sum_(n>m) 1/(n!(n!-1))`` be the scaled omitted tail, and let
``sigma_m = [fract(m! C) < delta_m]`` be the near-integer wrap indicator.  The
claimed exact identity, for every ``m >= 3``, is

    b_m = (m - 1 - d_m(C)) + sigma_m - m sigma_(m-1),

where ``b_m`` is the strict-successor carry ``Z_m = m Z_(m-1) + 1 - b_m``.
Consequences checked here as well:

    b_m = 1  ->  d_m(C) in {m-2, m-1},
    b_m = 0  ->  d_m(C) in {m-1, 0}.

The same generic boundary applies to Erdős's whole family
``S_t = sum_(n>=2) 1/(n!+t)``: with ``C_t = sum 1/(n!(n!+t))`` one has
``S_t = (e-2) - t C_t``, so ``S_t`` is rational iff
``ceil(t m! C_t) == 2 (mod m)`` for all large ``m``.  The probe records, for
small ``t``, the indices where that residue is hit, as finite evidence only.

Exact rational arithmetic is used for the carries; the companion constants are
evaluated in ``mpmath`` at two precisions and every floor must agree.  Nothing
here is proof authority: the Lean module ``CompanionConstantCarryLaw.lean``
owns the identity, and no cofinal statement is claimed.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "formal_math" / "probes"))

from erdos68_engine import exact_digits  # noqa: E402

problem_id = "erdos_68"
probe_id = "erdos68_companion_carry_law"

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def decimal_digits_of_factorial(n: int) -> int:
    return 1 if n < 2 else math.floor(math.lgamma(n + 1) / math.log(10)) + 1


def companion_constant(t: int, truncation: int) -> mp.mpf:
    factorial = mp.mpf(1)
    terms = []
    for n in range(1, truncation + 1):
        factorial *= n
        if n >= 2:
            terms.append(1 / (factorial * (factorial + t)))
    return mp.fsum(terms)


def carry_law_census(max_m: int, dps: int) -> dict:
    truncation = max_m + 60
    with mp.workdps(dps):
        C = companion_constant(-1, truncation)
        # exact carries b_m = D_m + 1 for m >= 3
        carries = {m: d + 1 for m, d, _ in exact_digits(max_m)}
        facs = {0: mp.mpf(1)}
        f = mp.mpf(1)
        for m in range(1, max_m + 2):
            f *= m
            facs[m] = f
        floors = {m: int(mp.floor(facs[m] * C)) for m in range(0, max_m + 1)}
        fracts = {m: facs[m] * C - floors[m] for m in range(0, max_m + 1)}
        # delta_m = m! * sum_{n>m} 1/(n!(n!-1)); use truncation tail
        deltas = {}
        for m in range(2, max_m + 1):
            fm = facs[m]
            acc = mp.mpf(0)
            g = fm
            for n in range(m + 1, truncation + 1):
                g *= n
                acc += fm / (g * (g - 1))
            deltas[m] = acc
        # sigma_m = [floor(F_m) = floor(m! C) - 1] with F_m = m! C_m exact.
        # (At m = 2 the carrier F_2 = 1 is an integer, so fract(2C) = delta_2
        # exactly and the strict inequality fract < delta fails; the exact
        # floor comparison is the robust form of the same indicator.)
        sigma = {}
        exact_fac = 1
        exact_partial = Fraction(0)
        for m in range(1, max_m + 1):
            exact_fac *= m
            if m >= 2:
                exact_partial += Fraction(1, exact_fac * (exact_fac - 1))
                F_m = exact_fac * exact_partial
                sigma[m] = int(math.floor(F_m) != floors[m])
                if math.floor(F_m) not in (floors[m], floors[m] - 1):
                    raise AssertionError(f"floor(F_m) outside two-floor window at m={m}")
        digits = {m: floors[m] - m * floors[m - 1] for m in range(3, max_m + 1)}
        violations = []
        unit_digit_violations = []
        zero_digit_violations = []
        for m in range(3, max_m + 1):
            predicted = (m - 1 - digits[m]) + sigma[m] - m * sigma[m - 1]
            if predicted != carries[m]:
                violations.append({"m": m, "carry": carries[m], "predicted": predicted})
            if carries[m] == 1 and digits[m] not in (m - 2, m - 1):
                unit_digit_violations.append(m)
            if carries[m] == 0 and digits[m] not in (m - 1, 0):
                zero_digit_violations.append(m)
        delta_bound_violations = [
            m for m in range(2, max_m + 1)
            if not (0 < deltas[m] < 1 / (facs[m + 1] - 1))
        ]
        return {
            "floors": floors,
            "max_m": max_m,
            "sigma_events": [m for m in range(2, max_m + 1) if sigma[m] == 1],
            "min_fract_over_delta": mp.nstr(
                min(fracts[m] / deltas[m] for m in range(3, max_m + 1)), 12),
            "identity_violations": violations,
            "unit_carry_digit_violations": unit_digit_violations,
            "zero_carry_digit_violations": zero_digit_violations,
            "delta_bound_violations": delta_bound_violations,
            "unit_carries": [m for m in range(3, max_m + 1) if carries[m] == 1],
            "zero_carries": [m for m in range(3, max_m + 1) if carries[m] == 0],
            "digit_at_unit_carries": {
                str(m): digits[m] - (m - 2)
                for m in range(3, max_m + 1) if carries[m] == 1
            },
        }


def family_census(max_m: int, dps: int, shifts: list[int]) -> dict:
    truncation = max_m + 60
    out = {}
    with mp.workdps(dps):
        facs = {0: mp.mpf(1)}
        f = mp.mpf(1)
        for m in range(1, max_m + 1):
            f *= m
            facs[m] = f
        for t in shifts:
            Ct = companion_constant(t, truncation)
            hits = []
            for m in range(3, max_m + 1):
                y = t * facs[m] * Ct
                c = int(mp.ceil(y))
                if (c - 2) % m == 0:
                    hits.append(m)
            out[str(t)] = {
                "residue_two_hits": hits,
                "hit_count": len(hits),
                "expected_uniform": mp.nstr(mp.fsum(mp.mpf(1) / m for m in range(3, max_m + 1)), 6),
            }
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=160)
    parser.add_argument("--family-max-m", type=int, default=400)
    parser.add_argument("--shifts", type=str, default="0,1,2,3,5,-1")
    args = parser.parse_args()
    shifts = [int(s) for s in args.shifts.split(",")]

    dps = decimal_digits_of_factorial(args.max_m + 1) + 400
    first = carry_law_census(args.max_m, dps)
    second = carry_law_census(args.max_m, dps + 120)
    if first["floors"] != second["floors"]:
        raise SystemExit("companion floors unstable under +120 decimal digits")
    del first["floors"]
    del second["floors"]
    if first != second:
        raise SystemExit("census unstable under +120 decimal digits")

    fdps = decimal_digits_of_factorial(args.family_max_m + 1) + 400
    fam = family_census(args.family_max_m, fdps, shifts)
    fam2 = family_census(args.family_max_m, fdps + 120, shifts)
    if fam != fam2:
        raise SystemExit("family census unstable under +120 decimal digits")

    # Consistency with the t = -1 unit-carry list: ceil(-m! C) == 2 mod m
    # is exactly floor(m! C) == -2 mod m, the companion unit-carry residue.
    minus_one_hits = fam["-1"]["residue_two_hits"]
    falsifiers = {
        "exact carry identity holds at every 3<=m<=max_m": not first["identity_violations"],
        "unit carry forces digit in {m-2,m-1}": not first["unit_carry_digit_violations"],
        "zero carry forces digit in {m-1,0}": not first["zero_carry_digit_violations"],
        "0 < delta_m < 1/((m+1)!-1)": not first["delta_bound_violations"],
        "t=0 (e-2) never hits residue 2": fam["0"]["hit_count"] == 0,
        "t=-1 residue hits equal certified unit carries in range": (
            minus_one_hits == [m for m in first["unit_carries"] if m <= args.family_max_m]
            or args.family_max_m < args.max_m
        ),
    }
    payload = {
        "probe_id": probe_id,
        "problem_id": problem_id,
        "parameters": {
            "max_m": args.max_m,
            "family_max_m": args.family_max_m,
            "shifts": shifts,
            "decimal_precision": dps,
            "family_decimal_precision": fdps,
        },
        "carry_law": first,
        "family": fam,
        "falsifiers": falsifiers,
        "all_falsifiers_pass": all(falsifiers.values()),
        "claim_boundary": (
            "finite dual-precision evidence for a Lean-owned exact identity; "
            "no cofinality, non-concentration, or irrationality claim for any t"
        ),
    }
    print(json.dumps(payload, indent=2))
    return 0 if all(falsifiers.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
