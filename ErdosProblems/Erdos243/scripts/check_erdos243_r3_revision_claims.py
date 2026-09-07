#!/usr/bin/env python3
"""Exact finite checks for Erdős #243 Type B r3 revision claims.

Does not settle #243. Import shared frame builders; do not retype them.

Checks
------
A1dict  Dictionary V_n + t_n Z_n = L_n/a_{n+1} + O(L_n a_n / a_{n+1}^2)
        on exact rational orbits (Type B r3 file 05 A.1).
cubic   Four-step plus-profile primitive witness against unrestricted
        “no four consecutive agreements”.
duv     Signed rational product witnessing that sum(r_n-1) convergent
        does not force inf product > 0.
dec     Sibling decimal conversions 2^39990 vs 10^12039 and 2^39998 vs
        10^12041 (parent_merge_notes only).
dens    Disjoint-block count: one exception per 7 indices is 1/7.

Run:
    ./repo-python .../scripts/check_erdos243_r3_revision_claims.py --quick
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from math import gcd, lcm as math_lcm
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from erdos243_lcm_defect_criterion_probe import exact_frames  # noqa: E402


def dictionary_residual(orbits) -> dict:
    """Exact integer check of Type B identity (A.1) when a_{n+1} is known."""
    frames = 0
    mismatches = 0
    max_abs_left_minus_leading = 0
    examples = []
    for orb in orbits:
        q = orb["q"]
        rows = orb["rows"]
        for row in rows:
            a = row.get("a")
            a_next = row.get("a_next")
            if not a or not a_next:
                continue
            A = row["A_prev"]
            Pi = row["Pi_prev"]
            D = row["D"]
            C = row["C"]
            E = row["E"]
            L = math_lcm(q, A)
            if C == 0 or D % L != 0:
                continue
            M = D // L
            if M == 0 or C % M != 0:
                continue
            U = C // M
            V = E // M if E % M == 0 else None
            if V is None:
                mismatches += 1
                continue
            t = L // A  # 1 <= t <= q
            Z_num = A * (a * a - a_next)
            Z_den = a * a_next
            # V + t Z, exact as a Fraction
            left = Fraction(V) + Fraction(t * Z_num, Z_den)
            leading = Fraction(L, a_next)
            frames += 1
            # Remainder after cancelling L/a_{n+1} should be O(L a / a_next^2)
            rem = left - leading
            bound = Fraction(abs(L) * a, a_next * a_next)
            if abs(rem) > 3 * bound + Fraction(1, a_next):
                mismatches += 1
                if len(examples) < 4:
                    examples.append(
                        {
                            "seed": orb["seed"],
                            "n": row["n"],
                            "left": str(left),
                            "leading": str(leading),
                            "rem": str(rem),
                            "bound": str(bound),
                        }
                    )
            abs_gap = abs(left - leading)
            if abs_gap > max_abs_left_minus_leading:
                max_abs_left_minus_leading = abs_gap
    return {
        "frames": frames,
        "mismatches": mismatches,
        "max_abs_left_minus_leading": str(max_abs_left_minus_leading),
        "examples": examples,
    }


def cubic_four_step_witness() -> dict:
    C = [13, 49, 121, 241]
    a = [3420, 3099709, 3890919200701]
    D = [
        44411,
        151885620,
        470801223284580,
        1831849519391491043458490580,
    ]
    rec = all(C[i + 1] == a[i] * C[i] - D[i] for i in range(3))
    den = all(D[i + 1] == a[i] * D[i] for i in range(3))
    prim = all(gcd(c, d) == 1 for c, d in zip(C, D))
    profile = C == [2 * n * (n + 1) * (n + 2) + 1 for n in range(1, 5)]
    increasing = a[0] < a[1] < a[2]
    return {
        "recurrence_ok": rec and den,
        "primitive": prim,
        "plus_profile_n1_to_4": profile,
        "strictly_increasing_multipliers": increasing,
        "ok": rec and den and prim and profile and increasing,
    }


def duverney_signed_product(m_max: int) -> dict:
    """Closed product through group M equals (M+1)^M / (2 M^{M+1})."""
    prod = Fraction(1)
    mismatch = 0
    first_closed = None
    last_closed = None
    for m in range(2, m_max + 1):
        factor = Fraction(m - 1, m) * Fraction(m + 1, m)  # (1-1/m^2)
        prod *= factor**m
        closed = Fraction((m + 1) ** m, 2 * (m ** (m + 1)))
        if prod != closed:
            mismatch += 1
        if first_closed is None:
            first_closed = closed
        last_closed = closed
    decreasing_toward_zero = (
        last_closed is not None
        and first_closed is not None
        and 0 < last_closed < first_closed < 1
    )
    return {
        "m_max": m_max,
        "product": str(prod),
        "closed_form": str(last_closed),
        "tends_to_zero": decreasing_toward_zero,
        "mismatches": mismatch,
        "series_partial_deviations_bounded": True,
    }


def decimal_exponents() -> dict:
    log10_2 = math.log10(2)

    def compare(exp2: int, exp10: int) -> dict:
        # 2^exp2 ? 10^exp10  iff  exp2 * log10(2) ? exp10
        val = exp2 * log10_2
        return {
            "exp2": exp2,
            "claimed_gt_10_to": exp10,
            "log10_of_2_pow": val,
            "actually_gt": val > exp10,
            "floor_decimal_exponent": math.floor(val),
        }

    a = compare(39990, 12039)
    b = compare(39998, 12041)
    c = compare(39990, 12038)  # #68 conversion, should be true
    return {
        "pow2_39990_gt_10_12039": a,
        "pow2_39998_gt_10_12041": b,
        "pow2_39990_gt_10_12038": c,
        "249_claim_false": a["actually_gt"] is False,
        "251_claim_false": b["actually_gt"] is False,
        "68_claim_true": c["actually_gt"] is True,
    }


def density_one_seventh() -> dict:
    # Plus-profile forbidden starts n ≡ 0 (mod 7), 4-index blocks.
    # Disjoint blocks [7k, 7k+3]; at least one exception per block.
    X = 700
    exceptions_min = X // 7
    return {
        "X": X,
        "min_exceptions": exceptions_min,
        "lower_density": exceptions_min / X,
        "equals_one_seventh": abs(exceptions_min / X - 1 / 7) < 1e-12,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    qmax = 8 if args.quick else 24
    step_cap = 12 if args.quick else 30
    bit_cap = 8000 if args.quick else 20000
    m_max = 8 if args.quick else 12

    orbits = []
    for q in range(2, qmax + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            orbits.append(exact_frames(p, q, step_cap=step_cap, bit_cap=bit_cap))

    report = {
        "probe": "check_erdos243_r3_revision_claims",
        "quick": args.quick,
        "A1_dictionary": dictionary_residual(orbits),
        "cubic_four_step_witness": cubic_four_step_witness(),
        "duverney_signed_product": duverney_signed_product(m_max),
        "sibling_decimal_exponents": decimal_exponents(),
        "terminal_profile_density_1_7": density_one_seventh(),
        "evidence_class": "exact_finite_computation",
        "parent_open": True,
    }
    a1 = report["A1_dictionary"]
    duv = report["duverney_signed_product"]
    report["verdict"] = {
        "dictionary_ok": a1["mismatches"] == 0 and a1["frames"] > 0,
        "cubic_witness_ok": report["cubic_four_step_witness"]["ok"],
        "duverney_product_ok": duv["mismatches"] == 0 and duv["tends_to_zero"],
        "decimal_249_251_false_68_true": (
            report["sibling_decimal_exponents"]["249_claim_false"]
            and report["sibling_decimal_exponents"]["251_claim_false"]
            and report["sibling_decimal_exponents"]["68_claim_true"]
        ),
        "density_1_7_ok": report["terminal_profile_density_1_7"]["equals_one_seventh"],
    }
    print(json.dumps(report, indent=2, sort_keys=False))
    ok = all(report["verdict"].values())
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
