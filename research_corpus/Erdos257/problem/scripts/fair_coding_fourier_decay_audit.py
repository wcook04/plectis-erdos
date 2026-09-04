#!/usr/bin/env python3
"""Interval audit for the fair-coding Fourier product and its resonances.

The uniform |xi|^(-1/3) estimate is proved analytically in
``FairCodingFourierDecay.md``.  This producer uses mpmath's directed interval
context for finite cosine products, adds an explicit analytic infinite-tail
enclosure, and compares LCM-aligned frequencies with deterministic controls.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from pathlib import Path

import mpmath as mp


def endpoint(x: object, side: str) -> mp.mpf:
    index = 0 if side == "a" else 1
    return mp.mpf(x._mpi_[index])


def fourier_magnitude_interval(xi: int, guard_bits: int) -> tuple[mp.mpf, mp.mpf, int]:
    assert 0 < xi
    cutoff = xi.bit_length() + guard_bits
    product = mp.iv.mpf(1)
    for n in range(1, cutoff + 1):
        mersenne = (1 << n) - 1
        residue = xi % mersenne if mersenne > 1 else 0
        distance = min(residue, mersenne - residue) if mersenne > 1 else 0
        angle = mp.iv.pi * mp.iv.mpf(distance) / mersenne
        product *= abs(mp.iv.cos(angle))

    # For n>cutoff, cos(x)>=1-x^2/2 and
    # sum 1/(2^n-1)^2 <= (4/3)4^(-cutoff).
    tail_loss = (
        mp.iv.mpf(2) * mp.iv.pi**2 / 3
        * mp.iv.mpf(xi) ** 2
        * mp.iv.mpf(4) ** (-cutoff)
    )
    assert endpoint(tail_loss, "b") < 1
    tail_lower = max(mp.mpf(0), 1 - endpoint(tail_loss, "b"))
    lower = endpoint(product, "a") * tail_lower
    upper = endpoint(product, "b")
    return lower, upper, cutoff


def neg_log2_interval(lower: mp.mpf, upper: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    return -mp.log(upper, 2), -mp.log(lower, 2)


def row(kind: str, parameter: int, xi: int, guard_bits: int) -> dict[str, object]:
    lower, upper, cutoff = fourier_magnitude_interval(xi, guard_bits)
    log_lo_exact, log_hi_exact = neg_log2_interval(lower, upper)
    log_lo = float(log_lo_exact)
    log_hi = float(log_hi_exact)
    constant = 2 / mp.pi + 2 * mp.pi / 3
    theorem_bound = constant * mp.mpf(xi) ** (-mp.mpf(1) / 3)
    exponent_lo = log_lo / math.log2(xi) if xi > 1 else 0.0
    exponent_hi = log_hi / math.log2(xi) if xi > 1 else 0.0
    return {
        "kind": kind,
        "parameter": parameter,
        "frequency_bits": xi.bit_length(),
        "frequency_sha256": hashlib.sha256(str(xi).encode()).hexdigest(),
        "cosine_cutoff": cutoff,
        "neg_log2_magnitude_interval": [log_lo, log_hi],
        "neg_log2_interval_width_decimal": mp.nstr(
            max(mp.mpf(0), log_hi_exact - log_lo_exact), 12
        ),
        "observed_power_exponent_interval": [exponent_lo, exponent_hi],
        "theorem_bound_verified": bool(upper <= theorem_bound),
        "upper_over_theorem_bound": float(upper / theorem_bound),
    }


def run(max_m: int, guard_bits: int, seed: int) -> dict[str, object]:
    rng = random.Random(seed)
    lcm_value = 1
    resonance_rows: list[dict[str, object]] = []
    control_rows: list[dict[str, object]] = []
    selected = set(range(4, max_m + 1, 2))

    for m in range(1, max_m + 1):
        lcm_value = math.lcm(lcm_value, (1 << m) - 1)
        if m not in selected:
            continue
        resonance_rows.append(row("mersenne_lcm", m, lcm_value, guard_bits))
        bits = lcm_value.bit_length()
        control = rng.randrange(1 << (bits - 1), 1 << bits)
        control_rows.append(row("same_bit_random_integer", m, control, guard_bits))

    zeros = [
        {
            "m": m,
            "frequency": f"(2^{m}-1)/2",
            "zero_factor": m,
            "reason": "cos(pi*((2^m-1)/2)/(2^m-1))=cos(pi/2)=0",
            "redundancy": "frequency is an odd half-integer and is already zero at factor n=1",
        }
        for m in range(1, max_m + 1)
    ]

    all_rows = resonance_rows + control_rows
    width_max = max(mp.mpf(r["neg_log2_interval_width_decimal"]) for r in all_rows)
    improvements = [
        control_rows[i]["neg_log2_magnitude_interval"][0]
        - resonance_rows[i]["neg_log2_magnitude_interval"][1]
        for i in range(len(resonance_rows))
    ]

    return {
        "schema": "erdos257_fair_coding_fourier_decay_audit_v0",
        "parameters": {
            "max_m": max_m,
            "guard_bits": guard_bits,
            "interval_decimal_digits": mp.iv.dps,
            "control_seed": seed,
        },
        "proved_all_scale_result": {
            "fourier_normalization": "hat(f)(xi)=integral f(x) exp(-2*pi*i*xi*x) dx",
            "product": "hat(1_Acal)(xi)=exp(-pi*i*xi*E)*product_n cos(pi*xi/(2^n-1))",
            "uniform_bound": "abs(hat(1_Acal)(xi)) <= (2/pi+2*pi/3)*abs(xi)^(-1/3) for abs(xi)>=1",
            "exact_zero_family": "hat(1_Acal)(j/2)=0 for every odd integer j; the m-indexed formula gives redundant subfamilies of this one lattice",
            "proof_location": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/FairCodingFourierDecay.md",
        },
        "interval_validation": {
            "all_rows_satisfy_uniform_bound": all(r["theorem_bound_verified"] for r in all_rows),
            "max_neg_log2_interval_width_decimal": mp.nstr(width_max, 12),
            "resonance_rows": resonance_rows,
            "control_rows": control_rows,
            "lcm_improvement_bits": improvements,
            "half_mersenne_exact_zeros": zeros,
        },
        "claim_boundary": [
            "The decay theorem is analytic and all-scale; interval rows are validation and resonance mapping, not its proof.",
            "Polynomial Fourier decay does not decide membership of any prescribed rational and does not settle Erdos 257.",
            "LCM alignment raises Fourier mass relative to same-bit controls but still decays; no nondecaying resonance was observed or claimed.",
            "The m-indexed exact-zero formulas are all contained in the half-integer lattice forced by the first coin and are not independent Mersenne resonance evidence.",
        ],
        "consequence_decisions": [
            {
                "surface": "FairCodingPushforward.md",
                "decision": "verified_no_change",
                "reason": "The pushforward identification is an input to this theorem; the new Fourier note links the dependency in the forward direction.",
            },
            {
                "surface": "rational_membership_and_universal_erdos257_claims",
                "decision": "verified_no_change",
                "reason": "Polynomial Fourier decay and exact transform zeros do not decide membership of any prescribed rational.",
            },
            {
                "surface": "historical_fourier_research_and_public_claim_surfaces",
                "decision": "defer_with_reason",
                "reason": "The theorem is durably bound here but is not yet Lean-formalized and creates no rational-membership consequence suitable for public theorem claims.",
            },
            {
                "surface": "generic_lexical_candidates_prod__prod_n__mathbf1_",
                "decision": "outside_scope",
                "reason": "These consequence-map hits are symbol collisions rather than semantic dependencies of the fair-coding theorem.",
            },
            {
                "surface": "formal_math_research_packet",
                "decision": "defer_with_reason",
                "reason": "The current packet has no matching fair-coding Fourier row and is concurrently owned; the theorem note and machine receipt are the present authority surfaces.",
            },
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=32)
    parser.add_argument("--guard-bits", type=int, default=48)
    parser.add_argument("--interval-dps", type=int, default=100)
    parser.add_argument("--seed", type=int, default=257)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("state/formal_math/erdos257_period_noncollapse/fair_coding_fourier_decay_receipt.json"),
    )
    args = parser.parse_args()
    mp.iv.dps = args.interval_dps
    mp.mp.dps = args.interval_dps
    result = run(args.max_m, args.guard_bits, args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "output": str(args.output),
        "all_bounds_verified": result["interval_validation"]["all_rows_satisfy_uniform_bound"],
        "resonance_row_count": len(result["interval_validation"]["resonance_rows"]),
        "exact_zero_family_count": len(result["interval_validation"]["half_mersenne_exact_zeros"]),
        "max_interval_width": result["interval_validation"]["max_neg_log2_interval_width_decimal"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
