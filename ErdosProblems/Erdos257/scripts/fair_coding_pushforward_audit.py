#!/usr/bin/env python3
"""Exact finite-cylinder audit for the fair Mersenne coding theorem.

The all-scale theorem is proved in ``FairCodingPushforward.md`` from existing
Lean-checked inputs (measure one and injective coding).  This producer does not
sample support words.  It checks, with ``Fraction`` arithmetic, the finite
cylinder geometry used by that proof and writes a durable JSON receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path


def weight(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def tail_bracket(n: int, cutoff: int) -> tuple[Fraction, Fraction]:
    """Directed rational bracket for sum_{k>n} 1/(2^k-1)."""
    assert 0 <= n < cutoff
    finite = sum((weight(k) for k in range(n + 1, cutoff + 1)), Fraction())
    # For k>cutoff, 2^-k < w_k <= 2^-k/(1-2^-(cutoff+1)).
    geometric = Fraction(1, 1 << cutoff)
    lower = finite + geometric
    upper = finite + geometric / (1 - Fraction(1, 1 << (cutoff + 1)))
    return lower, upper


def frac_record(x: Fraction) -> dict[str, object]:
    raw = f"{x.numerator}/{x.denominator}"
    return {
        "numerator_bits": x.numerator.bit_length(),
        "denominator_bits": x.denominator.bit_length(),
        "sha256": hashlib.sha256(raw.encode()).hexdigest(),
    }


def run(depth: int, cutoff: int) -> dict[str, object]:
    assert 1 <= depth < cutoff
    rows: list[dict[str, object]] = []
    all_strict = True
    stage_strictly_above_one = True
    stage_widths_decrease = True
    previous_hi: Fraction | None = None

    for n in range(1, depth + 1):
        tail_lo, tail_hi = tail_bracket(n, cutoff)
        gap_lo = weight(n) - tail_hi
        stage_lo = (1 << n) * tail_lo
        stage_hi = (1 << n) * tail_hi
        all_strict &= gap_lo > 0
        stage_strictly_above_one &= 1 < stage_lo < stage_hi
        if previous_hi is not None:
            # Exact stage volumes decrease; the directed brackets need not be
            # disjoint, so check the exact finite recurrence instead below.
            stage_widths_decrease &= True
        previous_hi = stage_hi
        rows.append(
            {
                "depth": n,
                "prefix_count": 1 << n,
                "fair_prefix_mass": f"1/{1 << n}",
                "tail_lower": frac_record(tail_lo),
                "tail_upper": frac_record(tail_hi),
                "strict_sibling_gap_lower": frac_record(gap_lo),
                "stage_volume_lower_minus_one": frac_record(stage_lo - 1),
                "stage_volume_upper_minus_one": frac_record(stage_hi - 1),
            }
        )

    # V_n=2^n T_n and T_n=w_(n+1)+T_(n+1), hence
    # V_n-V_(n+1)=2^n(w_(n+1)-T_(n+1))>0.
    recurrence_checks = []
    for n in range(1, depth):
        next_tail_lo, next_tail_hi = tail_bracket(n + 1, cutoff)
        decrement_lo = (1 << n) * (weight(n + 1) - next_tail_hi)
        recurrence_checks.append(decrement_lo > 0)
    stage_widths_decrease &= all(recurrence_checks)

    return {
        "schema": "erdos257_fair_coding_pushforward_audit_v0",
        "parameters": {"depth": depth, "tail_cutoff": cutoff},
        "finite_cylinder_audit": {
            "all_strict_sibling_gaps_certified": all_strict,
            "all_stage_volume_lower_bounds_strictly_above_one": stage_strictly_above_one,
            "stage_volumes_strictly_decrease_certified": stage_widths_decrease,
            "largest_prefix_count": 1 << depth,
            "rows": rows,
        },
        "all_scale_statement_audited": {
            "coding_space": "{0,1}^N with independent fair coordinates",
            "value_map": "pi(b)=sum_{n>=1} b_n/(2^n-1)",
            "cylinder_mass_identity": "P[prefix=u]=volume(pi[prefix=u])=2^(-|u|)",
            "conclusion": "map pi of fair Bernoulli product measure equals Lebesgue measure restricted to the Mersenne achievement set",
            "proof_location": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/FairCodingPushforward.md",
        },
        "claim_boundary": [
            "Finite arithmetic validates the cylinder geometry; the all-scale conclusion is a mathematical proof using existing Lean-checked measure-one and injectivity theorems.",
            "The pushforward theorem is metric. It does not imply that any prescribed rational belongs to the achievement set and does not settle Erdos 257.",
        ],
        "consequence_decisions": [
            {
                "surface": "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/research_packet.json::formalise_fair_pushforward",
                "decision": "defer_with_reason",
                "reason": "The mathematical proof is complete, but the named producer explicitly asks for formalisation and the owner path is concurrently claimed. Re-enter after the owner releases the path or after a Lean declaration lands.",
            },
            {
                "surface": "formal_math/erdos257_period_noncollapse/ErdosProblems/assimilation_manifest.json",
                "decision": "verified_no_change",
                "reason": "The open-producer id remains correct until the pushforward theorem is Lean formalised.",
            },
            {
                "surface": "existing measure-one and injective-coding claims",
                "decision": "verified_no_change",
                "reason": "They are inputs to the new theorem and their statements and authority do not change.",
            },
            {
                "surface": "rational-membership and universal Erdos 257 claims",
                "decision": "verified_no_change",
                "reason": "The new identity is measure-theoretic and supplies no arithmetic information on the null set of rational points.",
            },
            {
                "surface": "mathematical_consequence_map candidates matched only by Fraction",
                "decision": "outside_scope",
                "reason": "Generic Python exact-arithmetic vocabulary is not a mathematical consequence edge.",
            },
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=24)
    parser.add_argument("--tail-cutoff", type=int, default=192)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("state/formal_math/erdos257_period_noncollapse/fair_coding_pushforward_receipt.json"),
    )
    args = parser.parse_args()
    result = run(args.depth, args.tail_cutoff)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "output": str(args.output),
        "strict_gaps": result["finite_cylinder_audit"]["all_strict_sibling_gaps_certified"],
        "stage_volumes_decrease": result["finite_cylinder_audit"]["stage_volumes_strictly_decrease_certified"],
        "largest_prefix_count": result["finite_cylinder_audit"]["largest_prefix_count"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
