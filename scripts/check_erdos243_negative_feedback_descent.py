#!/usr/bin/env python3
"""Falsify local negative-mass descent laws in the exact Erdős #243 feedback map."""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)

SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_negative_feedback_descent.py"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CenteredEuclideanFeedback.lean"
)
LAB_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "NegativeFeedbackDescentComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "research_packet.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT / "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "negative_feedback_descent_receipt.json"
)


def step(u: int, v: int) -> dict[str, int] | None:
    nearest = (2 * v + u) // (2 * u)
    e = v - nearest * u
    if 2 * abs(e) >= u:
        return None
    a = nearest + 1
    raw_u, raw_v = a * u - v, a * v
    h = math.gcd(raw_u, raw_v)
    return {"a": a, "e": e, "h": h, "u": raw_u // h, "v": raw_v // h}


def scan(max_u: int, max_multiplier: int) -> dict[str, object]:
    valid = 0
    first_absolute = None
    first_normalized = None
    first_all_nonnegative_homogeneous_weights = None
    maximum = None
    for u in range(1, max_u + 1):
        for v in range(u, max_multiplier * u + 1):
            if math.gcd(u, v) != 1:
                continue
            current = step(u, v)
            if current is None or current["e"] >= 0:
                continue
            successor = step(current["u"], current["v"])
            if (
                successor is None
                or successor["e"] >= 0
                or successor["a"] <= current["a"]
            ):
                continue
            m, m_next = -current["e"], -successor["e"]
            A = current["a"] ** 2 // current["h"]
            k = current["a"] ** 2 - current["a"] + 1 - successor["a"]
            assert A * m == k * current["u"] + m_next
            row = {
                "u": u,
                "v": v,
                "a": current["a"],
                "m": m,
                "h": current["h"],
                "u_next": current["u"],
                "v_next": current["v"],
                "a_next": successor["a"],
                "m_next": m_next,
                "square_free_cancellation_quotient_A": A,
                "centered_quotient_k": k,
            }
            valid += 1
            if first_absolute is None and m_next >= m:
                first_absolute = row
            if first_normalized is None and m_next * u >= m * current["u"]:
                first_normalized = row
            if (
                first_all_nonnegative_homogeneous_weights is None
                and m_next >= m
                and current["u"] <= u
            ):
                first_all_nonnegative_homogeneous_weights = row
            if (
                maximum is None
                or m_next * u * maximum["denominator"]
                > maximum["numerator"] * m * current["u"]
            ):
                maximum = {
                    "numerator": m_next * u,
                    "denominator": m * current["u"],
                    "witness": row,
                }
    assert (
        first_absolute is not None
        and first_normalized is not None
        and first_all_nonnegative_homogeneous_weights is not None
        and maximum
    )
    return {
        "valid_negative_to_negative_increasing_steps": valid,
        "first_absolute_descent_counterexample": first_absolute,
        "first_normalized_descent_counterexample": first_normalized,
        "first_all_nonnegative_homogeneous_weights_counterexample": (
            first_all_nonnegative_homogeneous_weights
        ),
        "homogeneous_weight_consequence": (
            "Because m_next>=m and u_next<=u, m_next/u_next^alpha is at "
            "least m/u^alpha for every real alpha>=0; the stored witness is strict."
        ),
        "maximum_normalized_growth_ratio": maximum,
    }


def build_receipt(max_u: int, max_multiplier: int) -> dict[str, object]:
    result = scan(max_u, max_multiplier)
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Force eventual Sylvester recurrence from rational reciprocal sum and "
            "a_(n+1)/a_n^2 tending to one."
        ),
        claim_ceiling=(
            "This eliminates every one-step homogeneous weight m/u^alpha for real "
            "alpha>=0; "
            "it does not exclude globally constrained aperiodic negative excursions."
        ),
        hypothesis_id="negative_feedback_local_mass_descent",
        hypothesis_statement=(
            "Some real alpha>=0 makes m/u^alpha strictly decrease on every primitive "
            "strictly centred negative-to-negative step with increasing multiplier."
        ),
        probe_id="exact_primitive_feedback_step_scan",
        probe_question=(
            "Can any nonnegative homogeneous power of the primitive scale turn "
            "negative mass into a one-step Lyapunov function?"
        ),
        computation=(
            "Enumerate primitive pairs, execute two exact dynamically reduced centred "
            "steps, retain negative-to-negative transitions with increasing multiplier, "
            "and verify the Lean centered-quotient identity A*m=k*u_next+m_next."
        ),
        falsifier=(
            "One valid step with m_next>=m and u_next<=u, which makes every "
            "m/u^alpha with alpha>=0 nondecreasing simultaneously."
        ),
        stop_condition=(
            "Stop on an exact small witness and bind a bounded regression census; do "
            "not increase bounds as evidence for an infinitary conclusion."
        ),
        survival_consequence=(
            "A surviving descent law would provide a well-founded obstruction to "
            "cofinally unbounded negative excursions."
        ),
        falsification_consequence=(
            "Any successful invariant must use multi-step payment, residue, or global "
            "prefix coherence rather than local negative magnitude."
        ),
        consumer_ref=PACKET_REF,
        analysis_refs=[LAB_REF, LEAN_REF],
        source_refs=[SCRIPT_REF, LEAN_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "The primitive seed (9,62) sends scale u=9 to u_next=5 while "
            "negative mass goes from 1 to 2; every m/u^alpha with alpha>=0 "
            "strictly increases on this exact step."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "One exact transition eliminates the whole declared homogeneous "
            "Lyapunov family, not a larger finite census."
        ),
        next_analytic_target=(
            "Use multi-step cancellation payment, residue compatibility, or global "
            "prefix coherence; no one-step nonnegative homogeneous scale weight survives."
        ),
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-negative-feedback-descent/1",
        "parameters": {"max_u": max_u, "max_multiplier": max_multiplier},
        "result": result,
        "experiment_contract": contract,
        "sources": [
            source_record(REPO_ROOT, ref)
            for ref in [SCRIPT_REF, LEAN_REF, LAB_REF, PACKET_REF]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-u", type=int, default=250)
    parser.add_argument("--max-multiplier", type=int, default=100)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.max_u < 6 or args.max_multiplier < 6:
        parser.error("bounds must include the kernel-checked witness")
    rendered = json.dumps(
        build_receipt(args.max_u, args.max_multiplier), indent=2, sort_keys=True
    ) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {args.output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(args.output)}))
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(args.output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
