#!/usr/bin/env python3
"""Deep named falsifier for the denominator-21 doubling-height producer.

The open Lean producer is

    H(2*d) <= 2*H(d),
    H(0)=1, H(N+1)=max(H(N), Q_N+1),

where Q is the exact greedy defect for 1/21.  This script reuses the
rigorously bracketed block orbit from the primorial-producer falsifier and
tests the producer at every doubling pair.  It also tests the two source
lemmas selected by the record reduction: the phase lock at record successors
and the Euler/nested-height midpoint service inequalities.

Finite survival is evidence and falsification coverage only.  It is never
reported as a proof of the all-depth producer.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import time

import numpy as np


ROOT = pathlib.Path(__file__).resolve().parents[3]
DEEP_ENGINE = (
    ROOT
    / "formal_math/erdos257_hole_geometry/scripts/primorial_producer_falsification.py"
)
DEFAULT_RECEIPT = (
    ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_running_max_deep_receipt.json"
)


def _load_deep_engine():
    spec = importlib.util.spec_from_file_location("erdos257_primorial_deep_engine", DEEP_ENGINE)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load deep orbit engine: {DEEP_ENGINE}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256_file(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(depth: int) -> dict[str, object]:
    engine = _load_deep_engine()
    started = time.time()
    selected, coeff, undecided, min_decision_margin, bracket = engine.orbit(
        1, 21, depth
    )

    # Match the Lean indexing literally.  At the beginning of step n, Q is
    # Q_(n-1), so H[n] is updated before Q_n is computed.
    height = np.empty(depth + 2, dtype=np.int64)
    height[0] = 1
    defect = 0
    max_defect = 0
    records: list[dict[str, int]] = []
    for n in range(1, depth + 1):
        height[n] = max(int(height[n - 1]), defect + 1)
        defect = 2 * defect + engine.t_bit(n) - int(coeff[n])
        max_defect = max(max_defect, defect)
        if defect + 1 > int(height[n]):
            records.append({"rank": n, "defect": defect, "plateau_start": n + 1})
    height[depth + 1] = max(int(height[depth]), defect + 1)

    max_d = depth // 2
    doubling_margins = (
        2 * height[: max_d + 1]
        - height[: 2 * max_d + 1 : 2]
    )
    violating_d = np.nonzero(doubling_margins < 0)[0]
    equality_d = np.nonzero(doubling_margins == 0)[0]
    min_index = int(np.argmin(doubling_margins))

    record_rows: list[dict[str, object]] = []
    for row in records:
        n = row["rank"]
        s = n + 1
        if s > depth or s % 2 != 0:
            record_rows.append({**row, "even_successor": False})
            continue
        d = s // 2
        q_next = 2 * row["defect"] + engine.t_bit(s) - int(coeff[s])
        top_layer = int(coeff[s]) - int(coeff[d])
        phase = engine.t_bit(s) - engine.t_bit(d)
        service_lhs = top_layer + q_next
        midpoint_load = int(coeff[d])
        causal_service_lhs = 2 * row["defect"] + engine.t_bit(s) - midpoint_load
        if causal_service_lhs != service_lhs:
            raise AssertionError(
                f"midpoint-load identity failed at strict record {n}: "
                f"{causal_service_lhs=} != {service_lhs=}"
            )
        service_rhs = 2 * int(height[d]) + phase
        nested_rhs = int(height[d]) + int(height[d // 2]) + phase
        divisor_count = 1
        for exponent in engine.factor(d).values():
            divisor_count *= exponent + 1
        omitted_divisor_load = divisor_count - midpoint_load
        full_divisor_envelope_margin = divisor_count - 2 * row["defect"]
        omitted_divisor_budget_margin = (
            int(height[d]) + 2 - engine.t_bit(s) - omitted_divisor_load
        )
        height_plus_two_margin = int(height[d]) + 2 - service_lhs
        if (
            full_divisor_envelope_margin + omitted_divisor_budget_margin
            != height_plus_two_margin
        ):
            raise AssertionError(
                f"divisor-split identity failed at strict record {n}"
            )
        record_rows.append(
            {
                **row,
                "even_successor": True,
                "midpoint": d,
                "height_midpoint": int(height[d]),
                "height_half_midpoint": int(height[d // 2]),
                "midpoint_load": midpoint_load,
                "midpoint_divisor_count": divisor_count,
                "omitted_midpoint_divisor_load": omitted_divisor_load,
                "top_two_adic_layer": top_layer,
                "next_defect": q_next,
                "phase_difference": phase,
                "causal_service_lhs": causal_service_lhs,
                "midpoint_load_threshold_for_height_plus_two": (
                    2 * row["defect"] + engine.t_bit(s) - int(height[d]) - 2
                ),
                "midpoint_load_margin_for_height_plus_two": (
                    midpoint_load
                    - (2 * row["defect"] + engine.t_bit(s) - int(height[d]) - 2)
                ),
                "full_divisor_envelope_margin": full_divisor_envelope_margin,
                "half_selected_divisor_margin": 2 * midpoint_load - divisor_count,
                "omitted_divisor_budget_margin": omitted_divisor_budget_margin,
                "divisor_split_identity_holds": True,
                "doubling_margin": 2 * int(height[d]) - int(height[s]),
                "euler_midpoint_service_margin": service_rhs - service_lhs,
                "nested_height_margin": nested_rhs - service_lhs,
                "single_height_service_margin": int(height[d]) - service_lhs,
                "height_plus_two_service_margin": int(height[d]) + 2 - service_lhs,
                "successor_mod_4": s % 4,
                "successor_mod_20": s % 20,
            }
        )

    post_seed = [r for r in record_rows if r["rank"] > 19]
    even_rows = [r for r in record_rows if r.get("even_successor")]
    post_780_even_rows = [r for r in even_rows if r["plateau_start"] > 780]
    single_height_exceptions = [
        r for r in even_rows if r["single_height_service_margin"] < 0
    ]
    baseline_max_d = min(max_d, 1_000_001)
    baseline = doubling_margins[: baseline_max_d + 1]

    return {
        "schema": "twenty_one_running_max_deep_receipt_v1",
        "claim_ceiling": (
            "Finite exact survival does not prove the all-depth doubling-height, "
            "phase-lock, Euler-service, or nested-height producer and does not "
            "decide Erdős 257."
        ),
        "target": "1/21",
        "depth": depth,
        "engine": {
            "path": str(DEEP_ENGINE.relative_to(ROOT)),
            "sha256": sha256_file(DEEP_ENGINE),
            "undecided_decisions": len(undecided),
            "rigorous_error_bracket_units": bracket,
            "min_abs_decision_margin_units": min_decision_margin,
            "decision_safety_factor": round(min_decision_margin / bracket, 1),
            "selected_count_at_500002": int(selected[:500_003].sum())
            if depth >= 500_002
            else None,
            "pinned_selected_count_match": bool(
                depth >= 500_002 and int(selected[:500_003].sum()) == 249_858
            ),
        },
        "defect": {
            "maximum": max_defect,
            "record_count": len(records),
            "last_ten_records": records[-10:],
        },
        "doubling_height": {
            "pairs": max_d + 1,
            "violations": int(violating_d.size),
            "first_violating_d": int(violating_d[0]) if violating_d.size else None,
            "minimum_margin": int(doubling_margins[min_index]),
            "minimum_margin_d": min_index,
            "equality_count": int(equality_d.size),
            "equality_d": [int(d) for d in equality_d[:20]],
            "baseline_through_d": baseline_max_d,
            "baseline_violations": int(np.count_nonzero(baseline < 0)),
            "baseline_equalities": int(np.count_nonzero(baseline == 0)),
            "height_20": int(height[20]) if depth >= 20 else None,
        },
        "record_reduction": {
            "rows": record_rows,
            "post_rank_19_rows": len(post_seed),
            "post_rank_19_phase_lock_mod_4_violations": sum(
                r.get("successor_mod_4") != 0 for r in post_seed
            ),
            "post_rank_19_phase_lock_mod_20_violations": sum(
                r.get("successor_mod_20") != 0 for r in post_seed
            ),
            "euler_midpoint_service_violations": sum(
                r["euler_midpoint_service_margin"] < 0 for r in even_rows
            ),
            "euler_midpoint_service_min_margin": min(
                r["euler_midpoint_service_margin"] for r in even_rows
            ),
            "nested_height_violations": sum(
                r["nested_height_margin"] < 0 for r in even_rows
            ),
            "nested_height_min_margin": min(
                r["nested_height_margin"] for r in even_rows
            ),
            "height_plus_two_service_violations": sum(
                r["height_plus_two_service_margin"] < 0 for r in even_rows
            ),
            "height_plus_two_service_min_margin": min(
                r["height_plus_two_service_margin"] for r in even_rows
            ),
            "full_divisor_envelope_violations": sum(
                r["full_divisor_envelope_margin"] < 0 for r in even_rows
            ),
            "full_divisor_envelope_min_margin": min(
                r["full_divisor_envelope_margin"] for r in even_rows
            ),
            "half_selected_divisor_violations": sum(
                r["half_selected_divisor_margin"] < 0 for r in even_rows
            ),
            "half_selected_divisor_min_margin": min(
                r["half_selected_divisor_margin"] for r in even_rows
            ),
            "omitted_divisor_budget_violations": sum(
                r["omitted_divisor_budget_margin"] < 0 for r in even_rows
            ),
            "omitted_divisor_budget_min_margin": min(
                r["omitted_divisor_budget_margin"] for r in even_rows
            ),
            "single_height_service_exception_successors": [
                r["plateau_start"] for r in single_height_exceptions
            ],
            "post_successor_780_single_height_rows": len(post_780_even_rows),
            "post_successor_780_single_height_violations": sum(
                r["single_height_service_margin"] < 0 for r in post_780_even_rows
            ),
            "post_successor_780_single_height_min_margin": min(
                r["single_height_service_margin"] for r in post_780_even_rows
            ),
        },
        "elapsed_seconds": round(time.time() - started, 1),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=20_000_002)
    parser.add_argument("--output", type=pathlib.Path, default=DEFAULT_RECEIPT)
    args = parser.parse_args()
    if args.depth < 500_002:
        raise SystemExit("depth must be at least 500002 for the pinned-itinerary check")
    payload = audit(args.depth)
    output = args.output if args.output.is_absolute() else ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    try:
        output_label = str(output.relative_to(ROOT))
    except ValueError:
        output_label = str(output)
    summary = {
        "depth": payload["depth"],
        "engine": payload["engine"],
        "defect": payload["defect"],
        "doubling_height": payload["doubling_height"],
        "record_reduction": {
            key: value
            for key, value in payload["record_reduction"].items()
            if key != "rows"
        },
        "receipt": output_label,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if (
        payload["engine"]["undecided_decisions"] == 0
        and payload["engine"]["pinned_selected_count_match"]
        and payload["doubling_height"]["violations"] == 0
        and payload["doubling_height"]["baseline_violations"] == 0
    ) else 1


if __name__ == "__main__":
    raise SystemExit(main())
