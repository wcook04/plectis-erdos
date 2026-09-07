#!/usr/bin/env python3
"""Exact discriminator for the two-channel pullback slack.

This is deliberately a consumer of ``half_midpoint_tail_bridge_lab`` rather
than a second seam engine.  It checks the centered-carry coefficient and the
exact decomposition

    total_slack = 4**k * backward_slack + 3 * forward_slack

on every late factor-range upper pullback in the requested finite window.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
SEAM_LAB = HERE / "half_midpoint_tail_bridge_lab.py"


def load_seam_lab() -> Any:
    spec = importlib.util.spec_from_file_location("half_midpoint_tail_bridge_lab", SEAM_LAB)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {SEAM_LAB}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def audit(max_rank: int) -> dict[str, Any]:
    lab = load_seam_lab()
    result = lab.audit_forced_seam_words(max_rank, include_pullback_events=True)
    events = [
        event
        for event in result["upper_pullback_events"]
        if event["is_late_largest_false"] and event["factor_range"]
    ]
    if not events:
        raise AssertionError("no late factor-range pullbacks in audit window")

    backward_dominant = 0
    forward_dominant = 0
    minimum_coefficient: tuple[int, dict[str, Any]] | None = None
    minimum_backward_slack: tuple[int, dict[str, Any]] | None = None
    minimum_forward_slack: tuple[int, dict[str, Any]] | None = None

    for event in events:
        q = int(event["pullback_coordinate"])
        g = int(event["critical_gap"])
        r = int(event["endpoint_remainder"])
        m = int(event["backward_length"])
        k = int(event["right_run_length"])
        start = int(event["backward_multiplicity_window_start_centered_carry"])
        end = int(event["backward_multiplicity_window_end_centered_carry"])

        coefficient = start + 1 - q
        backward_slack = 3 * g - ((4**m) * q + 2 * q)
        forward_slack = 3 * r - ((4**k) * g + 2 * g)
        recomposed = (4**k) * backward_slack + 3 * forward_slack

        if coefficient <= 0:
            raise AssertionError(f"nonpositive centered coefficient at source {event['source_rank']}")
        if end != (4**m) * coefficient + g - 1:
            raise AssertionError(f"centered-carry balance failed at source {event['source_rank']}")
        if backward_slack < 0 or forward_slack < 0:
            raise AssertionError(f"negative component slack at source {event['source_rank']}")
        if recomposed != int(event["two_block_amplification_slack"]):
            raise AssertionError(f"two-channel decomposition failed at source {event['source_rank']}")

        if (4**k) * backward_slack >= 3 * forward_slack:
            backward_dominant += 1
        else:
            forward_dominant += 1

        row = {
            "source_rank": int(event["source_rank"]),
            "largest_false_rank": int(event["largest_false_rank"]),
            "right_run_length": k,
            "endpoint_rank": int(event["endpoint_rank"]),
        }
        if minimum_coefficient is None or coefficient < minimum_coefficient[0]:
            minimum_coefficient = (coefficient, row)
        if minimum_backward_slack is None or backward_slack < minimum_backward_slack[0]:
            minimum_backward_slack = (backward_slack, row)
        if minimum_forward_slack is None or forward_slack < minimum_forward_slack[0]:
            minimum_forward_slack = (forward_slack, row)

    assert minimum_coefficient is not None
    assert minimum_backward_slack is not None
    assert minimum_forward_slack is not None
    return {
        "schema": "erdos257_centered_carry_pullback_balance_audit_v0",
        "max_rank": max_rank,
        "late_factor_range_event_count": len(events),
        "centered_balance_failure_count": 0,
        "two_channel_decomposition_failure_count": 0,
        "negative_backward_slack_count": 0,
        "negative_forward_slack_count": 0,
        "backward_dominant_count": backward_dominant,
        "forward_dominant_count": forward_dominant,
        "minimum_centered_coefficient": {
            "value": minimum_coefficient[0],
            **minimum_coefficient[1],
        },
        "minimum_backward_slack": {
            "value": minimum_backward_slack[0],
            **minimum_backward_slack[1],
        },
        "minimum_forward_slack": {
            "value": minimum_forward_slack[0],
            **minimum_forward_slack[1],
        },
        "claim_boundary": (
            "Finite exact falsification only. The audit does not prove positivity "
            "or the pullback-card margin at all ranks."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-rank", type=int, default=1500)
    args = parser.parse_args()
    print(json.dumps(audit(args.max_rank), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
