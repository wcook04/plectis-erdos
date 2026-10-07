#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep evaluation-time and current-tree corpus facts visibly separate."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

from query_corpus import publication_evidence_packet


def main() -> int:
    packet = publication_evidence_packet("summary")
    historical = packet["corpus_snapshot"]
    current = packet["current_corpus_census"]
    time_axis = packet["time_axis"]
    failures: list[str] = []
    if historical["snapshot_kind"] != "evaluation_checkpoint_not_current_tree":
        failures.append("historical snapshot lost its evaluation-time posture")
    if current["snapshot_kind"] != "current_worktree_navigation_state":
        failures.append("current census lost its worktree-time posture")
    for field, delta in time_axis["current_minus_evaluation"].items():
        if current[field] - historical[field] != delta:
            failures.append(f"{field}: delta is not derived from both snapshots")
    same = all(
        historical[field] == current[field]
        for field in time_axis["current_minus_evaluation"]
    )
    if time_axis["same_as_evaluation_snapshot"] is not same:
        failures.append("same-snapshot verdict is not derived")
    if "evaluation-time" not in time_axis["rule"]:
        failures.append("time-axis rule lost its historical/current distinction")
    if failures:
        print(f"test_publication_evidence_time_axis: {len(failures)} failure(s)")
        for failure in failures:
            print(f"  FAIL {failure}")
        return 1
    print(
        "test_publication_evidence_time_axis: evaluation and current corpus "
        "censuses are separated with derived deltas"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
