#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the finite #257 second-channel measurement."""

from __future__ import annotations

from fractions import Fraction

import probe_second_channel_separation as probe


def test_weights_and_small_exact_states() -> None:
    assert [probe.mersenne_weight(n) for n in range(1, 7)] == [
        Fraction(1, 1),
        Fraction(1, 3),
        Fraction(1, 7),
        Fraction(1, 15),
        Fraction(1, 31),
        Fraction(1, 63),
    ]
    remainder = Fraction(1, 2)
    expected = {
        1: (False, Fraction(2, 1), Fraction(131, 112)),
        2: (True, Fraction(4, 3), Fraction(449, 672)),
        3: (True, Fraction(-104, 21), Fraction(967, 192)),
        4: (False, Fraction(-80, 21), Fraction(1511, 384)),
        5: (False, Fraction(352, 21), Fraction(87313, 5376)),
        6: (True, Fraction(64, 63), Fraction(16307, 32256)),
    }
    for rank in range(1, 7):
        weight = probe.mersenne_weight(rank)
        took = weight <= remainder
        if took:
            remainder -= weight
        phase = probe.direct_phase(rank, remainder)
        margin = probe.separation_margin(rank, phase)
        assert (took, phase, margin) == expected[rank]


def test_phase_recurrence_matches_direct_model() -> None:
    remainder = Fraction(1, 2)
    previous_phase = probe.direct_phase(0, remainder)
    assert previous_phase == 0
    for rank in range(1, 81):
        weight = probe.mersenne_weight(rank)
        took = weight <= remainder
        if took:
            remainder -= weight
        phase = probe.direct_phase(rank, remainder)
        assert phase == probe.next_phase_from_branch(
            rank - 1, previous_phase, took
        )
        previous_phase = phase


def test_source_contract_rejects_formula_drift() -> None:
    text = probe.SOURCE_PATH.read_text(encoding="utf-8")
    contract = probe.source_contract(text)
    assert [row["declaration"] for row in contract["definitions"]] == list(
        probe.SOURCE_FRAGMENTS
    )
    changed_threshold = text.replace("37 / 56", "36 / 56", 1)
    try:
        probe.source_contract(changed_threshold)
    except probe.SourceContractError:
        pass
    else:
        raise AssertionError("changed threshold must break the source contract")

    missing_branch = text.replace(
        "greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)",
        "greedyMersenneRemainderRat x n",
        1,
    )
    try:
        probe.source_contract(missing_branch)
    except probe.SourceContractError:
        pass
    else:
        raise AssertionError("changed recurrence must break the source contract")


def test_default_measurement_and_artifact() -> None:
    data = probe.build_measurement()
    assert data["schema"] == "erdos249257-second-channel-separation-probe/1"
    assert data["status"] == "MEASURED"
    assert data["question_id"] == "XQ257-second-channel-separation"
    assert data["parameters"]["checked_ranks"] == {
        "minimum": 1,
        "maximum": 1000,
    }
    summary = data["summary"]
    assert summary["checked_rank_count"] == 1000
    assert summary["separated_rank_count"] == 1000
    assert summary["failure_count"] == 0
    assert summary["failure_ranks"] == []
    assert summary["first_unchecked_rank"] == 1001
    assert summary["transition_check_count"] == 1000
    assert summary["branch_counts"] == {"take": 490, "skip": 510}
    assert summary["minimum_margin"] == {
        "rank": 6,
        "value": {"numerator": 16307, "denominator": 32256},
    }
    assert summary["minimum_margin_on_open_hypothesis_range"] == {
        "rank": 7,
        "value": {
            "numerator": 1033253069,
            "denominator": 8193024,
        },
    }
    word_rows = data["branch_word_coverage"]["rows"]
    assert [
        (
            row["length"],
            row["possible_word_count"],
            row["observed_word_count"],
            row["missing_word_count"],
        )
        for row in word_rows
    ] == [
        (1, 2, 2, 0),
        (2, 4, 4, 0),
        (3, 8, 8, 0),
        (4, 16, 16, 0),
        (5, 32, 32, 0),
        (6, 64, 64, 0),
        (7, 128, 128, 0),
        (8, 256, 252, 4),
    ]
    assert word_rows[-1]["missing_words"] == [
        "SSSSTSTT",
        "SSSTTTST",
        "TSTSSTTS",
        "TTTSSSST",
    ]
    assert word_rows[6]["window_start_ranks"] == {
        "minimum": 1,
        "maximum": 994,
    }
    assert word_rows[7]["sample_window_count"] == 993
    assert [row["rank"] for row in data["checkpoints"]] == list(
        probe.CHECKPOINT_RANKS
    )
    assert all(row["separated"] for row in data["checkpoints"])
    assert any("does not prove" in limit for limit in data["limits"])
    assert any("rank 1001" in limit for limit in data["limits"])
    assert probe.OUTPUT.read_text(encoding="utf-8") == probe.render_measurement(
        data
    )


def test_nondefault_range_remains_explicit() -> None:
    data = probe.build_measurement(max_rank=40)
    assert data["parameters"]["checked_ranks"] == {
        "minimum": 1,
        "maximum": 40,
    }
    assert data["summary"]["failure_ranks"] == []
    assert data["summary"]["first_unchecked_rank"] == 41
    assert [row["rank"] for row in data["checkpoints"]][-1] == 20


def main() -> int:
    test_weights_and_small_exact_states()
    test_phase_recurrence_matches_direct_model()
    test_source_contract_rejects_formula_drift()
    test_default_measurement_and_artifact()
    test_nondefault_range_remains_explicit()
    print(
        "test_probe_second_channel_separation: source contract, exact "
        "recurrence, finite failure set, margins, branch counts, checkpoints, "
        "short branch-word coverage, and generated output verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
