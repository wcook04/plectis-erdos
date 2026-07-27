#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the finite #249 certificate-supply measurement."""

from __future__ import annotations

from pathlib import Path

import probe_certificate_supply as probe


def test_totient_sieve() -> None:
    assert probe.totient_sieve(12) == [
        0, 1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4
    ]


def test_recurrence_matches_defining_sum() -> None:
    phi = probe.totient_sieve(80)
    for N, h in ((1, 1), (12, 8), (29, 5)):
        discrepancy = 0
        for depth in range(1, 24):
            discrepancy = (
                2 * discrepancy
                + phi[N + h + depth]
                - phi[N + depth]
            )
            assert discrepancy == probe.direct_window_discrepancy(
                phi, N, h, depth
            )


def test_checked_radius_is_the_larger_tail_not_the_sum() -> None:
    assert probe.omitted_tail_radius(12, 8, 16) == 38
    assert probe.omitted_tail_radius(12, 8, 16) != (38 + 30)


def test_admissible_depth_floor_matches_brute_small_cases() -> None:
    expected = {
        (0, 0): 4,
        (1, 0): 4,
        (1, 1): 5,
        (2, 2): 5,
        (6, 6): 6,
        (12, 8): 6,
        (120, 8): 9,
        (200, 1): 9,
    }
    for (N, h), depth in expected.items():
        assert probe.admissible_depth_floor(N, h) == depth

    for N in range(13):
        for h in range(9):
            depth = probe.admissible_depth_floor(N, h)
            assert (1 << depth) > 2 * probe.omitted_tail_radius(N, h, depth)
            if depth > 1:
                assert (1 << (depth - 1)) <= 2 * probe.omitted_tail_radius(
                    N, h, depth - 1
                )


def test_known_checked_fixture_and_minimality() -> None:
    phi = probe.totient_sieve(40)
    for h in range(1, 9):
        at_sixteen = probe.certificate_at_depth(
            probe.direct_window_discrepancy(phi, 12, h, 16),
            12,
            h,
            16,
        )
        assert at_sixteen["certified"] is True
        first = probe.minimum_certificate(phi, 12, h, 16)
        assert first is not None
        assert int(first["depth"]) <= 16


def test_failure_is_bounded_to_declared_depth_range() -> None:
    phi = probe.totient_sieve(10)
    row = probe.result_row(phi, 1, 1, 1)
    assert row == {
        "N": 1,
        "h": 1,
        "status": "failure_within_search_range",
        "searched_depths": {"minimum": 1, "maximum": 1},
        "admissible_depth_floor": 5,
        "excess_depth": None,
        "minimum_certificate": None,
    }


def test_exact_even_sample_median() -> None:
    assert probe.exact_median([8, 9, 10, 12]) == {
        "numerator": 19,
        "denominator": 2,
    }
    assert probe.exact_median([8, 10]) == {
        "numerator": 9,
        "denominator": 1,
    }


def test_excess_depth_summary_uses_exact_rationals() -> None:
    assert probe.excess_depth_summary([0, 0, 1, 3]) == {
        "sample_size": 4,
        "minimum": 0,
        "median": {"numerator": 1, "denominator": 2},
        "mean": {"numerator": 1, "denominator": 1},
        "maximum": 3,
        "distribution": [
            {
                "excess_depth": 0,
                "count": 2,
                "proportion": {"numerator": 1, "denominator": 2},
            },
            {
                "excess_depth": 1,
                "count": 1,
                "proportion": {"numerator": 1, "denominator": 4},
            },
            {
                "excess_depth": 3,
                "count": 1,
                "proportion": {"numerator": 1, "denominator": 4},
            },
        ],
    }


def test_lcm_prefix_sequence_retains_repeated_scales() -> None:
    assert probe.lcm_prefix_scales(16) == [
        1,
        2,
        6,
        12,
        60,
        60,
        420,
        840,
        2520,
        2520,
        27720,
        27720,
        360360,
        360360,
        360360,
        720720,
    ]


def test_lcm_diagonal_rows_are_exact_and_duplicate_aware() -> None:
    scales = probe.lcm_prefix_scales(16)
    phi = probe.totient_sieve(2 * scales[-1] + 400)
    rows = probe.lcm_diagonal_rows(phi, 16, 400)

    assert [row["t"] for row in rows] == list(range(1, 17))
    assert [row["lcm_1_to_t"] for row in rows] == scales
    assert [row["N"] for row in rows] == scales
    assert [row["h"] for row in rows] == scales
    assert [row["first_occurrence_t"] for row in rows] == [
        1, 2, 3, 4, 5, 5, 7, 8, 9, 9, 11, 11, 13, 13, 13, 16
    ]
    assert [
        row["t"] for row in rows if not row["is_new_scale"]
    ] == [6, 10, 12, 14, 15]
    assert all(row["status"] == "success" for row in rows)
    assert [
        row["minimum_certificate"]["depth"] for row in rows
    ] == [6, 5, 7, 7, 9, 9, 14, 15, 14, 14, 21, 21, 22, 22, 22, 23]
    assert [row["admissible_depth_floor"] for row in rows] == [
        5, 5, 6, 7, 9, 9, 11, 12, 14, 14, 17, 17, 21, 21, 21, 22
    ]
    assert [row["excess_depth"] for row in rows] == [
        1, 0, 1, 0, 0, 0, 3, 3, 0, 0, 4, 4, 1, 1, 1, 1
    ]


def test_default_measurement_and_generated_artifact_are_reproducible() -> None:
    data = probe.build_measurement()
    assert data["schema"] == "erdos249257-certificate-supply-probe/3"
    assert data["parameters"]["grid"] == {
        "N": {"minimum": 1, "maximum": 120},
        "h": {"minimum": 1, "maximum": 8},
    }
    assert data["parameters"]["searched_depths"] == {
        "minimum": 1,
        "maximum": 400,
    }
    assert data["parameters"]["spot_probes"] == {
        "h": 1,
        "N": [200, 500, 1000, 2000, 5000],
    }
    assert data["parameters"]["lcm_diagonal"]["t"] == {
        "minimum": 1,
        "maximum": 16,
    }
    assert data["parameters"]["totient_sieve_limit"] == 1441840
    assert len(data["pairs"]) == 960
    assert len(data["summary"]["per_h"]) == 8
    assert len(data["spot_probes"]) == 5
    assert data["summary"]["successes"] == 960
    assert data["summary"]["failures"] == 0
    assert [
        (
            row["minimum_depth"],
            row["median_depth"],
            row["maximum_depth"],
        )
        for row in data["summary"]["per_h"]
    ] == [
        (5, {"numerator": 9, "denominator": 1}, 13),
        (5, {"numerator": 9, "denominator": 1}, 18),
        (5, {"numerator": 9, "denominator": 1}, 19),
        (6, {"numerator": 9, "denominator": 1}, 15),
        (6, {"numerator": 9, "denominator": 1}, 14),
        (6, {"numerator": 9, "denominator": 1}, 16),
        (6, {"numerator": 9, "denominator": 1}, 12),
        (6, {"numerator": 9, "denominator": 1}, 17),
    ]
    assert [
        row["minimum_certificate"]["depth"] for row in data["spot_probes"]
    ] == [9, 13, 18, 15, 14]
    assert [
        row["admissible_depth_floor"] for row in data["spot_probes"]
    ] == [9, 11, 11, 12, 14]
    assert [
        row["excess_depth"] for row in data["spot_probes"]
    ] == [0, 2, 7, 3, 0]
    for row in [*data["pairs"], *data["spot_probes"]]:
        if row["status"] == "success":
            assert row["excess_depth"] >= 0
            assert row["minimum_certificate"]["depth"] == (
                row["admissible_depth_floor"] + row["excess_depth"]
            )

    rectangle_excess = data["summary"]["excess_depth"]
    assert {
        key: rectangle_excess[key]
        for key in ("sample_size", "minimum", "median", "mean", "maximum")
    } == {
        "sample_size": 960,
        "minimum": 0,
        "median": {"numerator": 1, "denominator": 1},
        "mean": {"numerator": 727, "denominator": 480},
        "maximum": 11,
    }
    assert [
        (row["excess_depth"], row["count"], row["proportion"])
        for row in rectangle_excess["distribution"]
    ] == [
        (0, 257, {"numerator": 257, "denominator": 960}),
        (1, 340, {"numerator": 17, "denominator": 48}),
        (2, 186, {"numerator": 31, "denominator": 160}),
        (3, 82, {"numerator": 41, "denominator": 480}),
        (4, 43, {"numerator": 43, "denominator": 960}),
        (5, 26, {"numerator": 13, "denominator": 480}),
        (6, 9, {"numerator": 3, "denominator": 320}),
        (7, 6, {"numerator": 1, "denominator": 160}),
        (8, 5, {"numerator": 1, "denominator": 192}),
        (9, 3, {"numerator": 1, "denominator": 320}),
        (10, 2, {"numerator": 1, "denominator": 480}),
        (11, 1, {"numerator": 1, "denominator": 960}),
    ]
    assert data["lcm_diagonal"]["summary"] == {
        "tested_t": 16,
        "distinct_scales": 11,
        "repeated_t": [6, 10, 12, 14, 15],
        "success_rows": 16,
        "failure_rows": 0,
        "failure_t": [],
        "distinct_scale_failures": 0,
        "failure_scales": [],
        "minimum_depth": 5,
        "maximum_depth": 23,
        "excess_depth_indexed_t": {
            "sample_size": 16,
            "minimum": 0,
            "median": {"numerator": 1, "denominator": 1},
            "mean": {"numerator": 5, "denominator": 4},
            "maximum": 4,
            "distribution": [
                {
                    "excess_depth": 0,
                    "count": 6,
                    "proportion": {"numerator": 3, "denominator": 8},
                },
                {
                    "excess_depth": 1,
                    "count": 6,
                    "proportion": {"numerator": 3, "denominator": 8},
                },
                {
                    "excess_depth": 3,
                    "count": 2,
                    "proportion": {"numerator": 1, "denominator": 8},
                },
                {
                    "excess_depth": 4,
                    "count": 2,
                    "proportion": {"numerator": 1, "denominator": 8},
                },
            ],
        },
        "excess_depth_distinct_scales": {
            "sample_size": 11,
            "minimum": 0,
            "median": {"numerator": 1, "denominator": 1},
            "mean": {"numerator": 14, "denominator": 11},
            "maximum": 4,
            "distribution": [
                {
                    "excess_depth": 0,
                    "count": 4,
                    "proportion": {"numerator": 4, "denominator": 11},
                },
                {
                    "excess_depth": 1,
                    "count": 4,
                    "proportion": {"numerator": 4, "denominator": 11},
                },
                {
                    "excess_depth": 3,
                    "count": 2,
                    "proportion": {"numerator": 2, "denominator": 11},
                },
                {
                    "excess_depth": 4,
                    "count": 1,
                    "proportion": {"numerator": 1, "denominator": 11},
                },
            ],
        },
    }
    assert len(data["lcm_diagonal"]["rows"]) == 16
    for row in data["lcm_diagonal"]["rows"]:
        if row["status"] == "success":
            assert row["excess_depth"] >= 0
            assert row["minimum_certificate"]["depth"] == (
                row["admissible_depth_floor"] + row["excess_depth"]
            )
    assert any("LCM-diagonal" in limit for limit in data["limits"])
    assert any("stops at t=16" in limit for limit in data["limits"])
    assert any("11 distinct scales" in limit for limit in data["limits"])
    assert any("Raw certificate depth" in limit for limit in data["limits"])
    assert any("equidistribution" in limit for limit in data["limits"])
    assert any("cofinal" in limit for limit in data["limits"])

    output = Path(probe.OUTPUT)
    assert output.read_text(encoding="utf-8") == probe.render_measurement(data)


def main() -> int:
    test_totient_sieve()
    test_recurrence_matches_defining_sum()
    test_checked_radius_is_the_larger_tail_not_the_sum()
    test_admissible_depth_floor_matches_brute_small_cases()
    test_known_checked_fixture_and_minimality()
    test_failure_is_bounded_to_declared_depth_range()
    test_exact_even_sample_median()
    test_excess_depth_summary_uses_exact_rationals()
    test_lcm_prefix_sequence_retains_repeated_scales()
    test_lcm_diagonal_rows_are_exact_and_duplicate_aware()
    test_default_measurement_and_generated_artifact_are_reproducible()
    print(
        "test_probe_certificate_supply: arithmetic, radius, admissibility "
        "floors, excess distributions, minima, bounded failures, LCM "
        "diagonal, and generated output verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
