#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused adversarial tests for the checked diagonal depth roster."""

from __future__ import annotations

from pathlib import Path
from tempfile import TemporaryDirectory
from typing import Callable

import build_checked_diagonal_depth_roster as roster


def expect_contract_error(action: Callable[[], object]) -> None:
    """Require ``action`` to reject a malformed source contract."""
    try:
        action()
    except roster.SourceContractError:
        return
    raise AssertionError("expected SourceContractError")


def test_lcm_scale_indices_and_plateaus_are_exact() -> None:
    rows = roster.lcm_scale_rows()
    assert [row["t"] for row in rows] == [
        1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27,
        29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64, 67, 71,
        73, 79, 81,
    ]
    assert len(rows) == 33
    assert rows[4] == {
        "t": 5,
        "period_lcm": 60,
        "plateau_max_t": 6,
    }
    assert rows[-1] == {
        "t": 81,
        "period_lcm": 97301577764381948734868316916891200,
        "plateau_max_t": 82,
    }


def test_admissibility_floor_is_minimal_on_small_and_large_scales() -> None:
    expected = {
        1: 5,
        2: 5,
        6: 6,
        60: 9,
        720720: 22,
        1182266884102822267511361600: 92,
        97301577764381948734868316916891200: 119,
    }
    for period, depth in expected.items():
        assert roster.admissible_depth_floor(period) == depth
        assert (1 << depth) > 2 * (2 * period + depth + 2)
        assert (1 << (depth - 1)) <= 2 * (
            2 * period + (depth - 1) + 2
        )


def test_certificate_parser_rejects_mismatch_and_malformed_depth() -> None:
    valid = """
theorem certifiedKill_diagonal_t7 :
    certifiedKill (periodLcm 7) (periodLcm 7) 14 := by
  exact witness
"""
    records = roster.parse_certificate_declarations(valid, "Valid.lean")
    assert [(row["t"], row["depth"]) for row in records] == [(7, 14)]
    assert records[0]["provenance"]["line"] == 2

    mismatched = """
theorem certifiedKill_diagonal_t7 :
    certifiedKill (periodLcm 7) (periodLcm 8) 14 := by
  exact witness
"""
    expect_contract_error(
        lambda: roster.parse_certificate_declarations(
            mismatched, "Mismatch.lean"
        )
    )

    malformed_depth = """
theorem certifiedKill_diagonal_t7 :
    certifiedKill (periodLcm 7) (periodLcm 7) (7 + 7) := by
  exact witness
"""
    expect_contract_error(
        lambda: roster.parse_certificate_declarations(
            malformed_depth, "Malformed.lean"
        )
    )

    expect_contract_error(
        lambda: roster.unique_by_t(
            [
                *records,
                *roster.parse_certificate_declarations(valid, "Copy.lean"),
            ],
            "certificate",
        )
    )


def test_minimality_parser_requires_all_smaller_depths() -> None:
    valid = """
theorem t7_minimal_depth :
    certifiedKill (periodLcm 7) (periodLcm 7) 14 ∧
      ∀ L : ℕ, L < 14 → ¬ certifiedKill
        (periodLcm 7) (periodLcm 7) L := by
  exact witness
"""
    records = roster.parse_minimality_declarations(valid, "Minimum.lean")
    assert [(row["t"], row["depth"]) for row in records] == [(7, 14)]

    inconsistent_bound = """
theorem t7_minimal_depth :
    certifiedKill (periodLcm 7) (periodLcm 7) 14 ∧
      ∀ L : ℕ, L < 13 → ¬ certifiedKill
        (periodLcm 7) (periodLcm 7) L := by
  exact witness
"""
    expect_contract_error(
        lambda: roster.parse_minimality_declarations(
            inconsistent_bound, "Inconsistent.lean"
        )
    )

    weakened = """
theorem t7_minimal_depth :
    certifiedKill (periodLcm 7) (periodLcm 7) 14 := by
  exact witness
"""
    expect_contract_error(
        lambda: roster.parse_minimality_declarations(
            weakened, "Weakened.lean"
        )
    )


def test_band_and_floor_parsers_reject_changed_statements() -> None:
    valid_band = """
theorem exists_diagonalKill_le_82 (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L := by
  exact witness
"""
    band = roster.parse_band_declaration(valid_band, "Band.lean")
    assert band["declaration"] == "exists_diagonalKill_le_82"

    wrong_band = valid_band.replace("ht : t ≤ 82", "ht : t ≤ 81")
    expect_contract_error(
        lambda: roster.parse_band_declaration(wrong_band, "WrongBand.lean")
    )

    valid_floor = """
theorem certifiedKill_depth_floor {h N L : ℕ}
    (hcert : certifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L := by
  exact witness
"""
    floor = roster.parse_depth_floor_declaration(
        valid_floor, "Floor.lean"
    )
    assert floor["declaration"] == "certifiedKill_depth_floor"

    wrong_floor = valid_floor.replace(
        "2 * (N + h + L + 2)", "4 * (N + h + L + 2)"
    )
    expect_contract_error(
        lambda: roster.parse_depth_floor_declaration(
            wrong_floor, "WrongFloor.lean"
        )
    )


def test_roster_validation_rejects_missing_extra_and_false_minimum() -> None:
    scale_t = [row["t"] for row in roster.lcm_scale_rows()]
    certificates = {
        t: {"t": t, "depth": t + 10, "provenance": {}}
        for t in scale_t
    }
    assert len(
        roster.validate_roster_indices(certificates, {}, roster.BAND_MAX_T)
    ) == 33

    missing = dict(certificates)
    missing.pop(29)
    expect_contract_error(
        lambda: roster.validate_roster_indices(
            missing, {}, roster.BAND_MAX_T
        )
    )

    extra = dict(certificates)
    extra[6] = {"t": 6, "depth": 20, "provenance": {}}
    expect_contract_error(
        lambda: roster.validate_roster_indices(
            extra, {}, roster.BAND_MAX_T
        )
    )

    false_minimum = {
        67: {"t": 67, "depth": certificates[67]["depth"] - 1}
    }
    expect_contract_error(
        lambda: roster.validate_roster_indices(
            certificates, false_minimum, roster.BAND_MAX_T
        )
    )


def test_stale_output_detection_is_byte_exact() -> None:
    rendered = '{"schema":"fixture"}\n'
    with TemporaryDirectory() as directory:
        output = Path(directory) / "roster.json"
        assert roster.output_is_current(output, rendered) is False
        output.write_text(rendered + " ", encoding="utf-8")
        assert roster.output_is_current(output, rendered) is False
        output.write_text(rendered, encoding="utf-8")
        assert roster.output_is_current(output, rendered) is True


def test_default_roster_and_generated_artifact_are_reproducible() -> None:
    data = roster.build_measurement()
    assert data["schema"] == (
        "erdos249257-checked-diagonal-depth-roster/1"
    )
    assert data["parameters"] == {
        "t": {"minimum": 1, "maximum": 82},
        "one_row_per": "distinct periodLcm scale",
        "admissibility_floor": (
            "min {L>=1 : 2^L > 2*(2*periodLcm(t)+L+2)}"
        ),
    }
    assert data["summary"]["covered_positive_t"] == 82
    assert data["summary"]["distinct_lcm_scales"] == 33
    assert data["summary"]["checked_working_depth_rows"] == 33
    assert data["summary"]["proved_exact_least_depth_rows"] == 5
    assert data["summary"]["working_depth_only_rows"] == 28
    assert data["summary"]["exact_least_depth_t"] == [67, 71, 73, 79, 81]

    rows = data["rows"]
    assert [row["checked_working_depth"] for row in rows] == [
        6, 5, 7, 7, 9, 14, 15, 14, 21, 22, 23, 26, 32, 35, 38,
        40, 45, 49, 50, 56, 61, 66, 73, 76, 81, 88, 94, 93, 100,
        105, 113, 120, 120,
    ]
    assert [row["arithmetic_admissibility_floor"] for row in rows] == [
        5, 5, 6, 7, 9, 11, 12, 14, 17, 21, 22, 26, 30, 35, 37,
        39, 44, 49, 50, 55, 60, 66, 71, 74, 80, 86, 91, 92, 98,
        105, 111, 117, 119,
    ]
    assert [row["checked_working_depth_excess"] for row in rows] == [
        1, 0, 1, 0, 0, 3, 3, 0, 4, 1, 1, 0, 2, 0, 1, 1, 1,
        0, 0, 1, 1, 0, 2, 2, 1, 2, 3, 1, 2, 0, 2, 3, 1,
    ]
    assert sum(
        row["proved_least_depth"] is not None for row in rows
    ) == 5
    for row in rows:
        exact = row["proved_least_depth"] is not None
        assert (
            row["checked_working_depth_excess_status"]
            == (
                "proved_exact_least_depth_excess"
                if exact
                else "upper_bound_on_least_depth_excess"
            )
        )
        if exact:
            assert row["least_depth_excess_upper_bound"] is None
            assert (
                row["proved_least_depth_excess"]
                == row["checked_working_depth_excess"]
            )
            assert row["provenance"]["least_depth"] is not None
        else:
            assert row["proved_least_depth_excess"] is None
            assert (
                row["least_depth_excess_upper_bound"]
                == row["checked_working_depth_excess"]
            )
            assert row["provenance"]["least_depth"] is None

    all_summary = data["summary"][
        "checked_working_depth_excess_all_rows"
    ]
    assert {
        key: all_summary[key]
        for key in ("sample_size", "minimum", "median", "mean", "maximum")
    } == {
        "sample_size": 33,
        "minimum": 0,
        "median": {"numerator": 1, "denominator": 1},
        "mean": {"numerator": 40, "denominator": 33},
        "maximum": 4,
    }
    assert [
        (entry["excess"], entry["count"]) for entry in all_summary["distribution"]
    ] == [(0, 10), (1, 12), (2, 6), (3, 4), (4, 1)]

    exact_summary = data["summary"]["proved_exact_least_depth_excess"]
    assert {
        key: exact_summary[key]
        for key in ("sample_size", "minimum", "median", "mean", "maximum")
    } == {
        "sample_size": 5,
        "minimum": 0,
        "median": {"numerator": 2, "denominator": 1},
        "mean": {"numerator": 8, "denominator": 5},
        "maximum": 3,
    }

    upper_summary = data["summary"][
        "working_depth_only_excess_upper_bounds"
    ]
    assert {
        key: upper_summary[key]
        for key in ("sample_size", "minimum", "median", "mean", "maximum")
    } == {
        "sample_size": 28,
        "minimum": 0,
        "median": {"numerator": 1, "denominator": 1},
        "mean": {"numerator": 8, "denominator": 7},
        "maximum": 4,
    }

    t64 = next(row for row in rows if row["scale_index_t"] == 64)
    assert t64["provenance"]["working_certificate"]["source_path"] == (
        "Erdos249257/DiagonalPincerCertificateT64Endpoint.lean"
    )
    assert len(data["source_contract"]["source_inventory"]) == 21
    assert all(
        item["source_sha256"].startswith("sha256:")
        for item in data["source_contract"]["source_inventory"]
    )
    assert any("t=83" in limit for limit in data["limits"])
    assert any("upper bound" in limit for limit in data["limits"])
    assert any("cofinal" in limit for limit in data["limits"])

    output = Path(roster.OUTPUT)
    assert output.read_text(encoding="utf-8") == roster.render_measurement(
        data
    )


def main() -> int:
    test_lcm_scale_indices_and_plateaus_are_exact()
    test_admissibility_floor_is_minimal_on_small_and_large_scales()
    test_certificate_parser_rejects_mismatch_and_malformed_depth()
    test_minimality_parser_requires_all_smaller_depths()
    test_band_and_floor_parsers_reject_changed_statements()
    test_roster_validation_rejects_missing_extra_and_false_minimum()
    test_stale_output_detection_is_byte_exact()
    test_default_roster_and_generated_artifact_are_reproducible()
    print(
        "test_checked_diagonal_depth_roster: source signatures, malformed "
        "inputs, exact minima, upper-bound labels, stale output, and "
        "generated roster verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
