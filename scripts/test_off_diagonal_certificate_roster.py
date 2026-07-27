#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the bounded off-diagonal certificate roster."""

from __future__ import annotations

from pathlib import Path

import build_off_diagonal_certificate_roster as roster


def _fixture_row(
    source_row: int,
    *,
    N: int,
    h: int = 1,
    L: int = 10,
    kill: bool = True,
    lean_verified: bool = True,
) -> dict[str, object]:
    return {
        "source_row": source_row,
        "source_line_sha256": f"hash-{source_row}",
        "record": {
            "N": N,
            "h": h,
            "L": L,
            "kill": kill,
            "lean_verified": lean_verified,
            "file": "Example.lean" if lean_verified else "",
        },
    }


def test_selection_uses_both_flags_and_the_inclusive_cutoff() -> None:
    cutoff = roster.HISTORICAL_AUDIT_CUTOFF_N
    rows = [
        _fixture_row(1, N=cutoff - 1),
        _fixture_row(2, N=cutoff),
        _fixture_row(3, N=cutoff + 1),
        _fixture_row(4, N=cutoff - 2, kill=False),
        _fixture_row(5, N=cutoff - 3, lean_verified=False),
    ]
    selected, excluded = roster.select_historical_rows(rows)
    assert [row["source_row"] for row in selected] == [1, 2]
    assert [row["source_row"] for row in excluded] == [3]


def test_public_signature_extraction_uses_lean_h_N_L_order() -> None:
    source = """\
private theorem hidden : certifiedKill 9 8 7 := by
  trivial

theorem publicOne :
    certifiedKill 2 300 41 := by
  trivial

theorem publicTwo : certifiedKill 5 700 43 := by
  trivial
"""
    signatures = roster.extract_public_certified_kills(
        source, "Fixture.lean"
    )
    assert [
        (
            row["declaration"],
            row["line"],
            row["arguments"],
            row["signature"],
        )
        for row in signatures
    ] == [
        (
            "publicOne",
            4,
            {"h": 2, "N": 300, "L": 41},
            "certifiedKill 2 300 41",
        ),
        (
            "publicTwo",
            8,
            {"h": 5, "N": 700, "L": 43},
            "certifiedKill 5 700 43",
        ),
    ]


def test_live_roster_counts_signatures_and_duplicate_groups() -> None:
    data = roster.build_roster()
    assert data["schema"] == (
        "erdos249257-off-diagonal-certificate-roster/1"
    )
    assert data["parameter_contract"]["data_field_order"] == [
        "N", "h", "L"
    ]
    assert data["parameter_contract"][
        "lean_certifiedKill_argument_order"
    ] == ["h", "N", "L"]
    assert data["counts"] == {
        "row_count": 125,
        "distinct_h_N_L_certificate_count": 123,
        "distinct_file_count": 122,
        "distinct_public_theorem_reference_count": 123,
        "duplicate_group_count": 2,
        "duplicate_row_count": 4,
        "duplicate_excess_row_count": 2,
    }
    assert len(data["source_rows"]) == 125
    assert len(data["distinct_certificates"]) == 123
    assert len(data["lean_files"]) == 122
    assert data["projection_contract"]["owner"] == (
        "docs/measurements/off_diagonal_certificate_roster.json"
    )
    assert all(
        certificate["h"] != certificate["N"]
        for certificate in data["distinct_certificates"]
    )

    assert [
        (
            group["source_files"],
            group["source_rows"],
            group["duplicate_key"],
        )
        for group in data["duplicate_certificate_groups"]
    ] == [
        (
            ["ErdosProblems/FreePosition/FreeKill59Root.lean"],
            [531, 535],
            {
                "h": 1,
                "N": 9690712164777231700912799,
                "L": 88,
            },
        ),
        (
            ["ErdosProblems/FreePosition/FreeKill64ForwardRoot.lean"],
            [712, 716],
            {
                "h": 1,
                "N": 2364533768205644535022723200,
                "L": 94,
            },
        ),
    ]

    for certificate in data["distinct_certificates"]:
        expected = {
            "h": certificate["h"],
            "N": certificate["N"],
            "L": certificate["L"],
        }
        assert certificate["theorems"]
        for theorem in certificate["theorems"]:
            assert theorem["arguments"] == expected
            assert theorem["argument_order"] == ["h", "N", "L"]
            assert theorem["line"] > 0
            assert theorem["declaration"].startswith("freeKill_")

    excluded = data["excluded_later_verified_rows"]
    assert excluded["row_count"] == 54
    assert excluded["distinct_h_N_L_certificate_count"] == 54
    assert excluded["distinct_file_count"] == 54
    assert excluded["minimum_N"] > roster.HISTORICAL_AUDIT_CUTOFF_N
    assert "historical Z27 cutoff" in excluded["policy"]


def test_depth_root_file_matches_two_distinct_public_signatures() -> None:
    data = roster.build_roster()
    depth_root = [
        certificate
        for certificate in data["distinct_certificates"]
        if certificate["source_files"] == [
            "ErdosProblems/FreePosition/FreeKill64DepthRoot.lean"
        ]
    ]
    assert [
        (
            certificate["L"],
            certificate["theorems"][0]["declaration"],
            certificate["theorems"][0]["line"],
        )
        for certificate in depth_root
    ] == [
        (92, "freeKill_64Depth1", 48),
        (93, "freeKill_64Depth2", 75),
    ]


def test_generated_artifact_is_reproducible() -> None:
    first = roster.build_roster()
    second = roster.build_roster()
    assert first == second
    rendered = roster.render_roster(first)
    assert rendered == roster.render_roster(second)
    assert Path(roster.OUTPUT).read_text(encoding="utf-8") == rendered


def test_public_projection_distinguishes_rows_and_certificates() -> None:
    data = roster.build_roster()
    statement = roster.public_projection_statement(data)
    caveat = roster.public_projection_scope_caveat(data)
    assert "123 distinct (h,N,L) triples" in statement
    assert "125 selected verification rows" in statement
    assert "2 rows duplicate" in statement
    assert "122 Lean files" in statement
    assert "54 later verified certificate triples" in caveat


def main() -> int:
    test_selection_uses_both_flags_and_the_inclusive_cutoff()
    test_public_signature_extraction_uses_lean_h_N_L_order()
    test_live_roster_counts_signatures_and_duplicate_groups()
    test_depth_root_file_matches_two_distinct_public_signatures()
    test_generated_artifact_is_reproducible()
    test_public_projection_distinguishes_rows_and_certificates()
    print(
        "test_off_diagonal_certificate_roster: selection, Lean-order "
        "signature matching, duplicate groups, counts, coordinates, and "
        "generated output verified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
