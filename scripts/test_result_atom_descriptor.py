#!/usr/bin/env python3
"""Focused read-only tests for result population in the corpus descriptor."""

from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import build_corpus_descriptor as descriptor


ROOT = Path(__file__).resolve().parents[1]


def test_result_population_is_dynamic_and_complete() -> None:
    packet = descriptor.build()
    population = packet["result_population"]
    atoms = [
        json.loads(line)
        for line in (ROOT / "docs" / "result-atoms.jsonl")
        .read_text(encoding="utf-8")
        .splitlines()
        if line.strip()
    ]
    palomar_order = json.loads(
        (ROOT / "docs" / "PALOMAR_RESULT_SHOWCASE.json").read_text(
            encoding="utf-8"
        )
    )["family_display_order"]
    assert population["atom_count"] == len(atoms)
    assert population["family_count"] == len(palomar_order)
    assert sum(population["interpretation_state_counts"].values()) == len(atoms)
    assert sum(population["display_tier_counts"].values()) == len(atoms)
    family_order = population["qualitative_family_order"]
    assert family_order["columns"] == [
        "family_id",
        "problem_id",
        "display_band",
        "editorial_disposition",
    ]
    assert [row[0] for row in family_order["rows"]] == [
        row["family_id"] for row in palomar_order
    ]


def test_routes_and_authority_boundaries_are_explicit() -> None:
    packet = descriptor.build()
    population = packet["result_population"]
    assert population["atom_query"].endswith("--result-atom <atom_id>")
    assert population["family_query"].endswith("--family-atoms <family_id>")
    assert population["family_order_authority"].endswith("::family_display_order")
    assert "not establish proof" in population["authority_boundary"]
    assert packet["access"]["schema"] == "plectis-public-corpus-access/1"
    assert packet["capabilities"]["exact_result_atom_lookup"] is True


def test_descriptor_remains_inside_registration_envelope() -> None:
    assert len(descriptor.render().encode("utf-8")) <= descriptor.DESCRIPTOR_MAX_BYTES


def test_orientation_omits_recoverable_claim_coordinates_with_receipt() -> None:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    atlas = json.loads(
        (ROOT / "docs" / "declaration_atlas.json").read_text(encoding="utf-8")
    )
    orientation = descriptor.build_orientation(claims, atlas)
    expected = [
        {"id": row["id"], "status": row["status"]}
        for row in claims["claims"]
        if row.get("readme_headline")
    ]
    assert orientation["principal_claims"] == expected
    receipt = orientation["principal_claim_detail_omission"]
    assert receipt["owner"] == "docs/claims.json::claims"
    assert receipt["query"].endswith("--claim <claim_id>")
    assert set(receipt["omitted_fields"]) == {
        "paper_label",
        "remaining_open_proposition_ids",
    }
    encoded = (
        json.dumps(orientation, ensure_ascii=False, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    assert len(encoded) <= descriptor.ORIENTATION_MAX_BYTES


def test_orientation_compacts_growing_paper_and_signal_detail() -> None:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    atlas = json.loads(
        (ROOT / "docs" / "declaration_atlas.json").read_text(encoding="utf-8")
    )
    orientation = descriptor.build_orientation(claims, atlas)
    architecture = orientation["editorial_architecture"]
    source_companions = claims["machine_readable_paper"]["publication_assembly"][
        "publication_architecture"
    ]["retained_companions"]
    assert architecture["retained_companion_count"] == len(source_companions)
    assert architecture["retained_companion_problem_ids"] == [
        row["id"].removesuffix("_reasoning_record") for row in source_companions
    ]
    assert architecture["full_detail"]["query"].endswith(
        "--publication-architecture"
    )

    presentation = orientation["mathematical_signal_presentation"]
    source_contract = json.loads(
        (ROOT / "docs" / "PALOMAR_RESULT_SHOWCASE.json").read_text(encoding="utf-8")
    )["selection_contract"]
    assert presentation["tiers"] == [
        {key: row[key] for key in ("order", "tier_id", "label")}
        for row in sorted(
            source_contract["presentation_tiers"], key=lambda row: row["order"]
        )
    ]
    assert presentation["relational_placements"] == [
        {
            "family_id": row["family_id"],
            "tier_id": row["tier_id"],
            "within_tier_order": row.get("within_tier_order"),
        }
        for row in source_contract["relational_placements"]
    ]
    assert presentation["full_detail"]["owner"].endswith("::selection_contract")
    assert len(
        (json.dumps(orientation, ensure_ascii=False, separators=(",", ":")) + "\n")
        .encode("utf-8")
    ) <= descriptor.ORIENTATION_MAX_BYTES - 2_000

    future_claims = deepcopy(claims)
    future_architecture = future_claims["machine_readable_paper"][
        "publication_assembly"
    ]["publication_architecture"]
    future_architecture["retained_companions"].append(
        {
            "id": "erdos_999_reasoning_record",
            "source": "paper/" + "future-detail-" * 500 + ".tex",
            "decision": "retain_as_full_problem_reasoning_record",
        }
    )
    future = descriptor.build_orientation(future_claims, atlas)
    future_encoded = (
        json.dumps(future, ensure_ascii=False, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    assert future["editorial_architecture"]["retained_companion_problem_ids"][-1] == (
        "erdos_999"
    )
    assert future["mathematical_signal_first"] == orientation[
        "mathematical_signal_first"
    ]
    assert b"future-detail" not in future_encoded
    assert len(future_encoded) <= descriptor.ORIENTATION_MAX_BYTES


def main() -> int:
    tests = (
        test_result_population_is_dynamic_and_complete,
        test_routes_and_authority_boundaries_are_explicit,
        test_descriptor_remains_inside_registration_envelope,
        test_orientation_omits_recoverable_claim_coordinates_with_receipt,
        test_orientation_compacts_growing_paper_and_signal_detail,
    )
    for test in tests:
        test()
    print(f"result atom descriptor: pass ({len(tests)} tests)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
