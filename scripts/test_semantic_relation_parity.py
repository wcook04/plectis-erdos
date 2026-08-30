#!/usr/bin/env python3
"""Focused order-neutral checks for semantic relation projection parity."""

from __future__ import annotations

from copy import deepcopy
import json
import subprocess
from pathlib import Path

import check_semantic_corpus as checker


ROOT = Path(__file__).resolve().parents[1]


def committed_json(path: str) -> dict:
    return json.loads(
        subprocess.check_output(["git", "show", f"HEAD:{path}"], cwd=ROOT, text=True)
    )


def committed_relation_sources() -> tuple[list[tuple[str, dict]], list[tuple[str, dict]]]:
    paths = subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", "HEAD", "--", "docs/semantic"],
        cwd=ROOT,
        text=True,
    ).splitlines()
    zones = [
        (path, committed_json(path))
        for path in paths
        if path.startswith("docs/semantic/zones/") and path.endswith(".json")
    ]
    relation_lenses = [
        (path, committed_json(path))
        for path in paths
        if path.startswith("docs/semantic/relations_") and path.endswith(".json")
    ]
    return zones, relation_lenses


def test_reordered_authored_sources_and_projection_preserve_parity() -> None:
    corpus = committed_json("docs/semantic_corpus.json")
    zones, relation_lenses = committed_relation_sources()
    assert checker.relation_parity_errors(corpus, zones=zones, relation_lenses=relation_lenses) == []

    reversed_zones = deepcopy(zones)
    reversed_lenses = deepcopy(relation_lenses)
    for _, zone in reversed_zones:
        zone["intra_zone_relations"].reverse()
    for _, lens in reversed_lenses:
        lens["edges"].reverse()
    reversed_zones.reverse()
    reversed_lenses.reverse()
    reversed_corpus = deepcopy(corpus)
    reversed_corpus["relations"].reverse()

    assert checker.relation_parity_errors(
        reversed_corpus, zones=reversed_zones, relation_lenses=reversed_lenses
    ) == []


def test_relation_basis_and_future_boundary_loss_fail_closed() -> None:
    corpus = committed_json("docs/semantic_corpus.json")
    zones, relation_lenses = committed_relation_sources()

    missing_basis = deepcopy(corpus)
    source_edge = next(
        edge
        for edge in missing_basis["relations"]
        if edge.get("scope") in {"intra_zone", "cross_zone"}
    )
    source_edge["basis"] = ""
    assert any(
        "omits" in error or "invents" in error
        for error in checker.relation_parity_errors(
            missing_basis, zones=zones, relation_lenses=relation_lenses
        )
    )

    missing_boundary = deepcopy(zones)
    zone = next(zone for _, zone in missing_boundary if zone["intra_zone_relations"])
    zone["intra_zone_relations"][0]["boundary"] = "Exact source boundary"
    assert any(
        "omits" in error
        for error in checker.relation_parity_errors(
            corpus, zones=missing_boundary, relation_lenses=relation_lenses
        )
    )
