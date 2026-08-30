#!/usr/bin/env python3
"""Keep the concrete cyclotomic-anchor family source-current and bounded.

Z73 records the generic prime-ray interfaces.  Z35 is the concrete X-2
specialisation and must therefore expose the declarations that actually
discharge its clean-order, layer-supply, and unbounded-support steps.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ZONE = ROOT / "docs" / "semantic" / "zones" / "Z35.json"
FRONTIER = ROOT / "docs" / "semantic" / "frontier.json"
ATLAS = ROOT / "docs" / "declaration_atlas.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def load(path: Path) -> dict:
    with path.open(encoding="utf-8") as stream:
        value = json.load(stream)
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def declaration_rows(atlas: dict) -> list[dict]:
    rows = atlas.get("declarations")
    require(isinstance(rows, list), "declaration atlas has no declarations list")
    return [row for row in rows if isinstance(row, dict)]


def test_concrete_clean_anchor_digest_is_source_current() -> None:
    zone = load(ZONE)
    atlas_rows = declaration_rows(load(ATLAS))
    node = next(
        (
            row
            for row in zone.get("statement_nodes", [])
            if isinstance(row, dict)
            and row.get("id") == "binary_cyclotomic_layers_supply_clean_cofinal_anchors"
        ),
        None,
    )
    require(node is not None, "Z35 lost the concrete cyclotomic-anchor statement node")

    expected = {
        "binaryCyclotomicLayer_dvd_mersenneLayer",
        "binaryCyclotomicLayer_prime_order_decomposition",
        "two_ne_zero_of_prime_dvd_binaryCyclotomicLayer",
        "prime_dvd_binaryCyclotomicLayer_clean_order",
        "exists_clean_binaryCyclotomicAnchor",
        "binaryCyclotomicLayer_layerSupply",
        "binaryCyclotomicLayer_eventualOrderConsumer",
        "binaryCyclotomicLayer_unboundedPrimeDivisorSupply",
        "cleanCyclotomicAnchorSupply_binaryCyclotomicLayer",
    }
    evidence = [row for row in node.get("evidence", []) if isinstance(row, dict)]
    by_name = {row.get("declaration"): row for row in evidence}
    require(
        expected <= set(by_name),
        "Z35 concrete anchor digest omits a clean-order/supply declaration: "
        + ", ".join(sorted(expected - set(by_name))),
    )

    atlas_by_name = {
        row.get("name"): row
        for row in atlas_rows
        if row.get("module") == "ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean"
    }
    for name in sorted(expected):
        row = by_name[name]
        current = atlas_by_name.get(name)
        require(current is not None, f"atlas lost source declaration {name}")
        require(
            row.get("module") == current.get("module")
            and row.get("line") == current.get("line"),
            f"stale Z35 source coordinate for {name}: "
            f"{row.get('line')} != {current.get('line')}",
        )

    statement = node.get("canonical_statement", "")
    caveat = node.get("scope_caveat", "")
    require("UnboundedPrimeDivisorSupply" in statement, "Z35 omits unbounded-support result")
    require("characteristic-prime" in statement, "Z35 omits clean-order exception mechanism")
    require("Z73" in caveat, "Z35 does not distinguish generic Z73 interfaces")
    require("carry" in caveat and "irrationality" in caveat, "Z35 scope boundary is incomplete")


def test_frontier_distinguishes_generic_socket_from_concrete_producer() -> None:
    frontier = load(FRONTIER)
    row = next(
        (
            candidate
            for candidate in frontier.get("open_antecedents", [])
            if isinstance(candidate, dict)
            and candidate.get("id") == "OA249-prime-ray-cyclotomic-sockets"
        ),
        None,
    )
    require(row is not None, "frontier lost the prime-ray cyclotomic socket row")
    require(
        row.get("closest_producer") == "binaryCyclotomicLayer_unboundedPrimeDivisorSupply",
        "frontier does not point the generic socket at the concrete X-2 producer",
    )
    gap = row.get("gap", "")
    require("generic interfaces remain conditional" in gap, "frontier erased generic boundary")
    require("Z35" in gap and "arithmetic anchors only" in gap, "frontier overclaims concrete supply")


if __name__ == "__main__":
    test_concrete_clean_anchor_digest_is_source_current()
    test_frontier_distinguishes_generic_socket_from_concrete_producer()
    print("cyclotomic semantic digest: ok")
