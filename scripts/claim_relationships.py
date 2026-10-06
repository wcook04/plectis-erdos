# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Resolve registry relationships without treating progress as an open target."""
from __future__ import annotations

from typing import Any


def resolve_claim_boundary(claim: dict[str, Any], claims: dict[str, Any]) -> dict[str, Any]:
    """Union forward and reverse links in stable order, retaining their kinds.

    Missing forward references are explicit registry inconsistencies. A progress
    claim's forward link need not equal the proposition's open target.
    """
    propositions = claims.get("remaining_open_propositions", [])
    index = {row["id"]: row for row in propositions}
    relationships: dict[str, list[str]] = {}
    inconsistencies = []

    def add(proposition_id: str, kind: str) -> None:
        kinds = relationships.setdefault(proposition_id, [])
        if kind not in kinds:
            kinds.append(kind)

    for proposition_id in claim.get("remaining_open_proposition_ids", []):
        add(proposition_id, "remaining_open_proposition_ids")
        if proposition_id not in index and not any(
            row["proposition_id"] == proposition_id for row in inconsistencies
        ):
            inconsistencies.append({
                "claim": claim.get("id"), "proposition_id": proposition_id,
                "status": "claim_references_unknown_open_proposition",
                "relation_kind": "remaining_open_proposition_ids",
            })
    known_claims = {row.get("id") for row in claims.get("claims", [])}
    for prop in propositions:
        if prop.get("open_target_claim") == claim.get("id"):
            add(prop["id"], "open_target_claim")
        if prop["id"] in relationships:
            target = prop.get("open_target_claim")
            if target and target not in known_claims:
                inconsistencies.append({
                    "claim": target, "proposition_id": prop["id"],
                    "status": "open_proposition_targets_unknown_claim",
                    "relation_kind": "open_target_claim",
                })
    return {
        "remaining_open": [index[key] for key in relationships if key in index],
        "remaining_open_relationships": [
            {"proposition_id": key, "relation_kinds": kinds}
            for key, kinds in relationships.items()
        ],
        "inconsistencies": inconsistencies,
    }


def audit_claim_relationships(claims: dict[str, Any]) -> list[dict[str, Any]]:
    """Check every forward reference and reverse target in the registry."""
    propositions = {row["id"] for row in claims.get("remaining_open_propositions", [])}
    known = {row.get("id") for row in claims.get("claims", [])}
    problems = []
    for claim in claims.get("claims", []):
        for proposition_id in dict.fromkeys(claim.get("remaining_open_proposition_ids", [])):
            if proposition_id not in propositions:
                problems.append({
                    "claim": claim.get("id"), "proposition_id": proposition_id,
                    "status": "claim_references_unknown_open_proposition",
                    "relation_kind": "remaining_open_proposition_ids",
                })
    for prop in claims.get("remaining_open_propositions", []):
        target = prop.get("open_target_claim")
        if target and target not in known:
            problems.append({
                "claim": target, "proposition_id": prop["id"],
                "status": "open_proposition_targets_unknown_claim",
                "relation_kind": "open_target_claim",
            })
    return problems
