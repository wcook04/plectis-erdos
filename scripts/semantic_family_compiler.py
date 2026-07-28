#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Compile exact source-structural proposition families for semantic coverage.

The authored semantic zones deliberately carry only proposition-level readings
that somebody actually wrote and bounded.  That remains the high tier.  It
cannot, however, be the only node-linking mechanism in a corpus with more than
one hundred thousand theorem declarations, most of them repetitive certificate
arithmetic.

This module supplies the exhaustive lower tier.  It never paraphrases a theorem
from its name and never treats lexical similarity as mathematical equivalence.
Instead it groups otherwise-unlinked theorem/lemma declarations only when they
share:

* the exact source module; and
* the same normalized Lean proposition signature after removing the declaration
  name and abstracting literal numerals.

Every family node retains every exact declaration id and source coordinate as
evidence; the declaration atlas remains authority for each un-normalized
signature.  The resulting link means "member of this source proposition
schema", not "reviewed mathematical interpretation".
"""

from __future__ import annotations

import hashlib
import re
from collections import defaultdict
from typing import Any, Iterable, Mapping

THEOREM_LIKE_KINDS = frozenset({"theorem", "lemma"})
INTERPRETATION_TIER = "source_structural_family"

_DECLARATION_PREFIX = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma)\s+[^\s:({\[]+\s*"
)
_NUMERAL = re.compile(r"(?<![A-Za-z_])(?:0x[0-9A-Fa-f]+|\d+)(?![A-Za-z_])")
_WHITESPACE = re.compile(r"\s+")


def normalized_proposition_signature(signature: str) -> str:
    """Return the exact proposition schema with name and numerals abstracted."""
    body = _DECLARATION_PREFIX.sub("", signature.strip(), count=1)
    body = _NUMERAL.sub("<num>", body)
    return _WHITESPACE.sub(" ", body).strip()


def problem_for_module(module: str) -> str:
    """Infer only explicit repository problem namespaces, never fuzzy labels."""
    for problem in ("243", "249", "251", "257", "269", "1049"):
        if re.search(rf"(?:^|/)Erdos{problem}(?:/|\.lean$)", module):
            return problem
    return "shared_substrate"


def family_id(module: str, signature_template: str) -> str:
    digest = hashlib.sha256(
        f"{module}\0{signature_template}".encode("utf-8")
    ).hexdigest()[:20]
    return f"structural::{digest}"


def _evidence(row: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "id": row["id"],
        "resolved": True,
    }


def compile_source_structural_families(
    atlas_rows: Iterable[Mapping[str, Any]],
    existing_roles: Mapping[str, Mapping[str, Any]],
    existing_direct_evidence_ids: Iterable[str] = (),
) -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]]]:
    """Return exhaustive lower-tier nodes and role replacements.

    Existing statement-node assignments are authoritative and excluded.  An
    existing zone-only role is upgraded by copying it and attaching the
    structural node, so its authored zone and declaration-role classification
    remain visible.
    """
    direct_ids = frozenset(existing_direct_evidence_ids)
    groups: dict[tuple[str, str], list[Mapping[str, Any]]] = defaultdict(list)
    for row in atlas_rows:
        if row.get("generated_certificate"):
            continue
        if row.get("kind") not in THEOREM_LIKE_KINDS:
            continue
        existing = existing_roles.get(str(row["id"]))
        if row["id"] in direct_ids:
            continue
        template = normalized_proposition_signature(str(row.get("signature", "")))
        groups[(str(row["module"]), template)].append(row)

    nodes: list[dict[str, Any]] = []
    role_updates: dict[str, dict[str, Any]] = {}
    for (module, template), members in sorted(groups.items()):
        members = sorted(members, key=lambda row: (int(row["line"]), str(row["name"])))
        node_id = family_id(module, template)
        docstrings = [
            str(row["docstring"]).strip()
            for row in members
            if str(row.get("docstring") or "").strip()
        ]
        documented_singleton = len(members) == 1 and len(docstrings) == 1
        if documented_singleton:
            canonical = f"SOURCE-DOCUMENTED: {docstrings[0]}"
        else:
            canonical = (
                "SOURCE-STRUCTURAL FAMILY: "
                f"{len(members)} theorem/lemma declaration(s) in `{module}` "
                "share the normalized Lean proposition schema "
                f"`{template}`."
            )
        nodes.append(
            {
                "id": node_id,
                "canonical_statement": canonical,
                "logical_class": "infrastructure",
                "problem": problem_for_module(module),
                "evidence": [_evidence(row) for row in members],
                "concepts": [],
                "open_antecedents": [],
                "is_restatement_of_open_problem": False,
                "engine": "exact Lean proposition-signature normalization",
                "prior_art_state": "not_assessed",
                "prior_art_note": (
                    "No mathematical priority assessment is inferred by the "
                    "structural compiler."
                ),
                "scope_caveat": (
                    "This machine-derived family proves exact source linkage and "
                    "shared proposition shape only. It is not a reviewed "
                    "mathematical paraphrase, a novelty claim, or evidence that "
                    "different family members are logically equivalent."
                ),
                "confidence": "high",
                "interpretation_tier": INTERPRETATION_TIER,
                "source_module": module,
                "signature_template": template,
                "member_count": len(members),
                "source_documented_singleton": documented_singleton,
                "zone": "structural",
            }
        )
        for row in members:
            prior = dict(existing_roles.get(str(row["id"]), {}))
            if prior.get("statement_node"):
                # The authored contextual route remains authoritative.  This
                # declaration is still exact evidence for the lower-tier
                # structural family, closing the audit dimension without
                # demoting its higher-value navigation link.
                continue
            prior.update(
                {
                    "declaration": row["name"],
                    "module": module,
                    "role": prior.get("role", "statement"),
                    "statement_node": node_id,
                    "zone": prior.get("zone", "structural"),
                    "routing_origin": INTERPRETATION_TIER,
                    "routing_basis": (
                        "Exact source module plus normalized Lean proposition "
                        "signature; no lexical semantic inference."
                    ),
                    "interpretation_tier": INTERPRETATION_TIER,
                }
            )
            role_updates[str(row["id"])] = prior
    return nodes, role_updates
