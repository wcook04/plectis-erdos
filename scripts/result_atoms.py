#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Load and validate the committed public result-atom catalog.

The catalog reproduces source excerpts and their full-source digests.  It does
not claim to reproduce every complete packet statement, and its editorial
interpretations are not proof, novelty, significance, or peer-review authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
CATALOG_PATH = ROOT / "docs/result-atoms.jsonl"
CLAIMS_PATH = ROOT / "docs/claims.json"
FAMILY_DISPLAY_ORDER_PATH = ROOT / "docs/family-display-order.jsonl"
PALOMAR_PATH = ROOT / "docs/PALOMAR_RESULT_SHOWCASE.json"

DISPLAY_TIER_CLAIM_CEILING = (
    "Attention-routing label only; not novelty, significance, review, "
    "publication, or acceptance authority."
)
PRIVATE_PATH_MARKERS = (
    "/Users/",
    ".plectis-convergence",
    "v5-run/",
    "ai_workflow/",
    "formal_math/erdos257_period_noncollapse/",
)
SHA256_RE = re.compile(r"[0-9a-f]{64}")

BASE_KEYS = {
    "schema",
    "atom_id",
    "problem_id",
    "result_id",
    "family_id",
    "source_ordinal",
    "statement_excerpt",
    "statement_scope",
    "source_statement_sha256",
    "evidence_status",
    "display_tier",
    "display_tier_claim_ceiling",
    "interpretation_state",
}
DELEGATED_KEYS = BASE_KEYS | {"interpretation"}
CARD_KEYS = BASE_KEYS | {"reviewer_card_ids", "reviewer_card_availability"}
INTERPRETATION_KEYS = {
    "actor",
    "review_status",
    "result_class",
    "secondary_classes",
    "one_sentence_result",
    "why_it_matters",
    "mechanism_or_hard_step",
    "exact_boundary",
    "does_not_establish",
    "evidence_posture",
    "prior_art_posture",
    "next_open_obligation",
    "declaration_bindings",
}


def _load_jsonl_objects(source: Path) -> list[dict]:
    """Load JSONL objects, rejecting blank lines and non-object values."""
    rows: list[dict] = []
    for line_number, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            raise ValueError(f"{source}:{line_number}: blank JSONL row")
        try:
            row = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValueError(f"{source}:{line_number}: invalid JSON: {error}") from error
        if not isinstance(row, dict):
            raise ValueError(f"{source}:{line_number}: row is not an object")
        rows.append(row)
    return rows


def load_result_atoms(path: Path | None = None) -> list[dict]:
    """Load public result-atom rows."""
    return _load_jsonl_objects(path or CATALOG_PATH)


def load_family_display_order(path: Path | None = None) -> list[dict]:
    """Load the complete authored review-family display order.

    An explicit path still supports validating the generated public JSONL
    projection.  The default follows the Palomar source authority so atom
    validation does not depend on a prior projection build.
    """
    if path is not None:
        return _load_jsonl_objects(path)
    payload = json.loads(PALOMAR_PATH.read_text(encoding="utf-8"))
    rows = payload.get("family_display_order") if isinstance(payload, dict) else None
    if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
        raise ValueError(f"{PALOMAR_PATH}: family_display_order must be a list of objects")
    return rows


def _load_claims(claims: Any) -> dict[str, Any]:
    if claims is None:
        return json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    if isinstance(claims, Path):
        return json.loads(claims.read_text(encoding="utf-8"))
    if not isinstance(claims, dict):
        raise ValueError("claims must be a mapping, pathlib.Path, or None")
    return claims


def _public_families(
    claims: dict[str, Any],
) -> tuple[set[tuple[str, str]], list[str], list[str]]:
    try:
        matrix = claims["external_verification_packet"]["review_matrix"]
    except (KeyError, TypeError) as error:
        raise ValueError("claims lacks external_verification_packet.review_matrix") from error
    if not isinstance(matrix, list):
        raise ValueError("claims review_matrix must be a list")

    coordinates: list[tuple[str, str]] = []
    problem_ids: list[str] = []
    family_ids: list[str] = []
    for group_index, group in enumerate(matrix, 1):
        if not isinstance(group, dict):
            raise ValueError(f"claims review group {group_index}: must be an object")
        problem = group.get("problem")
        if isinstance(problem, bool) or not isinstance(problem, (int, str)) or not str(problem):
            raise ValueError(f"claims review group {group_index}: invalid problem id")
        problem_id = f"erdos_{problem}"
        if problem_id in problem_ids:
            raise ValueError(f"claims review_matrix repeats problem {problem_id}")
        problem_ids.append(problem_id)
        families = group.get("families")
        if not isinstance(families, list):
            raise ValueError(f"claims review group {problem_id}: families must be a list")
        for family_index, family in enumerate(families, 1):
            if not isinstance(family, dict):
                raise ValueError(
                    f"claims review group {problem_id} family {family_index}: must be an object"
                )
            family_id = family.get("id")
            if not isinstance(family_id, str) or not family_id:
                raise ValueError(
                    f"claims review group {problem_id} family {family_index}: invalid family id"
                )
            coordinates.append((problem_id, family_id))
            family_ids.append(family_id)

    if len(coordinates) != len(set(coordinates)):
        raise ValueError("claims review_matrix contains duplicate family coordinates")
    if len(family_ids) != len(set(family_ids)):
        raise ValueError("claims review_matrix family ids must be globally unique")
    return set(coordinates), problem_ids, family_ids


def _load_family_display_order(value: Any) -> list[dict]:
    if value is None:
        return load_family_display_order()
    if isinstance(value, Path):
        return load_family_display_order(value)
    if not isinstance(value, list) or not all(isinstance(row, dict) for row in value):
        raise ValueError("family_display_order must be a list of objects, pathlib.Path, or None")
    return value


def _validate_family_display_order(
    rows: list[dict], family_registry: set[tuple[str, str]]
) -> tuple[list[str], Counter[str], int]:
    coordinates: list[tuple[str, str]] = []
    family_ids: list[str] = []
    global_orders: list[int] = []
    within_problem_orders: dict[str, list[int]] = {}
    band_counts: Counter[str] = Counter()
    promotion_count = 0

    for index, row in enumerate(rows, 1):
        if row.get("schema") != "plectis.family-display-order/1":
            raise ValueError(f"family display row {index}: unsupported schema")
        problem_id = row.get("problem_id")
        family_id = row.get("family_id")
        if not isinstance(problem_id, str) or not isinstance(family_id, str):
            raise ValueError(f"family display row {index}: invalid family coordinate")
        coordinates.append((problem_id, family_id))
        family_ids.append(family_id)
        if row.get("object_key") != f"review-family:{problem_id}:{family_id}":
            raise ValueError(f"family display row {index}: object_key drifted")

        global_order = row.get("global_display_order")
        if isinstance(global_order, bool) or not isinstance(global_order, int):
            raise ValueError(f"family display row {index}: invalid global_display_order")
        global_orders.append(global_order)

        display_band = row.get("display_band")
        if not isinstance(display_band, dict):
            raise ValueError(f"family display row {index}: display_band must be an object")
        band = display_band.get("band")
        if not isinstance(band, str) or not band:
            raise ValueError(f"family display row {index}: invalid display band")
        band_counts[band] += 1
        within_order = display_band.get("within_problem_order")
        if isinstance(within_order, bool) or not isinstance(within_order, int):
            raise ValueError(f"family display row {index}: invalid within_problem_order")
        within_problem_orders.setdefault(problem_id, []).append(within_order)

        disposition = row.get("editorial_disposition")
        if not isinstance(disposition, str) or not disposition:
            raise ValueError(f"family display row {index}: invalid editorial disposition")
        promotion_count += disposition == "promote"

    if len(coordinates) != len(set(coordinates)) or len(family_ids) != len(set(family_ids)):
        raise ValueError("family display order contains duplicate families")
    if set(coordinates) != family_registry:
        missing = sorted(family_registry - set(coordinates))
        extra = sorted(set(coordinates) - family_registry)
        raise ValueError(
            "family display order does not exactly match claims review families: "
            f"missing={missing}, extra={extra}"
        )
    expected_global_orders = list(range(1, len(rows) + 1))
    if global_orders != expected_global_orders:
        raise ValueError(
            f"family display global order must be contiguous 1..{len(rows)} in JSONL order"
        )
    for problem_id, observed in within_problem_orders.items():
        expected = list(range(1, len(observed) + 1))
        if sorted(observed) != expected:
            raise ValueError(
                f"{problem_id}: family display within-problem order must be contiguous "
                f"1..{len(observed)}"
            )
    return family_ids, band_counts, promotion_count


def _digest_json(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _private_path_hits(value: Any, path: str = "row") -> list[str]:
    hits: list[str] = []
    if isinstance(value, dict):
        for key, child in value.items():
            hits.extend(_private_path_hits(child, f"{path}.{key}"))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            hits.extend(_private_path_hits(child, f"{path}[{index}]"))
    elif isinstance(value, str) and any(marker in value for marker in PRIVATE_PATH_MARKERS):
        hits.append(path)
    return hits


def observed_result_atom_census(
    rows: list[dict], claims: Any = None, family_display_order: Any = None
) -> dict:
    """Validate authoritative inputs and return their observed public census."""
    claims_data = _load_claims(claims)
    family_registry, problem_ids, _ = _public_families(claims_data)
    display_rows = _load_family_display_order(family_display_order)
    display_family_ids, band_counts, promotion_count = _validate_family_display_order(
        display_rows, family_registry
    )
    atom_ids: set[str] = set()
    result_coordinates: set[tuple[str, str]] = set()
    ordinals: set[tuple[str, int]] = set()
    state_counts: Counter[str] = Counter()
    tier_counts: Counter[str] = Counter()
    problem_counts: Counter[str] = Counter()
    family_counts: Counter[str] = Counter()

    for index, row in enumerate(rows, 1):
        state = row.get("interpretation_state")
        if state == "delegated_agent_editorial_best_attempt":
            expected_keys = DELEGATED_KEYS
        elif state == "existing_source_linked_reviewer_card":
            expected_keys = CARD_KEYS
        else:
            raise ValueError(f"row {index}: unsupported interpretation state {state!r}")
        if set(row) != expected_keys:
            raise ValueError(f"row {index}: fields do not match state schema")
        if row["schema"] != "plectis.public-result-atom/1":
            raise ValueError(f"row {index}: unsupported schema")
        problem_id, result_id, atom_id = row["problem_id"], row["result_id"], row["atom_id"]
        if atom_id != f"{problem_id}:{result_id}":
            raise ValueError(f"row {index}: atom_id is not its problem/result coordinate")
        if atom_id in atom_ids or (problem_id, result_id) in result_coordinates:
            raise ValueError(f"row {index}: duplicate result atom {atom_id}")
        atom_ids.add(atom_id)
        result_coordinates.add((problem_id, result_id))
        if (problem_id, row["family_id"]) not in family_registry:
            raise ValueError(f"row {index}: family is absent from public claims")
        ordinal = row["source_ordinal"]
        if not isinstance(ordinal, int) or isinstance(ordinal, bool) or ordinal < 1:
            raise ValueError(f"row {index}: source_ordinal must be a positive integer")
        if (problem_id, ordinal) in ordinals:
            raise ValueError(f"row {index}: duplicate problem/source ordinal")
        ordinals.add((problem_id, ordinal))
        if not isinstance(row["statement_excerpt"], str) or not row["statement_excerpt"].strip():
            raise ValueError(f"row {index}: empty statement excerpt")
        if row["statement_scope"] != "excerpt_only_full_source_statement_not_reproduced":
            raise ValueError(f"row {index}: missing statement truth boundary")
        if not SHA256_RE.fullmatch(row["source_statement_sha256"]):
            raise ValueError(f"row {index}: malformed statement digest")
        if not isinstance(row["evidence_status"], str) or not row["evidence_status"]:
            raise ValueError(f"row {index}: missing evidence status")
        if not isinstance(row["display_tier"], str) or not row["display_tier"]:
            raise ValueError(f"row {index}: missing display tier")
        if row["display_tier_claim_ceiling"] != DISPLAY_TIER_CLAIM_CEILING:
            raise ValueError(f"row {index}: display tier claim ceiling drifted")
        hits = _private_path_hits(row, f"row[{index}]")
        if hits:
            raise ValueError(f"row {index}: private-only path at {hits[0]}")

        if state == "delegated_agent_editorial_best_attempt":
            interpretation = row["interpretation"]
            if not isinstance(interpretation, dict) or set(interpretation) != INTERPRETATION_KEYS:
                raise ValueError(f"row {index}: malformed delegated interpretation")
            if interpretation["actor"] != "delegated_agent_editorial":
                raise ValueError(f"row {index}: incorrect delegated actor")
            if interpretation["review_status"] != "llm_best_attempt_open_to_specialist_correction":
                raise ValueError(f"row {index}: incorrect delegated review status")
            for key in (
                "one_sentence_result",
                "why_it_matters",
                "mechanism_or_hard_step",
                "exact_boundary",
                "evidence_posture",
                "prior_art_posture",
                "next_open_obligation",
            ):
                if not isinstance(interpretation[key], str) or not interpretation[key].strip():
                    raise ValueError(
                        f"row {index}: interpretation.{key} must be nonempty text"
                    )
            for key in ("secondary_classes", "does_not_establish", "declaration_bindings"):
                if not isinstance(interpretation[key], list) or not all(
                    isinstance(value, str) for value in interpretation[key]
                ):
                    raise ValueError(f"row {index}: interpretation.{key} must be a string list")
            if not interpretation["does_not_establish"]:
                raise ValueError(
                    f"row {index}: interpretation.does_not_establish must be nonempty"
                )
        elif state == "existing_source_linked_reviewer_card":
            cards = row["reviewer_card_ids"]
            if (
                not isinstance(cards, list)
                or not cards
                or not all(isinstance(value, str) and value for value in cards)
            ):
                raise ValueError(f"row {index}: reviewer_card_ids must be nonempty")
            if (
                row["reviewer_card_availability"]
                != "pre_publication_source_link_only_card_body_not_included"
            ):
                raise ValueError(f"row {index}: reviewer-card availability is overstated")
        state_counts[state] += 1
        tier_counts[row["display_tier"]] += 1
        problem_counts[problem_id] += 1
        family_counts[row["family_id"]] += 1

    for problem_id in problem_ids:
        count = problem_counts.get(problem_id, 0)
        expected_ordinals = {(problem_id, ordinal) for ordinal in range(1, count + 1)}
        actual_ordinals = {
            coordinate for coordinate in ordinals if coordinate[0] == problem_id
        }
        if actual_ordinals != expected_ordinals:
            raise ValueError(f"{problem_id}: source ordinals are not contiguous 1..{count}")

    all_family_counts = {
        family_id: family_counts.get(family_id, 0) for family_id in display_family_ids
    }
    zero_family_ids = [
        family_id for family_id in display_family_ids if not all_family_counts[family_id]
    ]
    review_matrix = claims_data["external_verification_packet"]["review_matrix"]
    return {
        "total": len(rows),
        "family_count": len(display_family_ids),
        "populated_family_count": len(display_family_ids) - len(zero_family_ids),
        "family_ids": display_family_ids,
        "state_counts": dict(sorted(state_counts.items())),
        "tier_counts": dict(sorted(tier_counts.items())),
        "problem_counts": {
            problem_id: problem_counts.get(problem_id, 0)
            for problem_id in sorted(problem_ids)
        },
        "family_counts": all_family_counts,
        "band_counts": dict(sorted(band_counts.items())),
        "zero_family_ids": zero_family_ids,
        "promotion_count": promotion_count,
        "source_digests": {
            "claims_review_matrix_sha256": _digest_json(review_matrix),
            "family_display_order_sha256": _digest_json(display_rows),
            "result_atoms_sha256": _digest_json(rows),
        },
    }


def validate_result_atoms(
    rows: list[dict], claims: Any = None, family_display_order: Any = None
) -> dict:
    """Validate the complete public catalog and return its observed census."""
    return observed_result_atom_census(rows, claims, family_display_order)


def merge_candidate_atoms(
    rows: list[dict],
    candidates: list[dict],
    claims: Any = None,
    family_display_order: Any = None,
) -> tuple[list[dict], dict]:
    """Append candidates with derived ordinals and return a validated catalog.

    Candidate authors do not need to coordinate problem-local ordinals.  The
    owner derives them from the current catalog, then restores the canonical
    problem-block/ordinal ordering.  Every other field remains candidate-owned.
    """
    claims_data = _load_claims(claims)
    _, problem_ids, _ = _public_families(claims_data)
    validate_result_atoms(rows, claims_data, family_display_order)
    problem_order = {problem_id: index for index, problem_id in enumerate(problem_ids)}
    next_ordinal = {
        problem_id: max(
            (
                row["source_ordinal"]
                for row in rows
                if row["problem_id"] == problem_id
            ),
            default=0,
        )
        for problem_id in problem_ids
    }
    atom_ids = {row["atom_id"] for row in rows}
    merged = [dict(row) for row in rows]
    for index, candidate in enumerate(candidates, 1):
        if not isinstance(candidate, dict):
            raise ValueError(f"candidate row {index}: must be an object")
        problem_id = candidate.get("problem_id")
        if problem_id not in problem_order:
            raise ValueError(f"candidate row {index}: unknown problem {problem_id!r}")
        atom_id = candidate.get("atom_id")
        if atom_id in atom_ids:
            raise ValueError(f"candidate row {index}: duplicate result atom {atom_id}")
        atom_ids.add(atom_id)
        next_ordinal[problem_id] += 1
        row = dict(candidate)
        row["source_ordinal"] = next_ordinal[problem_id]
        merged.append(row)
    merged.sort(
        key=lambda row: (
            problem_order[row["problem_id"]],
            row["source_ordinal"],
            row["atom_id"],
        )
    )
    summary = validate_result_atoms(merged, claims_data, family_display_order)
    return merged, summary


def _write_catalog(rows: list[dict], path: Path) -> None:
    rendered = "".join(
        json.dumps(row, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
        + "\n"
        for row in rows
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    target_mode = stat.S_IMODE(path.stat().st_mode) if path.exists() else 0o644
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, delete=False
    ) as handle:
        handle.write(rendered)
        temporary = Path(handle.name)
    temporary.chmod(target_mode)
    os.replace(temporary, path)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate or safely merge the public result-atom catalog."
    )
    parser.add_argument(
        "--candidate-jsonl",
        type=Path,
        action="append",
        default=[],
        help="Candidate JSONL batch; repeatable. Ordinals are derived automatically.",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="Atomically write a validated candidate merge to the canonical catalog.",
    )
    args = parser.parse_args()
    rows = load_result_atoms()
    if args.write and not args.candidate_jsonl:
        parser.error("--write requires at least one --candidate-jsonl batch")
    if args.candidate_jsonl:
        candidates = [
            row
            for path in args.candidate_jsonl
            for row in _load_jsonl_objects(path)
        ]
        rows, summary = merge_candidate_atoms(rows, candidates)
        summary = {
            **summary,
            "mode": "write" if args.write else "dry_run",
            "candidate_count": len(candidates),
        }
        if args.write:
            _write_catalog(rows, CATALOG_PATH)
    else:
        summary = validate_result_atoms(rows)
    print(json.dumps(summary, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
