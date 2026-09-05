#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the aggregate Comparator replay candidate from per-entry packages.

The generated files are inputs for a future Comparator replay.  They are not a
Comparator receipt and do not claim that external verification has run.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tomllib
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from lean_source import lean_code_without_comments_and_strings


ROOT = Path(__file__).resolve().parent.parent
AGGREGATE_PACKAGE = "ComparatorReplay"
CHALLENGE_OUTPUT = ROOT / AGGREGATE_PACKAGE / "Challenge.lean"
SOLUTION_OUTPUT = ROOT / AGGREGATE_PACKAGE / "Solution.lean"
CONFIG_OUTPUT = ROOT / "verification" / "comparator-replay-candidate.json"
MEMBERSHIP_OUTPUT = ROOT / "verification" / "comparator-replay-membership.json"
PERMITTED_AXIOMS = ("propext", "Quot.sound", "Classical.choice")

IMPORT_RE = re.compile(r"(?m)^[ \t]*import[ \t]+(?P<module>[^\s]+)")
TOKEN_RE = re.compile(
    r"(?m)^[ \t]*(?:"
    r"namespace[ \t]+(?P<namespace>[A-Za-z_][A-Za-z0-9_'.]*)"
    r"|(?:(?:noncomputable)[ \t]+)?section(?:[ \t]+(?P<section>[A-Za-z_][A-Za-z0-9_']*))?[ \t]*$"
    r"|end(?:[ \t]+(?P<end>[A-Za-z_][A-Za-z0-9_'.]*))?[ \t]*$"
    r"|(?:@\[[^\]\r\n]*\][ \t]*)*"
    r"(?P<visibility>(?:private|protected)[ \t]+)?"
    r"(?:theorem|lemma)[ \t\r\n]+(?P<declaration>[A-Za-z_][A-Za-z0-9_'.]*)"
    r")"
)
FORBIDDEN_SOLUTION_RE = re.compile(
    r"\bsorry\b|\badmit\b|\bnative_decide\b|\bunsafe\b"
)


class PortfolioError(RuntimeError):
    """A per-entry package violates the aggregate replay contract."""


@dataclass(frozen=True)
class Package:
    name: str
    challenge_module: str
    solution_module: str
    theorem_names: tuple[str, ...]


@dataclass(frozen=True)
class Portfolio:
    packages: tuple[Package, ...]
    theorem_names: tuple[str, ...]
    required_packages: tuple[str, ...]
    required_interfaces_by_package: dict[str, tuple[str, ...]]
    result_family_coverage: dict[str, Any]
    registered_claim_coverage: dict[str, Any]
    legacy_package_record_assimilation: dict[str, Any] | None = None
    assurance_status: str = "replay_candidate"


FAMILY_REGISTRY_AUTHORITY = (
    "docs/claims.json::external_verification_packet.review_matrix"
)
CLAIM_REGISTRY_AUTHORITY = "docs/claims.json::claims"
CURRENT_COMPARATOR_ROLE = "current_comparator_package"
REPLAY_CANDIDATE_ROLE = "aggregate_replay_candidate_package"


def _family_disposition_class(disposition: str) -> str:
    if disposition.startswith("targeted"):
        return "targeted_exact_interface"
    if disposition.startswith("represented_by"):
        return "represented_by_selected_interface"
    if disposition.startswith("not_selected"):
        return "not_selected_for_comparator"
    if disposition.startswith("not_applicable"):
        return "not_applicable_to_comparator"
    raise PortfolioError(f"unknown result-family Comparator disposition: {disposition}")


def _non_executable_reason(disposition: str, disposition_class: str) -> str:
    if disposition_class == "represented_by_selected_interface":
        prefix = "The registry represents this family through another selected interface"
    elif disposition_class == "not_selected_for_comparator":
        prefix = "The registry deliberately does not select this family for Comparator"
    elif disposition_class == "not_applicable_to_comparator":
        prefix = "The registry marks Comparator execution as inapplicable to this family"
    else:
        raise PortfolioError(
            "a targeted result family cannot be intentionally non-executable: "
            f"{disposition}"
        )
    return f"{prefix}; comparator_disposition={disposition}."


def compile_result_family_coverage(
    claims: dict[str, Any],
    current_comparator: dict[str, Any],
    replay_packages: tuple[Package, ...],
) -> dict[str, Any]:
    """Join every registered family to current and replay-candidate packages.

    This is package discoverability, not a Comparator receipt.  Registered
    ``main_results`` provide the exact current-package join.  Other current or
    replay interfaces join only when their theorem leaf has one unique family
    owner in the review matrix.
    """
    try:
        packet = claims["external_verification_packet"]
        review_matrix = packet["review_matrix"]
        main_results = packet["main_results"]
    except (KeyError, TypeError) as exc:
        raise PortfolioError(
            "docs/claims.json lacks the external-verification family registry"
        ) from exc
    if not isinstance(review_matrix, list) or not isinstance(main_results, list):
        raise PortfolioError("external-verification family registry is malformed")

    families: dict[tuple[int, str], dict[str, Any]] = {}
    family_order: list[tuple[int, str]] = []
    leaf_owners: dict[str, list[tuple[int, str]]] = {}
    registry_digest_rows: list[dict[str, Any]] = []
    for problem_row in review_matrix:
        if not isinstance(problem_row, dict) or not isinstance(
            problem_row.get("families"), list
        ):
            raise PortfolioError("review-matrix problem row is malformed")
        problem = int(problem_row["problem"])
        for family in problem_row["families"]:
            if not isinstance(family, dict):
                raise PortfolioError("review-matrix family row is malformed")
            family_id = family.get("id")
            disposition = family.get("comparator_disposition")
            declarations = family.get("declarations", [])
            if (
                not isinstance(family_id, str)
                or not family_id
                or not isinstance(disposition, str)
                or not disposition
                or not isinstance(declarations, list)
                or not all(isinstance(name, str) and name for name in declarations)
            ):
                raise PortfolioError(
                    f"review-matrix family identity is malformed: problem={problem}"
                )
            key = (problem, family_id)
            if key in families:
                raise PortfolioError(f"duplicate review-matrix family: {key}")
            _family_disposition_class(disposition)
            families[key] = family
            family_order.append(key)
            registry_digest_rows.append(
                {
                    "problem": problem,
                    "family_id": family_id,
                    "comparator_disposition": disposition,
                    "declarations": declarations,
                }
            )
            for declaration in declarations:
                leaf_owners.setdefault(declaration.rsplit(".", 1)[-1], []).append(key)
    if not families:
        raise PortfolioError("review matrix contains no result families")

    current_names = current_comparator.get("theorem_names")
    if (
        not isinstance(current_names, list)
        or not current_names
        or not all(isinstance(name, str) and name for name in current_names)
        or len(current_names) != len(set(current_names))
    ):
        raise PortfolioError(
            "current Comparator theorem_names must be a nonempty unique string array"
        )
    current_roster = set(current_names)
    current_challenge = current_comparator.get("challenge_module")
    current_solution = current_comparator.get("solution_module")
    if not isinstance(current_challenge, str) or not isinstance(current_solution, str):
        raise PortfolioError("current Comparator module identities are malformed")

    registered_current: dict[tuple[int, str], list[str]] = {
        key: [] for key in families
    }
    explicitly_registered: set[str] = set()
    for row in main_results:
        if not isinstance(row, dict):
            raise PortfolioError("Comparator main-result row is malformed")
        key = (int(row.get("problem")), str(row.get("review_family")))
        wrapper = row.get("wrapper_declaration")
        if key not in families:
            raise PortfolioError(f"Comparator main result names unknown family: {key}")
        if not isinstance(wrapper, str) or wrapper not in current_roster:
            raise PortfolioError(
                f"registered Comparator wrapper is absent from current config: {wrapper}"
            )
        if wrapper in explicitly_registered:
            raise PortfolioError(f"duplicate registered Comparator wrapper: {wrapper}")
        explicitly_registered.add(wrapper)
        registered_current[key].append(wrapper)

    current_by_family: dict[tuple[int, str], list[str]] = {
        key: list(names) for key, names in registered_current.items()
    }
    unassociated_current: list[str] = []
    for theorem_name in current_names:
        if theorem_name in explicitly_registered:
            continue
        owners = leaf_owners.get(theorem_name.rsplit(".", 1)[-1], [])
        if len(owners) == 1:
            current_by_family[owners[0]].append(theorem_name)
        else:
            unassociated_current.append(theorem_name)

    replay_by_family: dict[tuple[int, str], dict[str, list[str]]] = {
        key: {} for key in families
    }
    unassociated_replay: list[str] = []
    for package in replay_packages:
        for theorem_name in package.theorem_names:
            owners = leaf_owners.get(theorem_name.rsplit(".", 1)[-1], [])
            if len(owners) == 1:
                replay_by_family[owners[0]].setdefault(package.name, []).append(
                    theorem_name
                )
            else:
                unassociated_replay.append(theorem_name)

    package_by_name = {package.name: package for package in replay_packages}
    rows: list[dict[str, Any]] = []
    execution_counts: Counter[str] = Counter()
    disposition_counts: Counter[str] = Counter()
    for problem, family_id in family_order:
        key = (problem, family_id)
        family = families[key]
        disposition = family["comparator_disposition"]
        disposition_class = _family_disposition_class(disposition)
        bindings: list[dict[str, Any]] = []
        current_family_names = sorted(set(current_by_family[key]))
        registered_names = sorted(set(registered_current[key]))
        if current_family_names:
            bindings.append(
                {
                    "package_id": current_challenge.rsplit(".", 1)[0],
                    "package_role": CURRENT_COMPARATOR_ROLE,
                    "challenge_module": current_challenge,
                    "solution_module": current_solution,
                    "interface_names": current_family_names,
                }
            )
        for package_id, theorem_names in sorted(replay_by_family[key].items()):
            package = package_by_name[package_id]
            bindings.append(
                {
                    "package_id": package_id,
                    "package_role": REPLAY_CANDIDATE_ROLE,
                    "challenge_module": package.challenge_module,
                    "solution_module": package.solution_module,
                    "interface_names": sorted(set(theorem_names)),
                }
            )

        executable_interface_count = sum(
            len(binding["interface_names"]) for binding in bindings
        )
        if bindings:
            execution_classification = "has_executable_challenge_package"
            non_executable_reason = None
        else:
            execution_classification = "intentionally_non_executable"
            non_executable_reason = _non_executable_reason(
                disposition, disposition_class
            )
        rows.append(
            {
                "problem": problem,
                "family_id": family_id,
                "registry_comparator_disposition": disposition,
                "registered_comparator_classification": disposition_class,
                "execution_classification": execution_classification,
                "registered_current_interface_count": len(registered_names),
                "current_comparator_interface_count": len(current_family_names),
                "replay_candidate_interface_count": (
                    executable_interface_count - len(current_family_names)
                ),
                "executable_package_count": len(bindings),
                "executable_interface_count": executable_interface_count,
                "packages": bindings,
                "non_executable_reason": non_executable_reason,
            }
        )
        execution_counts[execution_classification] += 1
        disposition_counts[disposition_class] += 1

    digest_payload = json.dumps(
        registry_digest_rows,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return {
        "schema": "plectis.comparator-result-family-coverage/1",
        "registry_authority": FAMILY_REGISTRY_AUTHORITY,
        "registry_digest": "sha256:" + hashlib.sha256(digest_payload).hexdigest(),
        "registered_family_count": len(rows),
        "classified_family_count": len(rows),
        "execution_classification_counts": dict(sorted(execution_counts.items())),
        "registered_comparator_classification_counts": dict(
            sorted(disposition_counts.items())
        ),
        "family_linked_current_interface_count": sum(
            row["current_comparator_interface_count"] for row in rows
        ),
        "family_linked_replay_candidate_interface_count": sum(
            row["replay_candidate_interface_count"] for row in rows
        ),
        "unassociated_current_interface_count": len(unassociated_current),
        "unassociated_replay_candidate_interface_count": len(unassociated_replay),
        "families": rows,
        "growth_policy": (
            "Every review-matrix family is joined dynamically. A newly targeted "
            "family must acquire an executable Challenge interface; represented, "
            "not-selected, and not-applicable families remain visible with their "
            "registry disposition as the explicit non-execution reason."
        ),
        "boundary": (
            "Family classification records package/interface discoverability only. "
            "It is not a Comparator run, axiom audit, kernel receipt, Palomar review, "
            "submission, registration, publication, novelty, or significance claim."
        ),
    }


def main_result_source_anchors(
    claim: dict[str, Any], result: dict[str, Any]
) -> list[dict[str, Any]]:
    """Resolve an explicitly claim-bound main result to one exact source anchor.

    The claim id establishes ownership.  The declaration check only verifies
    that the result's named source really is one of that claim's registered
    anchors; it is never used to infer a claim from a theorem leaf.
    """

    source = result.get("original_source")
    declaration = result.get("original_declaration")
    if not isinstance(source, str) or not isinstance(declaration, str):
        return []
    matches = [
        anchor
        for anchor in claim["declarations"]
        if anchor["module"] == source
        and (
            declaration == anchor["name"]
            or declaration.endswith(f".{anchor['name']}")
        )
    ]
    return matches if len(matches) == 1 else []


def validate_claim_transport_link(
    claim_id: str,
    claim: dict[str, Any],
    package_id: object,
    interface_name: object,
    source_declarations: object,
    interface_roster: dict[str, set[str]],
) -> list[dict[str, Any]]:
    """Validate one owner-authored link without guessing from theorem leaves."""

    if (
        not isinstance(package_id, str)
        or not isinstance(interface_name, str)
        or not isinstance(source_declarations, list)
        or not source_declarations
        or not all(isinstance(anchor, dict) for anchor in source_declarations)
        or any(anchor not in claim.get("declarations", []) for anchor in source_declarations)
    ):
        raise PortfolioError(
            f"claim transport uses an unregistered source anchor: {claim_id}"
        )
    if interface_name not in interface_roster.get(package_id, set()):
        raise PortfolioError(
            "claim transport names an absent Comparator package/interface: "
            f"{claim_id}: {package_id}: {interface_name}"
        )
    return sorted(
        source_declarations,
        key=lambda row: (row["module"], row["line"], row["name"]),
    )


def compile_registered_claim_coverage(
    claims: dict[str, Any],
    current_comparator: dict[str, Any],
    replay_packages: tuple[Package, ...],
) -> dict[str, Any]:
    """Account for every registered claim without inferring semantic coverage.

    A transport says only that Comparator has a separately declared interface
    linked to exact formal source anchors.  It does not say that the interface
    captures the full informal claim, that Comparator ran, or that any review
    or assurance was completed.
    """

    claim_rows = claims.get("claims")
    packet = claims.get("external_verification_packet")
    if not isinstance(claim_rows, list) or not isinstance(packet, dict):
        raise PortfolioError("docs/claims.json lacks the registered claim owner")
    main_results = packet.get("main_results")
    if not isinstance(main_results, list):
        raise PortfolioError("registered claim main_results are malformed")

    claim_by_id: dict[str, dict[str, Any]] = {}
    digest_rows: list[dict[str, Any]] = []
    for claim in claim_rows:
        if not isinstance(claim, dict):
            raise PortfolioError("registered claim row is malformed")
        claim_id = claim.get("id")
        status = claim.get("status")
        declarations = claim.get("declarations")
        explicit = claim.get("comparator_transports", [])
        if (
            not isinstance(claim_id, str)
            or not claim_id
            or claim_id in claim_by_id
            or not isinstance(status, str)
            or not status
            or not isinstance(declarations, list)
            or not all(
                isinstance(anchor, dict)
                and isinstance(anchor.get("name"), str)
                and isinstance(anchor.get("module"), str)
                and type(anchor.get("line")) is int
                and anchor["line"] > 0
                for anchor in declarations
            )
            or not isinstance(explicit, list)
        ):
            raise PortfolioError(f"registered claim identity is malformed: {claim_id}")
        claim_by_id[claim_id] = claim
        digest_rows.append(
            {
                "id": claim_id,
                "status": status,
                "statement": claim.get("statement"),
                "declarations": declarations,
                "comparator_transports": explicit,
            }
        )

    current_names = current_comparator.get("theorem_names")
    current_challenge = current_comparator.get("challenge_module")
    current_solution = current_comparator.get("solution_module")
    if (
        not isinstance(current_names, list)
        or not all(isinstance(name, str) and name for name in current_names)
        or not isinstance(current_challenge, str)
        or not isinstance(current_solution, str)
    ):
        raise PortfolioError("current Comparator claim transport roster is malformed")
    current_package_id = current_challenge.rsplit(".", 1)[0]
    package_catalog: dict[str, dict[str, Any]] = {
        current_package_id: {
            "package_role": CURRENT_COMPARATOR_ROLE,
            "challenge_module": current_challenge,
            "solution_module": current_solution,
            "interface_names": set(current_names),
        }
    }
    for package in replay_packages:
        package_catalog[package.name] = {
            "package_role": REPLAY_CANDIDATE_ROLE,
            "challenge_module": package.challenge_module,
            "solution_module": package.solution_module,
            "interface_names": set(package.theorem_names),
        }

    linked: dict[str, dict[tuple[str, str, str], dict[str, Any]]] = {
        claim_id: {} for claim_id in claim_by_id
    }
    interface_roster = {
        package_id: set(package["interface_names"])
        for package_id, package in package_catalog.items()
    }

    def add_transport(
        claim_id: str,
        package_id: str,
        interface_name: str,
        source_declarations: list[dict[str, Any]],
        link_source: str,
    ) -> None:
        claim = claim_by_id[claim_id]
        anchors = validate_claim_transport_link(
            claim_id,
            claim,
            package_id,
            interface_name,
            source_declarations,
            interface_roster,
        )
        package = package_catalog[package_id]
        anchor_key = json.dumps(anchors, sort_keys=True, separators=(",", ":"))
        key = (package_id, interface_name, anchor_key)
        existing = linked[claim_id].get(key)
        if existing is None:
            linked[claim_id][key] = {
                "package_id": package_id,
                "package_role": package["package_role"],
                "challenge_module": package["challenge_module"],
                "solution_module": package["solution_module"],
                "interface_name": interface_name,
                "source_declarations": anchors,
                "link_sources": [link_source],
            }
        elif link_source not in existing["link_sources"]:
            existing["link_sources"].append(link_source)
            existing["link_sources"].sort()

    for result in main_results:
        if not isinstance(result, dict):
            raise PortfolioError("registered claim main-result row is malformed")
        claim_id = result.get("claim_id")
        if claim_id is None:
            continue
        if not isinstance(claim_id, str) or claim_id not in claim_by_id:
            raise PortfolioError(f"main result names unknown registered claim: {claim_id}")
        anchors = main_result_source_anchors(claim_by_id[claim_id], result)
        if not anchors:
            raise PortfolioError(
                f"claim-bound main result lacks one exact registered source anchor: {claim_id}"
            )
        wrapper = result.get("wrapper_declaration")
        if not isinstance(wrapper, str):
            raise PortfolioError(f"claim-bound main result lacks an interface: {claim_id}")
        add_transport(
            claim_id,
            current_package_id,
            wrapper,
            anchors,
            "main_result_claim_id",
        )

    for claim_id, claim in claim_by_id.items():
        for transport in claim.get("comparator_transports", []):
            if not isinstance(transport, dict):
                raise PortfolioError(
                    f"explicit Comparator transport is malformed: {claim_id}"
                )
            package_id = transport.get("package_id")
            interface_name = transport.get("interface_name")
            source_declarations = transport.get("source_declarations")
            if (
                not isinstance(package_id, str)
                or not isinstance(interface_name, str)
                or not isinstance(source_declarations, list)
                or not all(isinstance(anchor, dict) for anchor in source_declarations)
            ):
                raise PortfolioError(
                    f"explicit Comparator transport is malformed: {claim_id}"
                )
            add_transport(
                claim_id,
                package_id,
                interface_name,
                source_declarations,
                "claim_owner_explicit",
            )

    rows: list[dict[str, Any]] = []
    counts: Counter[str] = Counter()
    missing_ids: list[str] = []
    for claim_id, claim in claim_by_id.items():
        transports = sorted(
            linked[claim_id].values(),
            key=lambda row: (row["package_id"], row["interface_name"]),
        )
        status = claim["status"]
        declarations = claim["declarations"]
        if transports:
            if not declarations or status in {"open", "cited only"}:
                raise PortfolioError(
                    f"non-formal claim cannot have an executable transport: {claim_id}"
                )
            classification = "linked_transport"
            reason = None
        elif declarations:
            classification = "missing_formal_transport"
            reason = "No explicit exact Comparator transport link is registered for this formal claim."
            missing_ids.append(claim_id)
        elif status == "open":
            classification = "open_non_executable"
            reason = "The claim is open and has no formal declaration to transport."
        elif status == "cited only":
            classification = "cited_only_non_executable"
            reason = "The claim is cited only and has no local formal declaration to transport."
        else:
            raise PortfolioError(
                "declaration-free claim needs an explicit open or cited-only status: "
                f"{claim_id}"
            )
        counts[classification] += 1
        rows.append(
            {
                "claim_id": claim_id,
                "claim_status": status,
                "classification": classification,
                "registered_declarations": declarations,
                "transport_count": len(transports),
                "transports": transports,
                "reason": reason,
                "semantic_coverage_status": "not_assessed_by_transport_link",
                "executed_comparator_assurance": "not_asserted",
            }
        )

    digest_payload = json.dumps(
        digest_rows,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return {
        "schema": "plectis.comparator-registered-claim-coverage/1",
        "registry_authority": CLAIM_REGISTRY_AUTHORITY,
        "registry_digest": "sha256:" + hashlib.sha256(digest_payload).hexdigest(),
        "registry_digest_definition": (
            "sha256 of canonical JSON rows containing each registered claim id, "
            "status, statement, exact declaration anchors, and explicit transports"
        ),
        "registered_claim_count": len(rows),
        "classified_claim_count": len(rows),
        "classification_counts": dict(sorted(counts.items())),
        "formal_claim_count": sum(bool(row["registered_declarations"]) for row in rows),
        "linked_transport_claim_count": counts["linked_transport"],
        "missing_formal_transport_count": len(missing_ids),
        "missing_formal_claim_ids": sorted(missing_ids),
        "complete_formal_transport_coverage": not missing_ids,
        "claims": rows,
        "boundary": (
            "A linked transport records an exact claim-owner edge to a separately "
            "declared Comparator interface. It does not establish full informal-claim "
            "semantic coverage, a Comparator execution, external review, assurance, "
            "novelty, significance, or publication acceptance."
        ),
    }
def membership_payload(root: Path = ROOT) -> dict[str, Any]:
    path = root / "verification" / "comparator-replay-membership.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise PortfolioError(f"cannot read aggregate membership owner {path}: {exc}") from exc
    if payload.get("schema") != "plectis.comparator-replay-membership/1":
        raise PortfolioError(f"unsupported aggregate membership schema: {path}")
    return payload


def required_package_ids(root: Path = ROOT) -> tuple[str, ...]:
    path = root / "verification" / "comparator-replay-membership.json"
    payload = membership_payload(root)
    rows = payload.get("required_package_ids")
    if (
        not isinstance(rows, list)
        or not rows
        or not all(isinstance(row, str) and row for row in rows)
        or rows != sorted(set(rows))
    ):
        raise PortfolioError(f"aggregate membership must be a sorted unique package list: {path}")
    return tuple(rows)


def required_interfaces_by_package(root: Path = ROOT) -> dict[str, tuple[str, ...]]:
    """Return the monotone theorem-interface baseline, if already established."""
    path = root / "verification" / "comparator-replay-membership.json"
    payload = membership_payload(root)
    rows = payload.get("required_interfaces_by_package", {})
    if not isinstance(rows, dict):
        raise PortfolioError(f"aggregate interface baseline must be an object: {path}")
    required_packages = set(required_package_ids(root))
    if not set(rows) <= required_packages:
        raise PortfolioError(
            f"aggregate interface baseline names a non-required package: {path}"
        )
    parsed: dict[str, tuple[str, ...]] = {}
    for package_id, names in rows.items():
        if (
            not isinstance(package_id, str)
            or not package_id
            or not isinstance(names, list)
            or not names
            or not all(isinstance(name, str) and name for name in names)
            or names != sorted(set(names))
        ):
            raise PortfolioError(
                f"aggregate interface baseline must contain sorted unique theorem names: {package_id}"
            )
        parsed[package_id] = tuple(names)
    return parsed


def validate_legacy_package_record_assimilation(
    payload: dict[str, Any] | None,
    packages: tuple[Package, ...],
    required_packages: tuple[str, ...],
) -> None:
    """Keep the old per-package Palomar release records monotonically covered.

    The historical rows are provenance, not executable Comparator configs.  Their
    theorem names must remain a subset of the generated aggregate, so new packages
    or interfaces can still be added without copying per-package manifests back
    into the repository.
    """
    if payload is None:
        return
    if payload.get("schema") != "plectis.legacy-palomar-package-assimilation/1":
        raise PortfolioError("unsupported legacy Palomar package assimilation schema")
    source = payload.get("source_snapshot")
    rows = payload.get("package_records")
    if not isinstance(source, dict) or not isinstance(rows, list):
        raise PortfolioError("legacy Palomar package assimilation is malformed")
    if (
        not re.fullmatch(r"[0-9a-f]{40}", str(source.get("revision")))
        or not re.fullmatch(r"[0-9a-f]{40}", str(source.get("tree")))
        or source.get("record_layout")
        != "{package_id}/comparator.json + {package_id}/formalization.yaml"
        or source.get("record_count") != len(rows)
    ):
        raise PortfolioError("legacy Palomar source snapshot identity is malformed")
    package_ids = [row.get("package_id") for row in rows if isinstance(row, dict)]
    if (
        len(package_ids) != len(rows)
        or not all(isinstance(package_id, str) and package_id for package_id in package_ids)
        or package_ids != sorted(set(package_ids))
    ):
        raise PortfolioError("legacy Palomar package records must be sorted and unique")

    historical_names: list[str] = []
    current_by_package = {package.name: set(package.theorem_names) for package in packages}
    required = set(required_packages)
    for row in rows:
        package_id = row["package_id"]
        names = row.get("legacy_theorem_names")
        if (
            not isinstance(names, list)
            or not names
            or not all(isinstance(name, str) and name for name in names)
            or len(names) != len(set(names))
            or any(
                not name.startswith(f"Erdos249257.{package_id}.") for name in names
            )
        ):
            raise PortfolioError(
                f"legacy Palomar theorem roster is malformed: {package_id}"
            )
        if package_id not in required or package_id not in current_by_package:
            raise PortfolioError(
                f"legacy Palomar package is absent from aggregate membership: {package_id}"
            )
        missing = sorted(set(names) - current_by_package[package_id])
        if missing:
            raise PortfolioError(
                "legacy Palomar Comparator interface(s) disappeared from the dynamic "
                f"aggregate: {missing}"
            )
        historical_names.extend(names)

    if len(historical_names) != len(set(historical_names)):
        raise PortfolioError("legacy Palomar Comparator interfaces are not globally unique")
    if source.get("comparator_interface_count") != len(historical_names):
        raise PortfolioError("legacy Palomar Comparator interface count drifted")

    formalization = payload.get("formalization_policy", {})
    configuration = payload.get("configuration_delta", {})
    if (
        formalization.get("current_owner") != "formalization.yaml"
        or formalization.get("per_package_manifests") != "historical_only_do_not_recreate"
        or configuration.get("current_aggregate_config")
        != "verification/comparator-replay-candidate.json"
        or configuration.get("legacy_enable_nanoda") is not True
        or configuration.get("current_enable_nanoda") is not False
    ):
        raise PortfolioError("legacy Palomar assimilation policy drifted")


def lake_targets(root: Path) -> set[str]:
    """Return the exact named Lean library targets in ``lakefile.toml``."""
    path = root / "lakefile.toml"
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise PortfolioError(f"cannot read {path}: {exc}") from exc
    rows = data.get("lean_lib", [])
    return {
        row["name"]
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("name"), str)
    }


def imports_in(path: Path) -> tuple[str, ...]:
    code = lean_code_without_comments_and_strings(path.read_text(encoding="utf-8"))
    return tuple(match.group("module") for match in IMPORT_RE.finditer(code))


def validate_challenge_imports(package_dir: Path) -> None:
    """Keep Challenge's transitive statement layer on the Mathlib boundary."""
    challenge = package_dir / "Challenge.lean"
    imports = imports_in(challenge)
    if not imports:
        raise PortfolioError(f"trusted Challenge has no imports: {challenge}")

    own_statements = f"{package_dir.name}.Statements"
    for module in imports:
        if module == "Mathlib" or module.startswith("Mathlib."):
            continue
        if module != own_statements:
            raise PortfolioError(
                f"trusted Challenge imports project-local module {module}: {challenge}"
            )
        statements = package_dir / "Statements.lean"
        if not statements.is_file():
            raise PortfolioError(
                f"trusted Challenge imports missing statement layer: {statements}"
            )
        statement_imports = imports_in(statements)
        if not statement_imports or any(
            module != "Mathlib" and not module.startswith("Mathlib.")
            for module in statement_imports
        ):
            raise PortfolioError(
                "trusted statement layer must import only Mathlib modules: "
                f"{statements}"
            )


def declarations_in(path: Path, *, reject_private: bool = False) -> tuple[str, ...]:
    """Extract source-order fully-qualified theorem and lemma names."""
    code = lean_code_without_comments_and_strings(path.read_text(encoding="utf-8"))
    blocks: list[tuple[str, str | None]] = []
    declarations: list[str] = []
    for match in TOKEN_RE.finditer(code):
        namespace = match.group("namespace")
        declaration = match.group("declaration")
        if namespace is not None:
            blocks.append(("namespace", namespace))
        elif match.group("section") is not None or re.match(
            r"^[ \t]*(?:(?:noncomputable)[ \t]+)?section(?:[ \t]|$)",
            match.group(0),
        ):
            blocks.append(("section", match.group("section")))
        elif declaration is not None:
            if match.group("visibility") and match.group("visibility").strip() == "private":
                if reject_private:
                    raise PortfolioError(
                        f"Comparator interface cannot be private: {path}: {declaration}"
                    )
                continue
            namespaces = [name for kind, name in blocks if kind == "namespace" and name]
            declarations.append(".".join((*namespaces, declaration)))
        elif blocks:
            blocks.pop()
    return tuple(declarations)


def validate_solution(path: Path) -> None:
    code = lean_code_without_comments_and_strings(path.read_text(encoding="utf-8"))
    match = FORBIDDEN_SOLUTION_RE.search(code)
    if match:
        raise PortfolioError(
            f"solution contains forbidden {match.group(0)!r}: {path}"
        )


def package_directories(
    root: Path, targets: set[str], required_packages: tuple[str, ...]
) -> tuple[Path, ...]:
    """Discover top-level per-entry packages, with the legacy root excluded."""
    packages: list[Path] = []
    for directory in sorted(
        (
            path
            for path in root.iterdir()
            if path.is_dir() and path.name.startswith("ExternalVerification")
        ),
        key=lambda path: path.name,
    ):
        if directory.name == "ExternalVerification":
            continue
        challenge = directory / "Challenge.lean"
        solution = directory / "Solution.lean"
        matches_contract = (
            challenge.is_file()
            and solution.is_file()
            and directory.name in targets
        )
        if not challenge.is_file() and not solution.is_file():
            continue
        if not challenge.is_file() or not solution.is_file():
            raise PortfolioError(
                f"per-entry package needs matching Challenge.lean and Solution.lean: {directory}"
            )
        if directory.name not in targets:
            raise PortfolioError(
                f"per-entry package has no named Lake target: {directory.name}"
            )
        packages.append(directory)
    discovered = {path.name for path in packages}
    missing = sorted(set(required_packages) - discovered)
    if missing:
        raise PortfolioError(
            "required Comparator replay package(s) disappeared without an explicit "
            f"membership migration: {missing}"
        )
    return tuple(packages)


def build_portfolio(root: Path = ROOT) -> Portfolio:
    membership = membership_payload(root)
    targets = lake_targets(root)
    required_packages = required_package_ids(root)
    required_interfaces = required_interfaces_by_package(root)
    packages: list[Package] = []
    all_theorems: list[str] = []
    for directory in package_directories(root, targets, required_packages):
        challenge = directory / "Challenge.lean"
        solution = directory / "Solution.lean"
        validate_challenge_imports(directory)
        validate_solution(solution)
        theorem_names = declarations_in(challenge, reject_private=True)
        if not theorem_names:
            raise PortfolioError(f"per-entry Challenge has no theorem: {challenge}")
        solution_names = set(declarations_in(solution))
        missing = [name for name in theorem_names if name not in solution_names]
        if missing:
            raise PortfolioError(
                f"Solution does not implement Challenge interface(s) {missing}: {solution}"
            )
        packages.append(
            Package(
                name=directory.name,
                challenge_module=f"{directory.name}.Challenge",
                solution_module=f"{directory.name}.Solution",
                theorem_names=theorem_names,
            )
        )
        all_theorems.extend(theorem_names)

    duplicates = sorted(
        name for name in set(all_theorems) if all_theorems.count(name) > 1
    )
    if duplicates:
        raise PortfolioError(
            f"fully-qualified Comparator theorem names are not unique: {duplicates}"
        )
    package_tuple = tuple(packages)
    current_by_package = {
        package.name: set(package.theorem_names) for package in package_tuple
    }
    for package_id, names in required_interfaces.items():
        missing = sorted(set(names) - current_by_package.get(package_id, set()))
        if missing:
            raise PortfolioError(
                "required Comparator replay interface(s) disappeared without an "
                f"explicit membership migration: {missing}"
            )
    legacy_assimilation = membership.get("legacy_package_record_assimilation")
    validate_legacy_package_record_assimilation(
        legacy_assimilation,
        package_tuple,
        required_packages,
    )
    try:
        claims = json.loads((root / "docs" / "claims.json").read_text(encoding="utf-8"))
        current_comparator = json.loads(
            (root / "verification" / "comparator.json").read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError) as exc:
        raise PortfolioError(
            "cannot read the result-family registry or current Comparator config"
        ) from exc
    result_family_coverage = compile_result_family_coverage(
        claims,
        current_comparator,
        package_tuple,
    )
    registered_claim_coverage = compile_registered_claim_coverage(
        claims,
        current_comparator,
        package_tuple,
    )
    return Portfolio(
        package_tuple,
        tuple(all_theorems),
        required_packages,
        required_interfaces,
        result_family_coverage,
        registered_claim_coverage,
        legacy_assimilation,
    )


def render_aggregate(module_names: tuple[str, ...], *, role: str) -> str:
    imports = "\n".join(f"import {module}" for module in module_names)
    return (
        "/-\n"
        "Copyright (c) 2026 Will Cook. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: Will Cook\n"
        "-/\n"
        f"-- Generated by scripts/build_comparator_replay_portfolio.py; do not edit.\n"
        f"-- Aggregate {role} for a Comparator replay candidate. This is not a replay receipt.\n"
        f"{imports}\n"
    )


def render_config(portfolio: Portfolio) -> str:
    payload = {
        "challenge_module": f"{AGGREGATE_PACKAGE}.Challenge",
        "solution_module": f"{AGGREGATE_PACKAGE}.Solution",
        "theorem_names": list(portfolio.theorem_names),
        "permitted_axioms": list(PERMITTED_AXIOMS),
        "enable_nanoda": False,
    }
    return json.dumps(payload, ensure_ascii=False, indent=2) + "\n"


def render_membership(portfolio: Portfolio) -> str:
    required = sorted(
        set(portfolio.required_packages) | {package.name for package in portfolio.packages}
    )
    current_by_package = {
        package.name: set(package.theorem_names) for package in portfolio.packages
    }
    interface_baseline = {
        package_id: sorted(
            set(portfolio.required_interfaces_by_package.get(package_id, ()))
            | current_by_package.get(package_id, set())
        )
        for package_id in required
    }
    payload = {
        "schema": "plectis.comparator-replay-membership/1",
        "required_package_ids": required,
        "required_interfaces_by_package": interface_baseline,
        "growth_policy": (
            "New eligible packages and theorem interfaces are included automatically. "
            "The builder appends them to these baselines; removing a required package "
            "or interface needs an explicit reviewed membership migration."
        ),
        "boundary": (
            "This file prevents silent package or theorem-interface coverage shrinkage. "
            "It does not assert that Comparator has run or that Palomar registered any "
            "package."
        ),
        "result_family_coverage": portfolio.result_family_coverage,
        "registered_claim_coverage": portfolio.registered_claim_coverage,
    }
    if portfolio.legacy_package_record_assimilation is not None:
        payload["legacy_package_record_assimilation"] = (
            portfolio.legacy_package_record_assimilation
        )
    return json.dumps(payload, ensure_ascii=False, indent=2) + "\n"


def expected_outputs(portfolio: Portfolio) -> dict[Path, str]:
    return {
        CHALLENGE_OUTPUT: render_aggregate(
            tuple(package.challenge_module for package in portfolio.packages),
            role="Challenge",
        ),
        SOLUTION_OUTPUT: render_aggregate(
            tuple(package.solution_module for package in portfolio.packages),
            role="Solution",
        ),
        CONFIG_OUTPUT: render_config(portfolio),
        MEMBERSHIP_OUTPUT: render_membership(portfolio),
    }


def write_changed_outputs(outputs: dict[Path, str]) -> int:
    """Write only changed projections so equal Lean outputs keep their mtimes."""

    changed = 0
    for path, content in outputs.items():
        if path.is_file() and path.read_text(encoding="utf-8") == content:
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        changed += 1
    return changed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="validate inputs and fail if generated outputs are stale"
    )
    parser.add_argument(
        "--require-complete-claims",
        action="store_true",
        help=(
            "read-only strict mode: fail unless every declaration-backed registered "
            "claim has an explicit exact linked Comparator transport"
        ),
    )
    args = parser.parse_args(argv)
    try:
        portfolio = build_portfolio()
        outputs = expected_outputs(portfolio)
    except (OSError, PortfolioError) as exc:
        print(f"comparator replay candidate error: {exc}", file=sys.stderr)
        return 1

    claim_coverage = portfolio.registered_claim_coverage
    incomplete_claim_coverage = args.require_complete_claims and not claim_coverage[
        "complete_formal_transport_coverage"
    ]

    if args.check or args.require_complete_claims:
        stale = [
            path.relative_to(ROOT).as_posix()
            for path, expected in outputs.items()
            if not path.is_file() or path.read_text(encoding="utf-8") != expected
        ]
        if stale:
            print(
                "Comparator replay candidate outputs stale: "
                + ", ".join(stale)
                + "; run python3 scripts/build_comparator_replay_portfolio.py"
            )
            return 1
        if incomplete_claim_coverage:
            print(
                "Comparator registered-claim coverage incomplete: "
                f"{claim_coverage['missing_formal_transport_count']} formal claim(s) "
                "lack explicit exact linked transports",
                file=sys.stderr,
            )
            return 1
        print(
            "Comparator replay candidate current: "
            f"{len(portfolio.packages)} packages, {len(portfolio.theorem_names)} interfaces; "
            f"claims={claim_coverage['linked_transport_claim_count']} linked/"
            f"{claim_coverage['missing_formal_transport_count']} missing formal; "
            "no Comparator run or receipt asserted"
        )
        return 0

    changed_outputs = write_changed_outputs(outputs)
    print(
        "wrote Comparator replay candidate: "
        f"{len(portfolio.packages)} packages, {len(portfolio.theorem_names)} interfaces, "
        f"{changed_outputs} changed output(s); "
        "no Comparator run or receipt asserted"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
