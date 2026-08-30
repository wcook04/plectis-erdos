#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build a validator-checked accepted receipt from an explicit review decision.

This command does not decide whether work is accepted.  It preserves the
submitted return verbatim except for ``record_kind``, ``accepted_commit``, and
the review block supplied by the repository reviewer.  The resulting file is
only durable attribution evidence after it is reviewed and committed.
"""

from __future__ import annotations

import argparse
import copy
import datetime as dt
import hashlib
import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Any

import route_memory_receipt
import validate_research_return as return_validator
import repository_identity as repository_identity_contract


ROOT = Path(__file__).resolve().parents[1]
DECISION_SCHEMA = "research-return-acceptance-decision/1"
RESULT_SCHEMA = "research-return-acceptance-candidate/1"
TEMPLATE_RESULT_SCHEMA = "research-return-acceptance-decision-template/1"
DECISION_FIELDS = {"schema", "accepted_commit", "review"}
REVIEW_NAMES = set(return_validator.REVIEW_STATES)


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except UnicodeError as exc:
        raise ValueError(f"cannot decode JSON as UTF-8: {path}: {exc}") from exc


def canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


def route_memory_binding_errors(
    submitted: Any,
    receipt_path: Path | None,
    *,
    required: bool,
) -> tuple[dict[str, Any] | None, list[str], bool]:
    """Validate the detached route receipt before accepting a submitted return.

    The accepted receipt schema intentionally stays single-sourced: route
    relationships remain in the companion sidecar.  This boundary nevertheless
    refuses to create an accepted artifact unless an explicitly supplied sidecar
    is bound to the submitted return's problem, return id, route digest, and
    evidence relationship.  The final boolean distinguishes unreadable input
    (CLI misuse, exit 2) from a readable but dishonest sidecar (validation,
    exit 1).
    """
    if receipt_path is None:
        if required:
            return None, [
                "route_memory_receipt: required for accepted receipt generation"
            ], False
        return None, [], False
    if path_has_symlink_component(receipt_path):
        return None, [
            "route_memory_receipt: path must not traverse symbolic links"
        ], False
    try:
        value = load_json(receipt_path)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        return None, [f"route_memory_receipt: cannot read JSON: {exc}"], True
    if not isinstance(value, dict):
        return None, ["route_memory_receipt: must be a JSON object"], False
    if not isinstance(submitted, dict):
        # The submitted-return validator supplies the authoritative shape error.
        return value, [], False
    errors = route_memory_receipt.validate_detached_return_receipt(
        value, submitted, ROOT
    )
    return value, errors, False


def route_memory_binding_summary(value: dict[str, Any]) -> dict[str, Any]:
    """Expose the verified route identity without copying it into the receipt."""
    binding = value.get("route_memory")
    relationships = value.get("relationships")
    route_ids: list[str] = []
    evidence_paths: set[str] = set()
    if isinstance(relationships, list):
        for relationship in relationships:
            if not isinstance(relationship, dict):
                continue
            route_id = relationship.get("route_id")
            if isinstance(route_id, str):
                route_ids.append(route_id)
            changed = relationship.get("changed_evidence")
            if isinstance(changed, list):
                evidence_paths.update(
                    item for item in changed if isinstance(item, str)
                )
    return {
        "problem": value.get("problem"),
        "route_ids": route_ids,
        "route_memory": copy.deepcopy(binding),
        "evidence_paths": sorted(evidence_paths),
    }


def acceptance_chronology_errors(submitted: dict[str, Any], review: Any) -> list[str]:
    """Reject an accepted-handoff decision that predates its submitted return."""
    if not isinstance(review, dict):
        return []
    handoff = review.get("accepted_handoff")
    if not isinstance(handoff, dict):
        return []
    submitted_at = submitted.get("submitted_at")
    decided_at = handoff.get("decided_at")
    if not isinstance(submitted_at, str) or not isinstance(decided_at, str):
        return []
    try:
        submitted_time = dt.datetime.fromisoformat(submitted_at.replace("Z", "+00:00"))
        decided_time = dt.datetime.fromisoformat(decided_at.replace("Z", "+00:00"))
    except ValueError:
        return []
    if submitted_time.utcoffset() is None or decided_time.utcoffset() is None:
        return []
    if decided_time < submitted_time:
        return [
            "decision.review.accepted_handoff.decided_at: "
            "must not precede submitted.submitted_at"
        ]
    return []


def acceptance_authority_errors(accepted_commit: Any, review: Any) -> list[str]:
    """Keep an explicit Git handoff authority bound to the accepted artifact."""
    if not isinstance(accepted_commit, str) or not isinstance(review, dict):
        return []
    handoff = review.get("accepted_handoff")
    if not isinstance(handoff, dict):
        return []
    authority_ref = handoff.get("authority_ref")
    if not isinstance(authority_ref, str) or not authority_ref.startswith("git:"):
        return []
    expected = f"git:{accepted_commit}"
    if authority_ref != expected:
        return [
            "decision.review.accepted_handoff.authority_ref: "
            "Git authority must name decision.accepted_commit"
        ]
    return []


def accepted_commit_checkout_errors(accepted_commit: Any) -> list[str]:
    """Keep accepted receipts bound to the checkout that produced them.

    ``validate_research_return`` proves object existence and ancestry from the
    submitted generation, while the accepted-only projection separately
    requires the accepted commit to be reachable from ``HEAD``.  Enforce that
    same boundary here so the acceptance CLI cannot emit a receipt that the
    canonical projection must later discard.
    """
    if not isinstance(accepted_commit, str):
        return []
    if not return_validator._git_commit_exists(accepted_commit):
        # The ordinary candidate validator reports the missing object with its
        # normal structured error; this helper only adds the reachability gate.
        return []
    if not return_validator._git_is_ancestor(accepted_commit, "HEAD"):
        return [
            "decision.accepted_commit: must be contained in the current checkout HEAD"
        ]
    return []


def _is_allowed_platform_alias(path: Path) -> bool:
    """Keep only the documented macOS temporary-directory alias usable."""
    try:
        return path == Path("/var") and path.resolve(strict=True) == Path("/private/var")
    except OSError:
        return False


def parent_has_symlink(path: Path) -> bool:
    """Reject mutable parent links, including arbitrary filesystem-root links."""
    current = Path(os.path.abspath(path.parent))
    while True:
        if current.is_symlink():
            if not _is_allowed_platform_alias(current):
                return True
            current = current.resolve(strict=True)
            continue
        if current.parent == current:
            return False
        current = current.parent


def path_has_symlink_component(path: Path) -> bool:
    """Reject input files that escape through a symlinked path component."""
    if path.is_symlink():
        return True
    current = Path(os.path.abspath(path.parent))
    while True:
        if current.is_symlink():
            if not _is_allowed_platform_alias(current):
                return True
            current = current.resolve(strict=True)
            continue
        if current.parent == current:
            return False
        current = current.parent


def write_new_file(path: Path, payload: bytes) -> str | None:
    """Publish a complete ``path`` once without exposing a partial artifact."""
    if parent_has_symlink(path):
        return "output parent must not contain a symbolic link"
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        return f"could not create output parent: {exc}"
    if parent_has_symlink(path):
        return "output parent must not contain a symbolic link"

    descriptor = -1
    staged_path: Path | None = None
    try:
        descriptor, staged_name = tempfile.mkstemp(
            prefix=f".{path.name}.",
            suffix=".tmp",
            dir=path.parent,
        )
        staged_path = Path(staged_name)
    except OSError as exc:
        return f"could not stage output: {exc}"

    try:
        try:
            with os.fdopen(descriptor, "wb") as output:
                descriptor = -1
                output.write(payload)
                output.flush()
                os.fchmod(output.fileno(), 0o644)
                os.fsync(output.fileno())
        except OSError as exc:
            return f"could not write output: {exc}"

        if parent_has_symlink(path):
            return "output parent must not contain a symbolic link"
        try:
            os.link(staged_path, path, follow_symlinks=False)
        except FileExistsError:
            if path.is_symlink():
                return "output path must not be a symbolic link"
            return "output already exists"
        except OSError as exc:
            return f"could not publish output: {exc}"
        return None
    finally:
        if descriptor >= 0:
            try:
                os.close(descriptor)
            except OSError:
                pass
        if staged_path is not None:
            try:
                staged_path.unlink()
            except FileNotFoundError:
                pass
            except OSError:
                pass


def build_candidate(
    submitted: Any,
    decision: Any,
    *,
    repository_identity: dict[str, Any] | None = None,
) -> tuple[dict[str, Any] | None, list[str]]:
    errors: list[str] = []
    if not isinstance(submitted, dict):
        return None, ["submitted return must be a JSON object"]
    if not isinstance(decision, dict):
        return None, ["acceptance decision must be a JSON object"]

    unknown = sorted(set(decision) - DECISION_FIELDS)
    missing = sorted(DECISION_FIELDS - set(decision))
    errors.extend(f"decision: unknown field {field!r}" for field in unknown)
    errors.extend(f"decision: missing required field {field!r}" for field in missing)
    if decision.get("schema") != DECISION_SCHEMA:
        errors.append(f"decision.schema: must equal {DECISION_SCHEMA}")

    submitted_errors = return_validator.validate_document(
        submitted,
        require_submitted=True,
        check_git=True,
        repository_identity=repository_identity,
    )
    errors.extend(f"submitted: {error}" for error in submitted_errors)
    if submitted.get("repository", {}).get("proposed_commit") is None:
        errors.append("submitted.repository.proposed_commit: acceptance requires a proposed commit")
    proposed_commit = submitted.get("repository", {}).get("proposed_commit")
    accepted_commit = decision.get("accepted_commit")
    if (
        isinstance(proposed_commit, str)
        and isinstance(accepted_commit, str)
        and return_validator._git_commit_exists(accepted_commit)
        and not return_validator._git_is_ancestor(proposed_commit, accepted_commit)
    ):
        errors.append(
            "decision.accepted_commit: must descend from "
            "submitted.repository.proposed_commit"
        )

    review = decision.get("review")
    if not isinstance(review, dict):
        errors.append("decision.review: must be an object")
    else:
        unknown_review = sorted(set(review) - REVIEW_NAMES)
        missing_review = sorted(REVIEW_NAMES - set(review))
        errors.extend(f"decision.review: unknown decision {name!r}" for name in unknown_review)
        errors.extend(f"decision.review: missing decision {name!r}" for name in missing_review)
        handoff = review.get("accepted_handoff")
        if not isinstance(handoff, dict) or handoff.get("state") != "accepted":
            errors.append("decision.review.accepted_handoff.state: must equal accepted")
        elif not handoff.get("authority_ref"):
            errors.append(
                "decision.review.accepted_handoff.authority_ref: explicit acceptance authority is required"
            )
    errors.extend(acceptance_chronology_errors(submitted, review))
    if (
        isinstance(accepted_commit, str)
        and return_validator._git_commit_exists(accepted_commit)
    ):
        errors.extend(acceptance_authority_errors(accepted_commit, review))
    errors.extend(accepted_commit_checkout_errors(accepted_commit))

    if return_validator.public_safety_errors(decision):
        errors.extend(
            f"decision: {error}" for error in return_validator.public_safety_errors(decision)
        )
    if errors:
        return None, sorted(set(errors))

    candidate = copy.deepcopy(submitted)
    candidate["record_kind"] = "accepted_receipt"
    candidate["repository"]["accepted_commit"] = decision["accepted_commit"]
    candidate["review"] = copy.deepcopy(review)
    accepted_errors = return_validator.validate_document(
        candidate,
        require_accepted=True,
        check_git=True,
        repository_identity=repository_identity,
    )
    if accepted_errors:
        return None, [f"accepted candidate: {error}" for error in accepted_errors]
    return candidate, []


def build_decision_template(
    submitted: Any,
    *,
    repository_identity: dict[str, Any] | None = None,
) -> tuple[dict[str, Any] | None, list[str]]:
    if not isinstance(submitted, dict):
        return None, ["submitted return must be a JSON object"]
    errors = return_validator.validate_document(
        submitted,
        require_submitted=True,
        check_git=True,
        repository_identity=repository_identity,
    )
    if submitted.get("repository", {}).get("proposed_commit") is None:
        errors.append("submitted.repository.proposed_commit: acceptance requires a proposed commit")
    if errors:
        return None, [f"submitted: {error}" for error in sorted(set(errors))]
    return {
        "schema": DECISION_SCHEMA,
        "accepted_commit": None,
        "review": copy.deepcopy(submitted["review"]),
    }, []


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("submitted", type=Path, help="validated submitted-return JSON")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--decision", type=Path, help="explicit reviewer decision JSON")
    mode.add_argument(
        "--write-decision-template",
        type=Path,
        help="write a non-accepting decision template copied from the submitted review state",
    )
    parser.add_argument("--output", type=Path, help="new accepted-receipt JSON path")
    parser.add_argument(
        "--repository-identity",
        type=Path,
        default=repository_identity_contract.DEFAULT_IDENTITY_PATH,
        help="current public repository identity authority (simulation may supply an isolated file)",
    )
    parser.add_argument(
        "--route-memory-receipt",
        type=Path,
        help="digest-bound route-memory sidecar for the submitted return",
    )
    parser.add_argument(
        "--require-route-memory-receipt",
        action="store_true",
        help="require and validate the route-memory sidecar before acceptance",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.decision is not None and args.output is None:
        parser.error("--output is required with --decision")
    if args.write_decision_template is not None and args.output is not None:
        parser.error("--output cannot be combined with --write-decision-template")
    destination = args.write_decision_template or args.output
    if destination is None:
        parser.error("one of --decision or --write-decision-template is required")
    result_schema = TEMPLATE_RESULT_SCHEMA if args.write_decision_template else RESULT_SCHEMA
    if destination.is_symlink():
        print(
            json.dumps(
                {
                    "schema": result_schema,
                    "valid": False,
                    "errors": ["output path must not be a symbolic link"],
                }
            )
        )
        return 2
    if destination.exists():
        print(json.dumps({"schema": result_schema, "valid": False, "errors": ["output already exists"]}))
        return 2
    input_paths = [("submitted return", args.submitted)]
    if args.decision is not None:
        input_paths.append(("acceptance decision", args.decision))
    for label, path in input_paths:
        if path_has_symlink_component(path):
            print(
                json.dumps(
                    {
                        "schema": result_schema,
                        "valid": False,
                        "errors": [f"{label} path must not traverse symbolic links"],
                    },
                    sort_keys=True,
                )
            )
            return 2
    try:
        submitted = load_json(args.submitted)
        identity_contract = repository_identity_contract.load_identity(
            args.repository_identity
        )
    except (
        OSError,
        UnicodeError,
        ValueError,
        json.JSONDecodeError,
        repository_identity_contract.IdentityError,
    ) as exc:
        print(json.dumps({"schema": result_schema, "valid": False, "errors": [str(exc)]}))
        return 2

    route_binding, route_errors, route_input_error = route_memory_binding_errors(
        submitted,
        args.route_memory_receipt,
        required=args.require_route_memory_receipt,
    )
    if route_errors:
        print(
            json.dumps(
                {
                    "schema": result_schema,
                    "valid": False,
                    "errors": sorted(set(route_errors)),
                },
                sort_keys=True,
            )
        )
        return 2 if route_input_error else 1
    route_summary = (
        {"route_memory_binding": route_memory_binding_summary(route_binding)}
        if route_binding is not None
        else {}
    )

    if args.write_decision_template is not None:
        template, errors = build_decision_template(
            submitted,
            repository_identity=identity_contract,
        )
        if template is None:
            print(json.dumps({"schema": TEMPLATE_RESULT_SCHEMA, "valid": False, "errors": errors}, sort_keys=True))
            return 1
        payload = canonical(template)
        output_error = write_new_file(destination, payload)
        if output_error is not None:
            print(
                json.dumps(
                    {
                        "schema": TEMPLATE_RESULT_SCHEMA,
                        "valid": False,
                        "errors": [output_error],
                    },
                    sort_keys=True,
                )
            )
            return 2
        print(
            json.dumps(
                {
                    "schema": TEMPLATE_RESULT_SCHEMA,
                    "valid": True,
                    "return_id": submitted["return_id"],
                    "template": destination.name,
                    "path_policy": "basename_only_for_portable_cli_output",
                    "authority_boundary": (
                        "The template preserves recorded review state and asserts no acceptance; "
                        "a reviewer must explicitly complete every applicable decision."
                    ),
                    **route_summary,
                },
                sort_keys=True,
            )
        )
        return 0

    if args.decision is None or args.output is None:
        parser.error("--decision and --output are required for accepted receipt generation")
    try:
        decision = load_json(args.decision)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        print(json.dumps({"schema": RESULT_SCHEMA, "valid": False, "errors": [str(exc)]}))
        return 2
    candidate, errors = build_candidate(
        submitted,
        decision,
        repository_identity=identity_contract,
    )
    if candidate is None:
        print(json.dumps({"schema": RESULT_SCHEMA, "valid": False, "errors": errors}, sort_keys=True))
        return 1

    payload = canonical(candidate)
    output_error = write_new_file(destination, payload)
    if output_error is not None:
        print(
            json.dumps(
                {
                    "schema": RESULT_SCHEMA,
                    "valid": False,
                    "errors": [output_error],
                },
                sort_keys=True,
            )
        )
        return 2
    print(
        json.dumps(
            {
                "schema": RESULT_SCHEMA,
                "valid": True,
                "return_id": candidate["return_id"],
                "output": destination.name,
                "path_policy": "basename_only_for_portable_cli_output",
                "sha256": "sha256:" + hashlib.sha256(payload).hexdigest(),
                "authority_boundary": (
                    "The reviewer decision is explicit input; this command does not grant acceptance, "
                    "mathematical review, claim promotion, or release inclusion."
                ),
                **route_summary,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
