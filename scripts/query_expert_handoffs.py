#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Query exact mathematical and systems handoffs, or validate a human response.

The default is a bounded six-question index.  Open one complete handoff with
``--question QUESTION_ID``; use ``--domain systems`` for the complete
ten-minute reader protocol.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from datetime import date
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parent.parent
FRONTIER = ROOT / "docs" / "semantic" / "frontier.json"
ATLAS = ROOT / "docs" / "declaration_atlas.json"
PROTOCOL = ROOT / "docs" / "expert_review_protocol.json"
SCHEMA = "plectis_expert_review_protocol_v1"
MATH_DOMAIN = "mathematics"
SYSTEMS_DOMAIN = "systems"
DOMAINS = (MATH_DOMAIN, SYSTEMS_DOMAIN)
FROZEN_PROBLEMS = frozenset(
    {"68", "243", "249", "251", "257", "269", "1041", "1049"}
)
REQUIRED_QUESTION_FIELDS = (
    "id",
    "domain",
    "classification",
    "status",
    "exact_ask",
    "payoff",
    "boundary",
    "known_obstruction",
    "current_hypothesis",
)


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def mathematical_questions() -> list[dict[str, Any]]:
    rows = load_json(FRONTIER).get("expert_questions", [])
    declarations = {
        (row["module"], row["name"]): row
        for row in load_json(ATLAS).get("declarations", [])
    }
    # Coordinates are navigation data, not authored mathematical content.
    # Resolve them from the exhaustive live atlas so every expert-query surface
    # survives harmless source movement in the same way as semantic_corpus.json.
    for question in rows:
        for consumer in question.get("consumer_declarations", []):
            declaration = declarations.get(
                (consumer.get("module"), consumer.get("declaration"))
            )
            if declaration is not None:
                consumer["line"] = declaration["line"]
    return [{"domain": MATH_DOMAIN, **row} for row in rows]


def systems_questions() -> list[dict[str, Any]]:
    return list(load_json(PROTOCOL).get("questions", []))


def all_questions() -> list[dict[str, Any]]:
    return [*mathematical_questions(), *systems_questions()]


def route_memory_handoff(row: Mapping[str, Any]) -> dict[str, Any]:
    """Expose a problem-bound resume command without inventing a route.

    Expert questions are research handoffs, not canonical programme routes.
    They therefore carry a selector-only navigation edge; the command must be
    run in the current checkout to resolve route IDs and source digests before
    any resume state is accepted.
    """
    raw_problem = row.get("problem")
    token = str(raw_problem).strip() if isinstance(raw_problem, (str, int)) else ""
    if not re.fullmatch(r"\d+", token) or token not in FROZEN_PROBLEMS:
        return {
            "status": "unbound",
            "bindings": [],
            "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
            "boundary": (
                "An expert question is not a canonical programme route; no "
                "resume route was invented."
            ),
            "unbound_reason": (
                "question does not carry one of the frozen public problem selectors"
            ),
        }
    return {
        "status": "unbound",
        "problem_number": int(token),
        "bindings": [],
        "command": f"python3 scripts/query_route_memory.py --problem {token}",
        "authority_posture": "derived_resume_handoff_not_claim_or_proof_authority",
        "identity_contract": (
            "Run the selector command in the current tracked checkout before "
            "resume: it resolves canonical route IDs and current source digests, "
            "and rejects stale or cross-problem packets."
        ),
        "boundary": (
            "This selector is a navigation handoff only; it does not bind an "
            "expert question to a programme route or promote a claim."
        ),
        "unbound_reason": (
            "expert question selects a problem but not a canonical programme "
            "route; no resume route was invented"
        ),
    }


def paper_source_handoff(problem_number: str) -> dict[str, Any]:
    """Expose the exact dedicated-paper source selector for a problem handoff."""
    problem = next(
        (
            row
            for row in load_json(ROOT / "docs" / "problems.json").get(
                "problems", []
            )
            if str(row.get("erdos_number")) == problem_number
        ),
        None,
    )
    paper = problem.get("paper", {}) if isinstance(problem, dict) else {}
    source = paper.get("source") if isinstance(paper, dict) else None
    if not isinstance(source, str) or not source:
        return {
            "status": "unavailable",
            "source": None,
            "command": None,
            "authority_posture": (
                "derived_paper_navigation_not_claim_or_proof_authority"
            ),
            "boundary": (
                "The public problem roster supplies no dedicated paper source; "
                "no paper route was invented."
            ),
        }
    return {
        "status": "bound",
        "source": source,
        "command": f"python3 scripts/query_corpus.py --paper-source {source}",
        "authority_posture": (
            "derived_paper_navigation_not_claim_or_proof_authority"
        ),
        "identity_contract": (
            "The selector resolves the complete exact anchor census for the "
            "dedicated paper in the current tracked checkout."
        ),
        "boundary": (
            "This selector is an exposition-navigation handoff only; it does "
            "not promote a paper anchor into a claim or proof."
        ),
    }


def problem_route_handoff(row: Mapping[str, Any]) -> dict[str, Any]:
    """Expose the canonical problem packet without inventing a programme route."""
    raw_problem = row.get("problem")
    token = str(raw_problem).strip() if isinstance(raw_problem, (str, int)) else ""
    if not re.fullmatch(r"\d+", token) or token not in FROZEN_PROBLEMS:
        return {
            "status": "unbound",
            "authority_posture": (
                "derived_problem_navigation_not_claim_or_proof_authority"
            ),
            "boundary": (
                "The expert question does not select a public problem route; no "
                "problem route was invented."
            ),
            "unbound_reason": (
                "question does not carry one of the frozen public problem selectors"
            ),
        }
    return {
        "status": "bound",
        "problem_number": int(token),
        "command": f"python3 scripts/query_corpus.py --route erdos_{token}",
        "paper_source": paper_source_handoff(token),
        "authority_posture": (
            "derived_problem_navigation_not_claim_or_proof_authority"
        ),
        "identity_contract": (
            "The canonical problem route expands the paper record, every "
            "review-matrix result family, declaration handles where supplied, "
            "and exact open obligations."
        ),
        "boundary": (
            "This problem route is navigation context only; it does not bind an "
            "expert question to a programme route or promote a claim."
        ),
    }


def respondent_view(row: dict[str, Any]) -> dict[str, Any]:
    """Return the handoff without evaluator-only expected answers."""
    if row.get("domain") != SYSTEMS_DOMAIN:
        view = dict(row)
        view["route_memory"] = route_memory_handoff(row)
        view["problem_route"] = problem_route_handoff(row)
        return view
    return {
        key: value
        for key, value in row.items()
        if key not in {"acceptance", "review_template"}
    }


def compact_respondent_view(row: dict[str, Any]) -> dict[str, Any]:
    """Return enough to choose a handoff before opening its full packet."""
    result = {
        "id": row["id"],
        "domain": row["domain"],
        "problem": row.get("problem"),
        "classification": row["classification"],
        "status": row["status"],
        "exact_ask": row["exact_ask"],
        "boundary": row["boundary"],
        "current_hypothesis": row["current_hypothesis"],
        "hypothesis_confidence": row["hypothesis_confidence"],
        "plausible_alternatives": [
            {
                "id": alternative["id"],
                "statement": alternative["statement"],
            }
            for alternative in row["plausible_alternatives"]
        ],
        "current_evidence": row["current_evidence"],
        "discriminating_evidence": row["discriminating_evidence"],
        "checked_consumers": (
            [
                (
                    f"{consumer['module']}:{consumer['line']}:"
                    f"{consumer['declaration']}"
                )
                for consumer in row.get("consumer_declarations", [])
            ]
            or [row.get("consumer", {}).get("command")]
        ),
        "detail_command": (
            "python3 scripts/query_expert_handoffs.py --question "
            f"{row['id']}"
        ),
    }
    if row.get("domain") == MATH_DOMAIN:
        result["route_memory"] = route_memory_handoff(row)
        result["problem_route"] = problem_route_handoff(row)
    return result


def protocol_errors() -> list[str]:
    errors: list[str] = []
    protocol = load_json(PROTOCOL)
    frontier = load_json(FRONTIER)
    if protocol.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA}")

    questions = all_questions()
    ids = [row.get("id") for row in questions]
    duplicates = sorted(qid for qid, count in Counter(ids).items() if count > 1)
    if duplicates:
        errors.append(f"duplicate question ids: {duplicates}")
    if len(mathematical_questions()) != 5:
        errors.append("mathematical handoff count must remain 5")
    if not systems_questions():
        errors.append("at least one systems handoff is required")

    for row in questions:
        qid = str(row.get("id") or "<missing>")
        for field in REQUIRED_QUESTION_FIELDS:
            if not row.get(field):
                errors.append(f"{qid}: missing {field}")
        if row.get("domain") not in DOMAINS:
            errors.append(f"{qid}: unsupported domain {row.get('domain')!r}")
        if row.get("status") != "OPEN":
            errors.append(f"{qid}: status must be OPEN")
        if row.get("hypothesis_confidence") not in {"low", "medium", "high"}:
            errors.append(f"{qid}: invalid hypothesis_confidence")
        alternatives = row.get("plausible_alternatives")
        if not isinstance(alternatives, list) or len(alternatives) < 2:
            errors.append(f"{qid}: invalid plausible_alternatives")
        elif any(not isinstance(item, dict) for item in alternatives):
            errors.append(f"{qid}: invalid plausible_alternatives")
        elif (
            len({item.get("id") for item in alternatives}) != len(alternatives)
            or any(
                any(
                    not item.get(field)
                    for field in ("id", "statement", "consequence")
                )
                for item in alternatives
            )
        ):
            errors.append(f"{qid}: invalid plausible_alternatives")
        for field in ("current_evidence", "discriminating_evidence"):
            evidence = row.get(field)
            if (
                not isinstance(evidence, list)
                or len(evidence) < 2
                or any(not isinstance(item, str) or not item for item in evidence)
            ):
                errors.append(f"{qid}: invalid {field}")
        measured_artifact = row.get("measured_evidence_artifact")
        measurement_check = row.get("measurement_check_command")
        if bool(measured_artifact) != bool(measurement_check):
            errors.append(
                f"{qid}: measured artifact and check command must occur together"
            )
        elif measured_artifact:
            artifact_path = Path(str(measured_artifact))
            if (
                artifact_path.is_absolute()
                or ".." in artifact_path.parts
                or not (ROOT / artifact_path).is_file()
            ):
                errors.append(f"{qid}: measured artifact is not a repository file")
            command_parts = str(measurement_check).split()
            if (
                len(command_parts) != 3
                or command_parts[0] != "python3"
                or not command_parts[1].startswith("scripts/")
                or command_parts[2] != "--check"
                or not (ROOT / command_parts[1]).is_file()
            ):
                errors.append(f"{qid}: invalid measurement check command")

    for row in systems_questions():
        qid = str(row.get("id") or "<missing>")
        template = row.get("input_template")
        acceptance = row.get("acceptance")
        consumer = row.get("consumer")
        if not isinstance(template, dict) or not template:
            errors.append(f"{qid}: missing input_template")
        if not isinstance(acceptance, dict) or not acceptance:
            errors.append(f"{qid}: missing acceptance contract")
        if not isinstance(consumer, dict) or not consumer.get("command"):
            errors.append(f"{qid}: missing executable consumer")
        elif not consumer.get("final_review_command"):
            errors.append(f"{qid}: missing final review consumer")
        if not row.get("verification_command"):
            errors.append(f"{qid}: missing verification_command")
        manual_fields = row.get("manual_review_fields")
        if not isinstance(manual_fields, list) or not manual_fields:
            errors.append(f"{qid}: missing manual_review_fields")
        rubric = row.get("manual_review_rubric")
        review_template = row.get("review_template")
        if not isinstance(rubric, dict) or not rubric:
            errors.append(f"{qid}: missing manual_review_rubric")
        if not isinstance(review_template, dict) or not review_template:
            errors.append(f"{qid}: missing review_template")
        elif isinstance(rubric, dict) and set(
            review_template.get("criteria", {})
        ) != set(rubric):
            errors.append(f"{qid}: review criteria drifted from manual rubric")
        if isinstance(acceptance, dict):
            lattice = frontier.get("demand_lattice", {})
            expected_substantial = lattice.get("counts", {}).get("substantial")
            expected_equivalent = sum(
                len(group.get("members", []))
                for group in lattice.get("classes", [])
                if group.get("equivalent_to_problem") is True
            )
            if acceptance.get("substantial_antecedents") != expected_substantial:
                errors.append(
                    f"{qid}: substantial antecedent count drifted from demand lattice"
                )
            if acceptance.get("equivalent_antecedents") != expected_equivalent:
                errors.append(
                    f"{qid}: endpoint-equivalent count drifted from demand lattice"
                )
    return errors


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def object_digest(value: Any) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def validate_response(response: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(response, dict):
        return ["response must be a JSON object"]
    qid = response.get("question_id")
    by_id = {row["id"]: row for row in systems_questions()}
    question = by_id.get(qid)
    if question is None:
        return [f"question_id does not select a systems handoff: {qid!r}"]

    template = question["input_template"]
    missing = sorted(set(template) - set(response))
    extra = sorted(set(response) - set(template))
    if missing:
        errors.append(f"missing fields: {missing}")
    if extra:
        errors.append(f"unknown fields: {extra}")

    acceptance = question["acceptance"]
    elapsed = response.get("elapsed_seconds")
    if not _is_int(elapsed) or elapsed < 0:
        errors.append("elapsed_seconds must be a nonnegative integer")
    elif elapsed > acceptance["maximum_elapsed_seconds"]:
        errors.append(
            "elapsed_seconds exceeds "
            f"{acceptance['maximum_elapsed_seconds']}-second contract"
        )

    expected_scalars = {
        "prior_project_context": acceptance["prior_project_context"],
        "problem_249_status": acceptance["problem_status"],
        "problem_257_status": acceptance["problem_status"],
        "farey_bound_provenance": acceptance["farey_bound_provenance"],
        "farey_numerical_delta": acceptance["farey_numerical_delta"],
        "equivalent_antecedents": acceptance["equivalent_antecedents"],
        "substantial_antecedents": acceptance["substantial_antecedents"],
    }
    if not isinstance(response.get("prior_project_context"), bool):
        errors.append("prior_project_context must be a boolean")
    for field in (
        "farey_numerical_delta",
        "equivalent_antecedents",
        "substantial_antecedents",
    ):
        if not _is_int(response.get(field)):
            errors.append(f"{field} must be an integer")
    for field, expected in expected_scalars.items():
        if response.get(field) != expected:
            errors.append(
                f"{field}: expected {expected!r}, got {response.get(field)!r}"
            )

    minimum = acceptance["minimum_nonrestatement_results_per_problem"]
    for problem in ("249", "257"):
        field = f"nonrestatement_results_{problem}"
        values = response.get(field)
        if not isinstance(values, list) or any(
            not isinstance(value, str) or not value.strip() for value in values
        ):
            errors.append(f"{field} must be an array of nonempty descriptions")
            continue
        if len({value.strip().casefold() for value in values}) < minimum:
            errors.append(f"{field} must name at least {minimum} distinct results")

    paths = response.get("source_paths_used")
    if not isinstance(paths, list) or not paths or any(
        not isinstance(path, str) or not path for path in paths
    ):
        errors.append("source_paths_used must be a nonempty array of paths")
    elif any(
        Path(path).is_absolute()
        or ".." in Path(path).parts
        or not (ROOT / path).is_file()
        for path in paths
    ):
        errors.append("source_paths_used must name existing repository files")

    reviewer = response.get("reviewer_identity")
    if not isinstance(reviewer, str) or not reviewer.strip():
        errors.append("reviewer_identity must be a nonempty string")
    reviewed_at = response.get("reviewed_at")
    if not isinstance(reviewed_at, str):
        errors.append("reviewed_at must be an ISO calendar date")
    else:
        try:
            date.fromisoformat(reviewed_at)
        except ValueError:
            errors.append("reviewed_at must be an ISO calendar date")
    revision = response.get("clone_revision")
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        errors.append("clone_revision must be a full lowercase commit id")

    confusing = response.get("first_confusing_surface")
    if not isinstance(confusing, str):
        errors.append("first_confusing_surface must be a string")
    verdict = response.get("verdict_summary")
    if not isinstance(verdict, str) or not verdict.strip():
        errors.append("verdict_summary must be a nonempty string")
    return errors


def validate_review(response: Any, review: Any) -> list[str]:
    response_errors = validate_response(response)
    if response_errors:
        return [f"response: {error}" for error in response_errors]
    if not isinstance(review, dict):
        return ["review must be a JSON object"]

    qid = response["question_id"]
    by_id = {row["id"]: row for row in systems_questions()}
    question = by_id[qid]
    template = question["review_template"]
    missing = sorted(set(template) - set(review))
    extra = sorted(set(review) - set(template))
    errors: list[str] = []
    if missing:
        errors.append(f"review missing fields: {missing}")
    if extra:
        errors.append(f"review has unknown fields: {extra}")
    if review.get("question_id") != qid:
        errors.append("review question_id does not match the response")
    if review.get("response_sha256") != object_digest(response):
        errors.append("review response_sha256 does not bind the supplied response")

    evaluator = review.get("evaluator_identity")
    if not isinstance(evaluator, str) or not evaluator.strip():
        errors.append("evaluator_identity must be a nonempty string")
    evaluated_at = review.get("evaluated_at")
    if not isinstance(evaluated_at, str):
        errors.append("evaluated_at must be an ISO calendar date")
    else:
        try:
            date.fromisoformat(evaluated_at)
        except ValueError:
            errors.append("evaluated_at must be an ISO calendar date")

    for field in ("reviewer_provenance_verified", "timing_provenance_verified"):
        if not isinstance(review.get(field), bool):
            errors.append(f"{field} must be a boolean")

    criteria = review.get("criteria")
    expected_criteria = set(question["manual_review_rubric"])
    if not isinstance(criteria, dict) or set(criteria) != expected_criteria:
        errors.append("review criteria must match the manual rubric exactly")
        criteria_values: list[bool] = []
    else:
        criteria_values = list(criteria.values())
        if any(not isinstance(value, bool) for value in criteria_values):
            errors.append("every review criterion must be a boolean")

    notes = review.get("review_notes")
    if not isinstance(notes, str):
        errors.append("review_notes must be a string")
    outcome = review.get("final_outcome")
    if outcome not in {"accepted", "needs_revision"}:
        errors.append("final_outcome must be accepted or needs_revision")
    elif outcome == "accepted":
        if (
            review.get("reviewer_provenance_verified") is not True
            or review.get("timing_provenance_verified") is not True
            or not criteria_values
            or not all(value is True for value in criteria_values)
        ):
            errors.append(
                "accepted outcome requires verified provenance, timing and all criteria"
            )
    elif (
        criteria_values
        and all(value is True for value in criteria_values)
        and review.get("reviewer_provenance_verified") is True
        and review.get("timing_provenance_verified") is True
    ):
        errors.append("needs_revision must identify at least one failed condition")
    elif not isinstance(notes, str) or not notes.strip():
        errors.append("needs_revision requires review_notes")
    return errors


def question_packet(
    domain: str | None, question_id: str | None = None
) -> dict[str, Any]:
    rows = all_questions()
    if domain:
        rows = [row for row in rows if row["domain"] == domain]
    if question_id:
        rows = [row for row in rows if row["id"] == question_id]
        if not rows:
            raise ValueError(f"no expert handoff {question_id!r}")
    full_packet = bool(question_id) or (domain == SYSTEMS_DOMAIN and len(rows) == 1)
    domain_counts = Counter(row["domain"] for row in rows)
    return {
        "question": "exact inputs requested from human experts",
        "rule": (
            "Every row names the requested input, current guess, alternatives, "
            "discriminating evidence, consumer, payoff and boundary."
        ),
        "packet_kind": "full_question" if full_packet else "compact_index",
        "count": len(rows),
        "domain_counts": dict(sorted(domain_counts.items())),
        "results": [
            respondent_view(row) if full_packet else compact_respondent_view(row)
            for row in rows
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--domain", choices=DOMAINS)
    parser.add_argument("--question", metavar="QUESTION_ID")
    parser.add_argument("--template", metavar="QUESTION_ID")
    parser.add_argument("--response", type=Path, metavar="RESPONSE.json")
    parser.add_argument("--review-template", metavar="QUESTION_ID")
    parser.add_argument(
        "--review",
        nargs=2,
        type=Path,
        metavar=("RESPONSE.json", "REVIEW.json"),
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    exclusive = (
        args.question,
        args.template,
        args.response,
        args.review_template,
        args.review,
        args.check,
    )
    if sum(bool(value) for value in exclusive) > 1:
        parser.error(
            "--question, --template, --response, --review-template, --review "
            "and --check are mutually exclusive"
        )

    if args.check:
        errors = protocol_errors()
        if errors:
            for error in errors:
                print(f"FAIL {error}")
            return 1
        print(
            "expert handoff protocol: 5 mathematical questions and "
            f"{len(systems_questions())} systems question(s) verified"
        )
        return 0

    if args.template:
        by_id = {row["id"]: row for row in systems_questions()}
        question = by_id.get(args.template)
        if question is None:
            parser.error("--template must name a systems handoff")
        print(json.dumps(question["input_template"], indent=2, ensure_ascii=False))
        return 0

    if args.review_template:
        by_id = {row["id"]: row for row in systems_questions()}
        question = by_id.get(args.review_template)
        if question is None:
            parser.error("--review-template must name a systems handoff")
        print(json.dumps(question["review_template"], indent=2, ensure_ascii=False))
        return 0

    if args.response:
        response = load_json(args.response)
        errors = validate_response(response)
        receipt = {
            "question_id": response.get("question_id"),
            "response_sha256": object_digest(response),
            "status": (
                "structurally_accepted_pending_content_review"
                if not errors
                else "discrepancies"
            ),
            "errors": errors,
            "manual_review_fields": (
                []
                if errors
                else next(
                    row["manual_review_fields"]
                    for row in systems_questions()
                    if row["id"] == response.get("question_id")
                )
            ),
            "boundary": (
                "This receipt checks scalar and structural fields and lists "
                "free prose for manual review; it does not authenticate the "
                "reviewer, timing, mathematics or priority."
            ),
        }
        print(json.dumps(receipt, indent=2, ensure_ascii=False))
        return 0 if not errors else 1

    if args.review:
        response = load_json(args.review[0])
        review = load_json(args.review[1])
        errors = validate_review(response, review)
        receipt = {
            "question_id": (
                response.get("question_id")
                if isinstance(response, dict)
                else None
            ),
            "response_sha256": object_digest(response),
            "status": (
                review.get("final_outcome")
                if not errors and isinstance(review, dict)
                else "discrepancies"
            ),
            "errors": errors,
            "boundary": (
                "This is a reviewed communication receipt, not a verdict on "
                "mathematical correctness, priority, novelty or either problem."
            ),
        }
        print(json.dumps(receipt, indent=2, ensure_ascii=False))
        return 0 if not errors else 1

    try:
        packet = question_packet(args.domain, args.question)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps(packet, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
