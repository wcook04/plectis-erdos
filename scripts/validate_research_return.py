#!/usr/bin/env python3
"""Validate a provider-neutral public research return or accepted receipt.

The validator is deliberately standard-library only. It validates recorded
evidence; it never executes commands from a return and never treats model or
provider disclosure as mathematical evidence.
"""

from __future__ import annotations

import argparse
import copy
import datetime as dt
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import repository_identity as repository_identity_contract
import route_memory_receipt
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
IDENTITY_PATH = repository_identity_contract.DEFAULT_IDENTITY_PATH
DEFAULT_REPOSITORY_IDENTITY = repository_identity_contract.load_identity(IDENTITY_PATH)
SCHEMA_PATH = ROOT / DEFAULT_REPOSITORY_IDENTITY["contracts"]["current_schema_path"]
CANONICAL_REPOSITORY_ORIGIN = DEFAULT_REPOSITORY_IDENTITY["current"]["origin"]
PATH_POLICY = "repository_relative_or_basename_for_portable_cli_output"
GIT_COMMAND_TIMEOUT_SECONDS = 30
GIT_CONTEXT_KEYS = frozenset(
    {
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_CEILING_DIRECTORIES",
        "GIT_DISCOVERY_ACROSS_FILESYSTEM",
    }
)
GIT_PROCESS_CONTROL_KEYS = frozenset(
    {
        "GIT_TRACE",
        "GIT_TRACE2",
        "GIT_TRACE_PACKET",
        "GIT_TRACE_PERFORMANCE",
        "GIT_TRACE_SETUP",
        "GIT_TRACE_CURL",
        "GIT_TRACE2_EVENT",
        "GIT_TRACE2_PERF",
        "GIT_SSH",
        "GIT_SSH_COMMAND",
        "GIT_SSH_VARIANT",
        "GIT_EXTERNAL_DIFF",
        "GIT_DIFF_OPTS",
        "GIT_EDITOR",
        "GIT_SEQUENCE_EDITOR",
        "GIT_MERGE_AUTOEDIT",
    }
)
PYTHON_CONTEXT_KEYS = frozenset(
    {
        "PYTHONPATH",
        "PYTHONHOME",
        "PYTHONUSERBASE",
        "PYTHONSTARTUP",
        "PYTHONBREAKPOINT",
        "PYTHONWARNINGS",
    }
)
PYTHON_STABILITY_KEYS = frozenset({"PYTHONHASHSEED", "PYTHONOPTIMIZE", "PYTHONUTF8"})
LOCALE_KEYS = frozenset({"LC_ALL", "LANG", "LANGUAGE"})


def route_memory_binding_summary(value: dict[str, Any]) -> dict[str, Any]:
    """Expose verified route identity without copying route prose or locators."""
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


def path_has_symlink_component(path: Path) -> bool:
    """Reject return inputs that escape through a symlinked path component."""
    if path.is_symlink():
        return True
    current = Path(os.path.abspath(path.parent))
    root = Path(current.anchor)
    while True:
        if current.is_symlink():
            # macOS exposes its temporary area through /var -> /private/var.
            # Keep that platform-owned alias usable while rejecting every
            # other symlink, including arbitrary filesystem-root parents.
            try:
                platform_alias = (
                    current == Path("/var")
                    and current.resolve(strict=True) == Path("/private/var")
                )
            except OSError:
                platform_alias = False
            if not platform_alias:
                return True
            current = current.resolve(strict=True)
            continue
        if current.parent == current:
            return False
        current = current.parent


def portable_path_reference(path: Path | None) -> str | None:
    """Expose a stable repository path or basename, never local topology."""
    if path is None:
        return None
    try:
        absolute = Path(os.path.abspath(os.fspath(path)))
        relative = absolute.relative_to(ROOT.resolve())
    except (OSError, ValueError, TypeError):
        absolute = Path(os.fspath(path))
        return absolute.name or None
    return relative.as_posix() or "."


def git_environment() -> dict[str, str]:
    """Run Git validation through the canonical environment-neutral boundary."""
    return singleflight.command_environment()


COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
RETURN_ID_RE = re.compile(r"^rr-[a-z0-9][a-z0-9-]{2,80}$")
PRIVATE_RE = re.compile(r"(?:/Users/|/home/|[A-Za-z]:\\\\|(?:^|/)ai_workflow(?:/|$))")
SECRET_RE = re.compile(
    r"(?:gh[pousr]_[A-Za-z0-9]{20,}|sk-[A-Za-z0-9]{20,}|"
    r"AKIA[0-9A-Z]{16}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----)"
)
OVERCLAIM_RE = re.compile(
    r"\b(?:solves|resolved|proves)\s+(?:the\s+)?(?:universal\s+)?"
    r"(?:erd[oő]s\s+)?(?:problem\s+)?#?\d+\b",
    re.IGNORECASE,
)
# Evidence commands are recorded strings, never executable input.  When a
# command explicitly carries the public ``--problem`` selector, bind that
# declaration to the return frontier so a copied command cannot silently
# provide evidence for a different problem.
PROBLEM_SELECTOR_RE = re.compile(r"(?<![A-Za-z0-9_])--problem(?:=|\s+)(\d+)(?!\d)")
PROBLEMS = {68, 243, 249, 251, 257, 269, 1041, 1049}
RESULT_CLASSES = {"checked_positive", "negative", "inconclusive", "corrective"}
CLAIM_CEILINGS = {
    "formalized_proposition",
    "verified_finite_instance",
    "conditional_reduction",
    "documentation_correction",
    "negative_for_bounded_route",
    "inconclusive_attempt",
    "cited_only",
    "open",
    "validation_fixture_only",
}
DISPOSITIONS = {
    "accept_handoff",
    "review_correction",
    "consider_problem_proposition",
    "consider_core_promotion",
    "no_promotion",
    "not_requested",
}
CORRECTION_DISPOSITIONS = {"retain", "supersede", "withdraw", "request_review"}
REVIEW_STATES = {
    "structural_validation": {"pending", "valid", "invalid"},
    "reproduction": {"pending", "reproduced", "not_reproduced", "not_required"},
    "mathematical_review": {"pending", "approved", "rejected", "not_required"},
    "claim_boundary_review": {"pending", "approved", "rejected", "not_required"},
    "accepted_handoff": {"pending", "accepted", "rejected"},
    "problem_owned_proposition": {"not_requested", "pending", "accepted", "rejected"},
    "core_promotion": {"not_requested", "pending", "accepted", "rejected"},
    "tagged_release_inclusion": {"not_requested", "pending", "included", "rejected"},
}


def public_safety_errors(value: Any) -> list[str]:
    """Return public-package safety failures without executing any content."""
    text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
    errors = []
    if PRIVATE_RE.search(text):
        errors.append("contains a private path or private-repository reference")
    if SECRET_RE.search(text):
        errors.append("contains material shaped like a credential or private key")
    return errors


class Validation:
    def __init__(self) -> None:
        self.errors: list[str] = []

    def error(self, path: str, message: str) -> None:
        self.errors.append(f"{path}: {message}")

    def object(
        self,
        value: Any,
        path: str,
        required: set[str],
        allowed: set[str] | None = None,
    ) -> dict[str, Any] | None:
        if not isinstance(value, dict):
            self.error(path, "must be an object")
            return None
        missing = sorted(required - value.keys())
        for key in missing:
            self.error(path, f"missing required field {key!r}")
        if allowed is not None:
            for key in sorted(value.keys() - allowed):
                self.error(path, f"unknown field {key!r}")
        return value

    def string(self, value: Any, path: str, *, nonempty: bool = True) -> str | None:
        if not isinstance(value, str):
            self.error(path, "must be a string")
            return None
        if nonempty and not value.strip():
            self.error(path, "must not be empty")
        return value

    def string_list(self, value: Any, path: str, *, nonempty: bool = False) -> list[str]:
        if not isinstance(value, list):
            self.error(path, "must be an array")
            return []
        if nonempty and not value:
            self.error(path, "must contain at least one item")
        for index, item in enumerate(value):
            self.string(item, f"{path}[{index}]")
        return [item for item in value if isinstance(item, str)]


def _date_time(value: Any, path: str, check: Validation, *, nullable: bool = False) -> None:
    if value is None and nullable:
        return
    text = check.string(value, path)
    if text is None:
        return
    try:
        parsed = dt.datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError:
        check.error(path, "must be an ISO-8601 date-time")
        return
    if parsed.tzinfo is None:
        check.error(path, "must include an explicit timezone")


def _commit(value: Any, path: str, check: Validation, *, nullable: bool = False) -> None:
    if value is None and nullable:
        return
    if not isinstance(value, str) or not COMMIT_RE.fullmatch(value):
        check.error(path, "must be a full lowercase 40-character commit")


def _git_commit_exists(commit: str) -> bool:
    completed = _run_git(
        ["cat-file", "-e", f"{commit}^{{commit}}"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return completed is not None and completed.returncode == 0


def _git_is_ancestor(ancestor: str, descendant: str) -> bool:
    completed = _run_git(
        ["merge-base", "--is-ancestor", ancestor, descendant],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return completed is not None and completed.returncode == 0


def _run_git(
    args: list[str], *, stdout: int, stderr: int
) -> subprocess.CompletedProcess[bytes] | None:
    """Run a validator Git query with a bounded failure boundary."""
    try:
        return subprocess.run(
            ["git", *args],
            cwd=ROOT,
            stdout=stdout,
            stderr=stderr,
            check=False,
            env=git_environment(),
            timeout=GIT_COMMAND_TIMEOUT_SECONDS,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None


def _git_changed_paths(starting_commit: str, ending_commit: str) -> set[str] | None:
    completed = _run_git(
        [
            "diff", "--name-only", "--no-renames", "-z",
            starting_commit, ending_commit, "--",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if completed is None or completed.returncode != 0:
        return None
    return {
        path.decode("utf-8", errors="surrogateescape")
        for path in completed.stdout.split(b"\0")
        if path
    }


def _git_path_exists(commit: str, path: str) -> bool:
    completed = _run_git(
        ["cat-file", "-e", f"{commit}:{path}"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return completed is not None and completed.returncode == 0


def _relative_path(value: Any, path: str, check: Validation) -> None:
    text = check.string(value, path)
    if text is None:
        return
    candidate = Path(text)
    if (
        candidate.is_absolute()
        or "\\" in text
        or ".." in candidate.parts
        or not candidate.parts
    ):
        check.error(path, "must be a repository-relative path without '..' or backslashes")
    if candidate.parts and candidate.parts[0] == ".git":
        check.error(path, "must not target Git internals")


def _decision(value: Any, name: str, check: Validation) -> dict[str, Any] | None:
    path = f"review.{name}"
    required = {"state", "reviewer", "decided_at", "authority_ref", "notes"}
    decision = check.object(value, path, required, required)
    if decision is None:
        return None
    state = check.string(decision.get("state"), f"{path}.state")
    if state not in REVIEW_STATES[name]:
        check.error(f"{path}.state", f"must be one of {sorted(REVIEW_STATES[name])}")
    for key in ("reviewer", "authority_ref"):
        item = decision.get(key)
        if item is not None:
            check.string(item, f"{path}.{key}")
    _date_time(decision.get("decided_at"), f"{path}.decided_at", check, nullable=True)
    check.string(decision.get("notes"), f"{path}.notes", nonempty=False)
    terminal = state not in {"pending", "not_requested"}
    if terminal and state not in {"not_required"}:
        if not decision.get("reviewer") or not decision.get("decided_at"):
            check.error(path, "terminal decisions require reviewer and decided_at")
    return decision


def _validate_identity(value: Any, check: Validation) -> dict[str, Any] | None:
    allowed = {"contributor", "operator", "model_system", "provider", "material_collaborators"}
    identity = check.object(
        value,
        "identity",
        {"contributor", "operator", "material_collaborators"},
        allowed,
    )
    if identity is None:
        return None
    contributor = check.object(
        identity.get("contributor"),
        "identity.contributor",
        {"name"},
        {"name", "handle", "identifiers"},
    )
    if contributor:
        check.string(contributor.get("name"), "identity.contributor.name")
        if contributor.get("handle") is not None:
            check.string(contributor["handle"], "identity.contributor.handle")
        if "identifiers" in contributor:
            check.string_list(contributor["identifiers"], "identity.contributor.identifiers")
    operator = check.object(
        identity.get("operator"),
        "identity.operator",
        {"relationship", "name"},
        {"relationship", "name"},
    )
    if operator:
        relationship = operator.get("relationship")
        if relationship not in {"same_as_contributor", "named", "undisclosed"}:
            check.error("identity.operator.relationship", "has an unknown value")
        if operator.get("name") is not None:
            check.string(operator["name"], "identity.operator.name")
        if relationship == "named" and not operator.get("name"):
            check.error("identity.operator.name", "is required for a named operator")
        if relationship == "undisclosed" and operator.get("name") is not None:
            check.error("identity.operator.name", "must be null for an undisclosed operator")
        if relationship == "same_as_contributor" and contributor:
            if operator.get("name") != contributor.get("name"):
                check.error(
                    "identity.operator.name",
                    "must equal identity.contributor.name when relationship is same_as_contributor",
                )
    for field in ("model_system", "provider"):
        if field not in identity:
            continue
        disclosure = check.object(
            identity[field],
            f"identity.{field}",
            {"state"},
            {"state", "name", "version", "resources"},
        )
        if disclosure is None:
            continue
        state = disclosure.get("state")
        if state not in {"not_used", "undisclosed", "disclosed"}:
            check.error(f"identity.{field}.state", "has an unknown value")
        if state == "disclosed" and not disclosure.get("name"):
            check.error(f"identity.{field}.name", "is required when disclosed")
        if state != "disclosed" and any(key in disclosure for key in ("name", "version", "resources")):
            check.error(f"identity.{field}", "non-disclosed resources must not carry identifying detail")
    collaborators = identity.get("material_collaborators")
    if not isinstance(collaborators, list):
        check.error("identity.material_collaborators", "must be an array")
    else:
        for index, item in enumerate(collaborators):
            base = f"identity.material_collaborators[{index}]"
            collaborator = check.object(item, base, {"name", "role"}, {"name", "role"})
            if collaborator:
                check.string(collaborator.get("name"), f"{base}.name")
                check.string(collaborator.get("role"), f"{base}.role")
    return identity


def _validate_correction_lineage(value: Any, check: Validation) -> dict[str, Any] | None:
    fields = {
        "prior_return_reference",
        "affected_paths",
        "starting_commit",
        "changed_evidence_or_wording",
        "reason",
        "disposition",
    }
    lineage = check.object(value, "correction_lineage", fields, fields)
    if lineage is None:
        return None
    check.string(lineage.get("prior_return_reference"), "correction_lineage.prior_return_reference")
    paths = check.string_list(
        lineage.get("affected_paths"), "correction_lineage.affected_paths", nonempty=True
    )
    for index, path in enumerate(paths):
        _relative_path(path, f"correction_lineage.affected_paths[{index}]", check)
    if len(paths) != len(set(paths)):
        check.error("correction_lineage.affected_paths", "must not contain duplicates")
    _commit(lineage.get("starting_commit"), "correction_lineage.starting_commit", check)
    check.string(
        lineage.get("changed_evidence_or_wording"),
        "correction_lineage.changed_evidence_or_wording",
    )
    check.string(lineage.get("reason"), "correction_lineage.reason")
    disposition = check.string(lineage.get("disposition"), "correction_lineage.disposition")
    if disposition not in CORRECTION_DISPOSITIONS:
        check.error(
            "correction_lineage.disposition",
            f"must be one of {sorted(CORRECTION_DISPOSITIONS)}",
        )
    return lineage


def validate_document(
    data: Any,
    *,
    require_accepted: bool = False,
    require_submitted: bool = False,
    check_git: bool = False,
    repository_identity: dict[str, Any] | None = None,
) -> list[str]:
    check = Validation()
    try:
        identity_contract = repository_identity_contract.validate_identity(
            repository_identity
            if repository_identity is not None
            else DEFAULT_REPOSITORY_IDENTITY
        )
    except repository_identity_contract.IdentityError as exc:
        return [f"repository_identity: {exc}"]
    top_fields = {
        "schema", "record_kind", "return_id", "submitted_at", "identity",
        "repository", "frontier", "result", "evidence", "review", "attribution", "safety",
    }
    root = check.object(data, "$", top_fields, top_fields | {"correction_lineage"})
    if root is None:
        return check.errors
    record_kind = root.get("record_kind")
    if record_kind not in {"submitted_return", "accepted_receipt", "validation_fixture"}:
        check.error("record_kind", "has an unknown value")
    schema_value = check.string(root.get("schema"), "schema")
    if schema_value is not None:
        accepted_schema_values = {
            identity_contract["contracts"]["current_submission_schema"],
            *(
                row["schema_value"]
                for row in identity_contract["historical_receipt_contracts"]
            ),
        }
        if schema_value not in accepted_schema_values:
            check.error(
                "schema",
                "must identify a current or historical research-return contract",
            )
    return_id = root.get("return_id")
    if not isinstance(return_id, str) or not RETURN_ID_RE.fullmatch(return_id):
        check.error("return_id", "must match rr-[a-z0-9][a-z0-9-]{2,80}")
    _date_time(root.get("submitted_at"), "submitted_at", check)
    identity = _validate_identity(root.get("identity"), check)

    repository_fields = {"origin", "starting_commit", "proposed_commit", "accepted_commit", "changed_paths"}
    repository = check.object(root.get("repository"), "repository", repository_fields, repository_fields)
    commits: list[tuple[str, str]] = []
    changed_paths: list[str] = []
    if repository:
        origin = check.string(repository.get("origin"), "repository.origin")
        if origin and not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", origin):
            check.error("repository.origin", "must be a public GitHub repository URL without a local path")
        if origin:
            for error in repository_identity_contract.origin_contract_errors(
                record_kind,
                root.get("schema"),
                origin,
                identity_contract,
            ):
                check.error("repository.origin", error)
        for field in ("starting_commit", "proposed_commit", "accepted_commit"):
            value = repository.get(field)
            _commit(value, f"repository.{field}", check, nullable=field != "starting_commit")
            if isinstance(value, str) and COMMIT_RE.fullmatch(value):
                commits.append((field, value))
        changed_paths = check.string_list(
            repository.get("changed_paths"), "repository.changed_paths", nonempty=True
        )
        for index, item in enumerate(changed_paths):
            _relative_path(item, f"repository.changed_paths[{index}]", check)
        if len(changed_paths) != len(set(changed_paths)):
            check.error("repository.changed_paths", "must not contain duplicates")

    frontier_fields = {"problem", "handle", "bounded_question", "stop_condition", "starting_paths"}
    frontier = check.object(root.get("frontier"), "frontier", frontier_fields, frontier_fields)
    if frontier:
        if frontier.get("problem") not in PROBLEMS:
            check.error("frontier.problem", f"must be one of {sorted(PROBLEMS)}")
        for field in ("handle", "bounded_question", "stop_condition"):
            check.string(frontier.get(field), f"frontier.{field}")
        paths = check.string_list(frontier.get("starting_paths"), "frontier.starting_paths", nonempty=True)
        for index, item in enumerate(paths):
            _relative_path(item, f"frontier.starting_paths[{index}]", check)

    result_fields = {"class", "summary", "claim_ceiling", "surviving_boundary", "limitations", "requested_disposition"}
    result = check.object(root.get("result"), "result", result_fields, result_fields)
    if result:
        result_class = result.get("class")
        ceiling = result.get("claim_ceiling")
        if result_class not in RESULT_CLASSES:
            check.error("result.class", "has an unknown value")
        if ceiling not in CLAIM_CEILINGS:
            check.error("result.claim_ceiling", "has an unknown value")
        summary = check.string(result.get("summary"), "result.summary")
        if summary and OVERCLAIM_RE.search(summary):
            check.error("result.summary", "claims resolution of an open problem")
        check.string(result.get("surviving_boundary"), "result.surviving_boundary")
        check.string_list(result.get("limitations"), "result.limitations", nonempty=True)
        if result.get("requested_disposition") not in DISPOSITIONS:
            check.error("result.requested_disposition", "has an unknown value")
        if record_kind != "validation_fixture" and ceiling == "validation_fixture_only":
            check.error(
                "result.claim_ceiling",
                "validation_fixture_only is reserved for validation fixtures",
            )
        if record_kind != "validation_fixture" and result.get("requested_disposition") == "not_requested":
            check.error(
                "result.requested_disposition",
                "not_requested is reserved for validation fixtures",
            )
        negative_ceilings = {"negative_for_bounded_route"}
        if record_kind == "validation_fixture":
            negative_ceilings.add("validation_fixture_only")
        expected = {
            "negative": negative_ceilings,
            "inconclusive": {"inconclusive_attempt", "open"},
            "corrective": {"documentation_correction"},
        }
        if result_class in expected and ceiling not in expected[result_class]:
            check.error("result.claim_ceiling", f"is inconsistent with result class {result_class}")

    correction_lineage: dict[str, Any] | None = None
    if result and result.get("class") == "corrective":
        if "correction_lineage" not in root:
            check.error("correction_lineage", "is required for corrective returns")
        else:
            correction_lineage = _validate_correction_lineage(root.get("correction_lineage"), check)
    elif "correction_lineage" in root:
        check.error(
            "correction_lineage",
            "is only valid for corrective returns",
        )

    if correction_lineage:
        if repository and correction_lineage.get("starting_commit") != repository.get("starting_commit"):
            check.error(
                "correction_lineage.starting_commit",
                "must equal repository.starting_commit",
            )
        if correction_lineage.get("prior_return_reference") == return_id:
            check.error(
                "correction_lineage.prior_return_reference",
                "must identify a prior return rather than this return_id",
            )
        requests_review = correction_lineage.get("disposition") == "request_review"
        routed_for_review = result.get("requested_disposition") == "review_correction"
        if requests_review and not routed_for_review:
            check.error(
                "result.requested_disposition",
                "must be review_correction when correction_lineage requests review",
            )
        if routed_for_review and not requests_review:
            check.error(
                "correction_lineage.disposition",
                "must be request_review when result requests correction review",
            )
    elif result and result.get("requested_disposition") == "review_correction":
        check.error(
            "result.requested_disposition",
            "review_correction is only valid for a corrective result",
        )

    evidence = root.get("evidence")
    evidence_artifacts: list[str] = []
    passed_evidence = 0
    if not isinstance(evidence, list) or not evidence:
        check.error("evidence", "must be a non-empty array")
    else:
        evidence_fields = {"command", "exit_state", "exit_code", "observed", "environment", "artifacts", "replay_state"}
        for index, item in enumerate(evidence):
            base = f"evidence[{index}]"
            row = check.object(item, base, evidence_fields, evidence_fields)
            if not row:
                continue
            command = check.string(row.get("command"), f"{base}.command")
            for field in ("observed", "environment"):
                check.string(row.get(field), f"{base}.{field}")
            if command is not None and isinstance(frontier, dict):
                selected_problem = frontier.get("problem")
                if isinstance(selected_problem, int) and selected_problem in PROBLEMS:
                    for match in PROBLEM_SELECTOR_RE.finditer(command):
                        recorded_problem = int(match.group(1))
                        if recorded_problem != selected_problem:
                            check.error(
                                f"{base}.command",
                                f"problem selector must match frontier.problem {selected_problem}; "
                                f"found {recorded_problem}",
                            )
            state = row.get("exit_state")
            code = row.get("exit_code")
            if state not in {"passed", "failed", "not_run"}:
                check.error(f"{base}.exit_state", "has an unknown value")
            elif state == "passed":
                passed_evidence += 1
                if code != 0:
                    check.error(f"{base}.exit_code", "passed evidence must have exit code 0")
            elif state == "failed" and (not isinstance(code, int) or isinstance(code, bool) or code == 0):
                check.error(f"{base}.exit_code", "failed evidence must have a non-zero integer exit code")
            elif state == "not_run" and code is not None:
                check.error(f"{base}.exit_code", "not-run evidence must have a null exit code")
            if row.get("replay_state") not in {"reproduced", "not_reproduced", "not_applicable", "pending"}:
                check.error(f"{base}.replay_state", "has an unknown value")
            paths = check.string_list(row.get("artifacts"), f"{base}.artifacts")
            evidence_artifacts.extend(paths)
            for path_index, artifact in enumerate(paths):
                _relative_path(artifact, f"{base}.artifacts[{path_index}]", check)
            if len(paths) != len(set(paths)):
                check.error(f"{base}.artifacts", "must not contain duplicates")
    if result and result.get("class") in {"checked_positive", "negative", "corrective"} and not passed_evidence:
        check.error("evidence", "this result class requires at least one truthfully passed evidence command")
    foreign_evidence = sorted(set(evidence_artifacts) - set(changed_paths))
    missing_evidence = sorted(set(changed_paths) - set(evidence_artifacts))
    if foreign_evidence:
        check.error(
            "evidence.artifacts",
            f"must not cite paths outside repository.changed_paths: {foreign_evidence}",
        )
    if missing_evidence:
        check.error(
            "evidence.artifacts",
            f"must cover every repository.changed_paths artifact: {missing_evidence}",
        )

    review = check.object(root.get("review"), "review", set(REVIEW_STATES), set(REVIEW_STATES))
    decisions: dict[str, dict[str, Any]] = {}
    if review:
        for name in REVIEW_STATES:
            decision = _decision(review.get(name), name, check)
            if decision:
                decisions[name] = decision
        for name in ("problem_owned_proposition", "core_promotion", "tagged_release_inclusion"):
            decision = decisions.get(name, {})
            if decision.get("state") in {"accepted", "included"} and not decision.get("authority_ref"):
                check.error(f"review.{name}.authority_ref", "accepted promotion requires its external authority reference")

    attribution_fields = {"artifact_credit", "requested_display", "existing_corpus_authorship_preserved"}
    attribution = check.object(root.get("attribution"), "attribution", attribution_fields, attribution_fields)
    if attribution:
        credits = attribution.get("artifact_credit")
        credited_paths: list[str] = []
        credit_names: list[str] = []
        if not isinstance(credits, list) or not credits:
            check.error("attribution.artifact_credit", "must be a non-empty array")
        else:
            for index, item in enumerate(credits):
                base = f"attribution.artifact_credit[{index}]"
                credit = check.object(item, base, {"name", "artifact_paths"}, {"name", "artifact_paths"})
                if credit:
                    name = check.string(credit.get("name"), f"{base}.name")
                    if name is not None:
                        credit_names.append(name)
                    paths = check.string_list(credit.get("artifact_paths"), f"{base}.artifact_paths", nonempty=True)
                    credited_paths.extend(paths)
                    for path_index, artifact in enumerate(paths):
                        _relative_path(artifact, f"{base}.artifact_paths[{path_index}]", check)
                    if len(paths) != len(set(paths)):
                        check.error(f"{base}.artifact_paths", "must not contain duplicates")
            missing_credit = sorted(set(changed_paths) - set(credited_paths))
            foreign_credit = sorted(set(credited_paths) - set(changed_paths))
            if missing_credit:
                check.error(
                    "attribution.artifact_credit",
                    f"must credit every repository.changed_paths artifact; missing {missing_credit}",
                )
            if foreign_credit:
                check.error(
                    "attribution.artifact_credit",
                    f"must not credit paths outside repository.changed_paths; unexpected {foreign_credit}",
                )
            contributor_value = identity.get("contributor") if identity else None
            contributor_name = (
                contributor_value.get("name") if isinstance(contributor_value, dict) else None
            )
            if isinstance(contributor_name, str) and contributor_name not in credit_names:
                check.error(
                    "attribution.artifact_credit",
                    "must include identity.contributor.name in artifact credit",
                )
        check.string(attribution.get("requested_display"), "attribution.requested_display")
        if attribution.get("existing_corpus_authorship_preserved") is not True:
            check.error("attribution.existing_corpus_authorship_preserved", "must be true")

    safety_fields = {"private_material_removed", "credentials_removed", "evidence_truthfully_reported", "no_claim_overreach"}
    safety = check.object(root.get("safety"), "safety", safety_fields, safety_fields)
    if safety:
        for field in safety_fields:
            if safety.get(field) is not True:
                check.error(f"safety.{field}", "must be true")

    for safety_error in public_safety_errors(root):
        check.error("$", safety_error)

    if require_accepted and record_kind != "accepted_receipt":
        check.error("record_kind", "--require-accepted requires accepted_receipt")
    if require_submitted and record_kind != "submitted_return":
        check.error("record_kind", "--require-submitted requires submitted_return")
    if require_accepted and require_submitted:
        check.error("record_kind", "accepted and submitted modes are mutually exclusive")
    if record_kind == "accepted_receipt":
        if repository and repository.get("accepted_commit") is None:
            check.error("repository.accepted_commit", "accepted receipts require an accepted commit")
        if repository and repository.get("proposed_commit") is None:
            check.error("repository.proposed_commit", "accepted receipts require a proposed commit")
        required_states = {
            "structural_validation": "valid",
            "reproduction": "reproduced",
            "accepted_handoff": "accepted",
        }
        for name, expected_state in required_states.items():
            if decisions.get(name, {}).get("state") != expected_state:
                check.error(f"review.{name}.state", f"accepted receipts require {expected_state}")
        if not decisions.get("accepted_handoff", {}).get("authority_ref"):
            check.error(
                "review.accepted_handoff.authority_ref",
                "accepted receipts require an explicit acceptance authority reference",
            )

        submitted_at = root.get("submitted_at")
        accepted_decided_at = decisions.get("accepted_handoff", {}).get("decided_at")
        if isinstance(submitted_at, str) and isinstance(accepted_decided_at, str):
            try:
                submitted_time = dt.datetime.fromisoformat(
                    submitted_at.replace("Z", "+00:00")
                )
                accepted_time = dt.datetime.fromisoformat(
                    accepted_decided_at.replace("Z", "+00:00")
                )
            except ValueError:
                # _date_time already reports malformed timestamps; this guard
                # only adds the ordering rule when both values are parseable.
                pass
            else:
                if (
                    submitted_time.utcoffset() is not None
                    and accepted_time.utcoffset() is not None
                    and accepted_time < submitted_time
                ):
                    check.error(
                        "review.accepted_handoff.decided_at",
                        "must not precede submitted_at",
                    )

        requested_disposition = result.get("requested_disposition") if result else None
        problem_state = decisions.get("problem_owned_proposition", {}).get("state")
        core_state = decisions.get("core_promotion", {}).get("state")
        problem_dispositions = {"consider_problem_proposition", "consider_core_promotion"}

        if problem_state != "not_requested" and requested_disposition not in problem_dispositions:
            check.error(
                "review.problem_owned_proposition.state",
                "requires a matching problem-proposition or core-promotion disposition",
            )
        if requested_disposition in problem_dispositions and problem_state == "not_requested":
            check.error(
                "review.problem_owned_proposition.state",
                "the requested disposition requires a recorded promotion decision",
            )
        if core_state != "not_requested" and requested_disposition != "consider_core_promotion":
            check.error(
                "review.core_promotion.state",
                "requires a matching core-promotion disposition",
            )
        if requested_disposition == "consider_core_promotion" and core_state == "not_requested":
            check.error(
                "review.core_promotion.state",
                "the requested disposition requires a recorded promotion decision",
            )

        if problem_state == "accepted":
            for name in ("mathematical_review", "claim_boundary_review"):
                if decisions.get(name, {}).get("state") != "approved":
                    check.error(
                        f"review.{name}.state",
                        "problem-owned proposition acceptance requires approved review",
                    )
        if core_state in {"pending", "accepted"} and problem_state != "accepted":
            check.error(
                "review.core_promotion.state",
                "core promotion requires an accepted problem-owned proposition",
            )
        if requested_disposition == "consider_core_promotion":
            for name in ("mathematical_review", "claim_boundary_review"):
                if decisions.get(name, {}).get("state") != "approved":
                    check.error(f"review.{name}.state", "core-promotion requests require approved review")
        check_git = True
    elif repository and repository.get("accepted_commit") is not None:
        check.error("repository.accepted_commit", "only accepted_receipt records may name an accepted commit")
    if record_kind != "accepted_receipt" and decisions.get("accepted_handoff", {}).get("state") == "accepted":
        check.error("review.accepted_handoff.state", "only accepted_receipt records may assert acceptance")

    if check_git:
        present_commits: set[str] = set()
        for field, commit in commits:
            if not _git_commit_exists(commit):
                check.error(f"repository.{field}", "commit is not present in this checkout")
            else:
                present_commits.add(commit)

        accepted_commit = repository.get("accepted_commit") if repository else None
        if (
            record_kind == "accepted_receipt"
            and isinstance(accepted_commit, str)
            and accepted_commit in present_commits
            and not _git_is_ancestor(accepted_commit, "HEAD")
        ):
            check.error(
                "repository.accepted_commit",
                "must be contained in the current checkout HEAD",
            )

        if repository:
            starting_commit = repository.get("starting_commit")
            if isinstance(starting_commit, str) and starting_commit in present_commits:
                for field in ("proposed_commit", "accepted_commit"):
                    ending_commit = repository.get(field)
                    if not isinstance(ending_commit, str) or ending_commit not in present_commits:
                        continue
                    if not _git_is_ancestor(starting_commit, ending_commit):
                        check.error(
                            f"repository.{field}",
                            "must descend from repository.starting_commit",
                        )
                        continue
                    git_paths = _git_changed_paths(starting_commit, ending_commit)
                    if git_paths is None:
                        check.error(
                            f"repository.{field}",
                            "could not inspect changed paths in this checkout",
                        )
                        continue
                    absent_paths = sorted(set(changed_paths) - git_paths)
                    if absent_paths:
                        check.error(
                            "repository.changed_paths",
                            f"paths are absent from the starting-to-{field} Git diff: {absent_paths}",
                        )
                proposed_commit = repository.get("proposed_commit")
                accepted_commit = repository.get("accepted_commit")
                if (
                    isinstance(proposed_commit, str)
                    and proposed_commit in present_commits
                    and isinstance(accepted_commit, str)
                    and accepted_commit in present_commits
                    and not _git_is_ancestor(proposed_commit, accepted_commit)
                ):
                    check.error(
                        "repository.accepted_commit",
                        "must descend from repository.proposed_commit",
                    )
        for artifact in sorted(set(evidence_artifacts)):
            if present_commits and not any(
                _git_path_exists(commit, artifact) for commit in present_commits
            ):
                check.error(
                    "evidence.artifacts",
                    f"{artifact!r} is absent from every recorded commit",
                )

    return sorted(set(check.errors))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON return or receipt to validate")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--require-accepted",
        action="store_true",
        help="require an accepted receipt and verify its commits in local Git history",
    )
    mode.add_argument(
        "--require-submitted",
        action="store_true",
        help="require a submitted return rather than a fixture or accepted receipt",
    )
    parser.add_argument(
        "--check-git",
        action="store_true",
        help="verify every recorded commit against local Git history",
    )
    parser.add_argument(
        "--repository-identity",
        type=Path,
        default=IDENTITY_PATH,
        help="current public repository identity authority (simulation may supply an isolated file)",
    )
    parser.add_argument(
        "--route-memory-receipt",
        type=Path,
        help="validate a digest-bound route-memory relationship sidecar from a continuation package",
    )
    parser.add_argument(
        "--require-route-memory-receipt",
        action="store_true",
        help="require a digest-bound route-memory relationship sidecar (for GitHub intake)",
    )
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    unsafe_inputs = []
    if path_has_symlink_component(args.input):
        unsafe_inputs.append("input path must not traverse symbolic links")
    if args.route_memory_receipt is not None and path_has_symlink_component(
        args.route_memory_receipt
    ):
        unsafe_inputs.append(
            "route_memory_receipt path must not traverse symbolic links"
        )
    if unsafe_inputs:
        print(
            json.dumps(
                {
                    "schema": "research-return-validation/1",
                    "valid": False,
                    "path_policy": PATH_POLICY,
                    "route_memory_binding": None,
                    "errors": unsafe_inputs,
                },
                sort_keys=True,
            )
        )
        return 2
    try:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        identity_contract = repository_identity_contract.load_identity(
            args.repository_identity
        )
    except (
        OSError,
        UnicodeError,
        json.JSONDecodeError,
        repository_identity_contract.IdentityError,
    ) as exc:
        print(
            json.dumps(
                {
                    "schema": "research-return-validation/1",
                    "valid": False,
                    "path_policy": PATH_POLICY,
                    "route_memory_binding": None,
                    "errors": [str(exc)],
                }
            )
        )
        return 2
    errors = validate_document(
        data,
        require_accepted=args.require_accepted,
        require_submitted=args.require_submitted,
        check_git=args.check_git,
        repository_identity=identity_contract,
    )
    route_memory_receipt_path = args.route_memory_receipt
    route_memory_data: dict[str, Any] | None = None
    route_memory_errors: list[str] = []
    if args.require_route_memory_receipt and route_memory_receipt_path is None:
        route_memory_errors.append(
            "route_memory_receipt: required for submitted return intake"
        )
    if route_memory_receipt_path is not None:
        try:
            loaded_route_memory = json.loads(
                route_memory_receipt_path.read_text(encoding="utf-8")
            )
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            route_memory_errors.append(f"route_memory_receipt: cannot read JSON: {exc}")
        else:
            if not isinstance(loaded_route_memory, dict):
                route_memory_errors.append("route_memory_receipt: must be a JSON object")
            elif not isinstance(data, dict):
                route_memory_errors.append("route_memory_receipt: return input must be an object")
            else:
                route_memory_data = loaded_route_memory
                route_memory_errors.extend(
                    route_memory_receipt.validate_detached_return_receipt(
                        loaded_route_memory, data, ROOT
                    )
                )
    errors.extend(route_memory_errors)
    contract_path = ROOT / identity_contract["contracts"]["current_schema_path"]
    receipt = {
        "schema": "research-return-validation/1",
        "input": portable_path_reference(args.input),
        "contract": (
            str(contract_path.relative_to(ROOT))
            if contract_path.is_relative_to(ROOT)
            else str(contract_path)
        ),
        "path_policy": PATH_POLICY,
        "repository_identity": portable_path_reference(args.repository_identity),
        "route_memory_receipt": portable_path_reference(route_memory_receipt_path),
        "route_memory_receipt_required": args.require_route_memory_receipt,
        "route_memory_binding": (
            route_memory_binding_summary(route_memory_data)
            if route_memory_data is not None and not route_memory_errors
            else None
        ),
        "return_id": data.get("return_id") if isinstance(data, dict) else None,
        "valid": not errors,
        "accepted": bool(
            isinstance(data, dict)
            and data.get("record_kind") == "accepted_receipt"
            and not errors
        ),
        "submitted": bool(
            isinstance(data, dict)
            and data.get("record_kind") == "submitted_return"
            and not errors
        ),
        "errors": errors,
    }
    if args.format == "json":
        print(json.dumps(receipt, indent=2, sort_keys=True))
    elif errors:
        for error in errors:
            print(f"FAIL {error}")
    else:
        print(f"PASS {receipt['return_id']}")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
