#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run the deterministic reconstruction of the publication mutation study.

The historical paper does not retain every original byte target.  This harness
therefore runs the explicit operators in experiments/publication_mutations.json
as a new experiment at the same checkpoint.  It never rewrites the historical
receipt or claims that reconstructed timings are the original timings.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MANIFEST = ROOT / "experiments" / "publication_mutations.json"
MANIFEST_SCHEMA = "erdos249257-publication-mutation-operators/1"
RUN_SCHEMA = "erdos249257-publication-mutation-run/1"
VERIFY_SCHEMA = "erdos249257-publication-mutation-operator-verification/1"
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
SUBPROCESS_TIMEOUT_SECONDS = singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS


class MutationError(RuntimeError):
    """Raised when a declared mutation does not apply uniquely."""


def sha256(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def find_by_id(rows: list[dict[str, Any]], row_id: str, label: str) -> dict[str, Any]:
    matches = [row for row in rows if row.get("id") == row_id]
    if len(matches) != 1:
        raise MutationError(
            f"{label} selector {row_id!r} matched {len(matches)} rows"
        )
    return matches[0]


def nested_parent(data: dict[str, Any], field_path: list[str]) -> tuple[dict[str, Any], str]:
    if not field_path:
        raise MutationError("field_path must not be empty")
    node: Any = data
    for key in field_path[:-1]:
        if not isinstance(node, dict) or key not in node:
            raise MutationError(f"field_path does not resolve at {key!r}")
        node = node[key]
    if not isinstance(node, dict):
        raise MutationError("field_path parent is not an object")
    return node, field_path[-1]


def replace_text(path: Path, operation: dict[str, Any]) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    old = operation["old"]
    expected = operation.get("expected_occurrences", 1)
    occurrences = text.count(old)
    if occurrences != expected:
        raise MutationError(
            f"{path}: expected {expected} occurrences of {old!r}, found {occurrences}"
        )
    path.write_text(text.replace(old, operation["new"], expected), encoding="utf-8")
    return {"replaced_occurrences": expected}


def set_claim_status(path: Path, operation: dict[str, Any]) -> dict[str, Any]:
    data = load_json(path)
    claim = find_by_id(data["claims"], operation["claim_id"], "claim")
    if claim.get("status") != operation["from"]:
        raise MutationError(
            f"claim {operation['claim_id']} status is {claim.get('status')!r}, "
            f"expected {operation['from']!r}"
        )
    claim["status"] = operation["to"]
    write_json(path, data)
    return {
        "claim_id": operation["claim_id"],
        "from": operation["from"],
        "to": operation["to"],
    }


def increment_claim_declaration_line(
    path: Path,
    operation: dict[str, Any],
) -> dict[str, Any]:
    data = load_json(path)
    claim = find_by_id(data["claims"], operation["claim_id"], "claim")
    declarations = [
        row
        for row in claim.get("declarations", [])
        if row.get("name") == operation["declaration_name"]
    ]
    if len(declarations) != 1:
        raise MutationError(
            f"declaration selector {operation['declaration_name']!r} matched "
            f"{len(declarations)} rows"
        )
    row = declarations[0]
    before = row.get("line")
    if not isinstance(before, int):
        raise MutationError("selected declaration line is not an integer")
    row["line"] = before + operation["delta"]
    write_json(path, data)
    return {
        "claim_id": operation["claim_id"],
        "declaration_name": operation["declaration_name"],
        "from_line": before,
        "to_line": row["line"],
    }


def increment_tex_anchor_line(path: Path, operation: dict[str, Any]) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    old = (
        f"\\{operation['macro']}{{{operation['source']}}}"
        f"{{{operation['line']}}}{{{operation['declaration']}}}"
    )
    new_line = operation["line"] + operation["delta"]
    new = (
        f"\\{operation['macro']}{{{operation['source']}}}"
        f"{{{new_line}}}{{{operation['declaration']}}}"
    )
    expected = operation.get("expected_occurrences", 1)
    occurrence_index = operation.get("occurrence_index", 0)
    if text.count(old) != expected:
        raise MutationError(
            f"{path}: TeX anchor selector matched {text.count(old)} occurrences, "
            f"expected {expected}"
        )
    positions = [match.start() for match in re.finditer(re.escape(old), text)]
    if not 0 <= occurrence_index < len(positions):
        raise MutationError(
            f"{path}: occurrence_index {occurrence_index} is outside "
            f"0..{len(positions) - 1}"
        )
    start = positions[occurrence_index]
    mutated = text[:start] + new + text[start + len(old) :]
    path.write_text(mutated, encoding="utf-8")
    return {
        "from_anchor": old,
        "to_anchor": new,
        "selected_occurrence_index": occurrence_index,
        "matched_occurrences": expected,
    }


def duplicate_claim_across_families(
    path: Path,
    operation: dict[str, Any],
) -> dict[str, Any]:
    data = load_json(path)
    families = data["machine_readable_paper"]["publication_assembly"][
        "contribution_families"
    ]
    source = find_by_id(families, operation["source_family_id"], "source family")
    target = find_by_id(families, operation["target_family_id"], "target family")
    claim_id = operation["claim_id"]
    if claim_id not in source["claim_ids"]:
        raise MutationError(f"{claim_id!r} is absent from the declared source family")
    if claim_id in target["claim_ids"]:
        raise MutationError(f"{claim_id!r} is already present in the target family")
    target["claim_ids"].append(claim_id)
    write_json(path, data)
    return {
        "claim_id": claim_id,
        "source_family_id": source["id"],
        "target_family_id": target["id"],
    }


def increment_json_integer(path: Path, operation: dict[str, Any]) -> dict[str, Any]:
    data = load_json(path)
    parent, field = nested_parent(data, operation["field_path"])
    before = parent.get(field)
    if not isinstance(before, int):
        raise MutationError(f"selected JSON field {field!r} is not an integer")
    parent[field] = before + operation["delta"]
    write_json(path, data)
    return {"field_path": operation["field_path"], "from": before, "to": parent[field]}


def append_text(path: Path, operation: dict[str, Any]) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    absent = operation.get("must_be_absent")
    if absent and absent in text:
        raise MutationError(f"{path}: required-absent token already exists: {absent!r}")
    appended = operation["text"]
    path.write_text(text + appended, encoding="utf-8")
    return {"appended_bytes": len(appended.encode("utf-8"))}


def set_open_anchor_title(path: Path, operation: dict[str, Any]) -> dict[str, Any]:
    data = load_json(path)
    proposition = find_by_id(
        data["remaining_open_propositions"],
        operation["open_proposition_id"],
        "remaining-open proposition",
    )
    anchor = proposition.get("paper_anchor")
    if not isinstance(anchor, dict) or anchor.get("title") != operation["from"]:
        raise MutationError(
            f"open anchor title is {anchor.get('title') if isinstance(anchor, dict) else None!r}, "
            f"expected {operation['from']!r}"
        )
    anchor["title"] = operation["to"]
    write_json(path, data)
    return {
        "open_proposition_id": operation["open_proposition_id"],
        "from": operation["from"],
        "to": operation["to"],
    }


def pad_file_to_bytes(path: Path, operation: dict[str, Any]) -> dict[str, Any]:
    data = path.read_bytes()
    target = operation["target_size_bytes"]
    pad = operation["pad_byte"].encode("utf-8")
    if len(pad) != 1:
        raise MutationError("pad_byte must encode to exactly one byte")
    if len(data) >= target:
        raise MutationError(
            f"{path}: current size {len(data)} is not below target {target}"
        )
    path.write_bytes(data + pad * (target - len(data)))
    return {"from_size_bytes": len(data), "to_size_bytes": target}


OPERATORS = {
    "replace_text": replace_text,
    "set_claim_status": set_claim_status,
    "increment_claim_declaration_line": increment_claim_declaration_line,
    "increment_tex_anchor_line": increment_tex_anchor_line,
    "duplicate_claim_across_families": duplicate_claim_across_families,
    "increment_json_integer": increment_json_integer,
    "append_text": append_text,
    "set_open_anchor_title": set_open_anchor_title,
    "pad_file_to_bytes": pad_file_to_bytes,
}


def apply_operator(repo: Path, row: dict[str, Any]) -> dict[str, Any]:
    operation = row["operation"]
    kind = operation["kind"]
    handler = OPERATORS.get(kind)
    if handler is None:
        raise MutationError(f"unknown mutation operator kind: {kind}")
    relative = operation["path"]
    path = repo / relative
    if not path.is_file():
        raise MutationError(f"mutation target is missing: {relative}")
    before = sha256(path)
    detail = handler(path, operation)
    after = sha256(path)
    if before == after:
        raise MutationError(f"mutation {row['id']} did not change {relative}")
    return {
        "path": relative,
        "before_digest": before,
        "after_digest": after,
        "detail": detail,
    }


def run_checked(argv: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    for attempt in range(1, singleflight.MAX_EXTERNAL_TERMINATION_ATTEMPTS + 1):
        completed = subprocess.run(
            argv,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
            env=singleflight.command_environment(),
            timeout=SUBPROCESS_TIMEOUT_SECONDS,
        )
        if completed.returncode == 0:
            return completed
        if (
            singleflight.is_external_termination_exit(completed.returncode)
            and attempt < singleflight.MAX_EXTERNAL_TERMINATION_ATTEMPTS
        ):
            continue
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise MutationError(
            f"{' '.join(argv)} failed with exit {completed.returncode}: {detail}"
        )
    raise MutationError(f"{' '.join(argv)} exhausted external-termination recovery")


def clone_at_checkpoint(checkpoint: str, parent: Path) -> Path:
    clone = parent / "repo"
    run_checked(
        [
            "git",
            "clone",
            "--shared",
            "--no-checkout",
            "--quiet",
            str(ROOT),
            str(clone),
        ],
        ROOT,
    )
    run_checked(
        ["git", "checkout", "--detach", "--force", "--quiet", checkpoint],
        clone,
    )
    return clone


def resolve_commit(ref: str) -> str:
    completed = run_checked(
        ["git", "rev-parse", "--verify", f"{ref}^{{commit}}"],
        ROOT,
    )
    commit = completed.stdout.strip()
    if re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        raise MutationError(f"base ref did not resolve to a full commit id: {ref}")
    return commit


def reset_clone(clone: Path, checkpoint: str) -> None:
    run_checked(["git", "reset", "--hard", "--quiet", checkpoint], clone)
    run_checked(["git", "clean", "-fdq"], clone)


def changed_paths(clone: Path) -> list[str]:
    completed = run_checked(["git", "status", "--short", "--untracked-files=all"], clone)
    return sorted(line[3:] for line in completed.stdout.splitlines() if line)


def load_manifest(path: Path) -> dict[str, Any]:
    manifest = load_json(path)
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise MutationError(f"manifest must use schema {MANIFEST_SCHEMA}")
    ids = [row.get("id") for row in manifest.get("operators", [])]
    if ids != [f"M{i}" for i in range(1, 11)]:
        raise MutationError("manifest must contain M1 through M10 in order")
    if manifest.get("experiment_kind") != (
        "deterministic_reconstruction_not_exact_historical_replay"
    ):
        raise MutationError("manifest lost its reconstruction boundary")
    return manifest


def verify_operators(
    manifest: dict[str, Any],
    base_ref: str,
    base_commit: str,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="publication-mutation-verify-") as temp:
        clone = clone_at_checkpoint(base_commit, Path(temp))
        rows = []
        for operator in manifest["operators"]:
            reset_clone(clone, base_commit)
            applied = apply_operator(clone, operator)
            changed = changed_paths(clone)
            expected_paths = [operator["operation"]["path"]]
            if changed != expected_paths:
                raise MutationError(
                    f"{operator['id']} changed {changed}, expected {expected_paths}"
                )
            rows.append(
                {
                    "id": operator["id"],
                    "operator_kind": operator["operation"]["kind"],
                    "exact_original_target_registered": operator[
                        "exact_original_target_registered"
                    ],
                    "changed_paths": changed,
                    "application": applied,
                    "status": "applied_uniquely",
                }
            )
    return {
        "schema": VERIFY_SCHEMA,
        "suite_id": manifest["suite_id"],
        "experiment_kind": manifest["experiment_kind"],
        "manifest_checkpoint": manifest["checkpoint"],
        "base_ref": base_ref,
        "base_commit": base_commit,
        "base_role": (
            "historical_evaluation_checkpoint"
            if base_commit == manifest["checkpoint"]
            else "selected_later_commit"
        ),
        "verified_operator_count": len(rows),
        "operators": rows,
        "status": "all_operators_apply_uniquely",
    }


def bounded_tail(text: str, limit: int = 4000) -> str:
    return text[-limit:]


def parse_check_count(output: str) -> int | None:
    matches = re.findall(
        r"(?:across|all) ([0-9,]+) checks(?: passed)?",
        output,
    )
    return int(matches[-1].replace(",", "")) if matches else None


def first_failure(output: str) -> str | None:
    return next(
        (line.strip() for line in output.splitlines() if "FAIL" in line),
        None,
    )


def run_gate_command(
    command: list[str],
    clone: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    """Run one gate and retain enough evidence to validate the run itself."""
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            cwd=clone,
            capture_output=True,
            text=True,
            check=False,
            env=singleflight.command_environment(),
            timeout=timeout_seconds,
        )
        elapsed = round(time.monotonic() - started, 3)
        combined = completed.stdout + "\n" + completed.stderr
        return {
            "status": "passed" if completed.returncode == 0 else "failed",
            "gate_returncode": completed.returncode,
            "wall_time_seconds": elapsed,
            "reported_check_count": parse_check_count(combined),
            "first_failure": first_failure(combined),
            "stdout_tail": bounded_tail(completed.stdout),
            "stderr_tail": bounded_tail(completed.stderr),
        }
    except subprocess.TimeoutExpired as error:
        elapsed = round(time.monotonic() - started, 3)
        stdout = error.stdout or ""
        stderr = error.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="replace")
        return {
            "status": "timeout",
            "gate_returncode": None,
            "wall_time_seconds": elapsed,
            "reported_check_count": None,
            "first_failure": None,
            "stdout_tail": bounded_tail(stdout),
            "stderr_tail": bounded_tail(stderr),
        }


def run_mutations(
    manifest: dict[str, Any],
    selected_ids: list[str],
    timeout_seconds: int,
    base_ref: str,
    base_commit: str,
) -> dict[str, Any]:
    by_id = {row["id"]: row for row in manifest["operators"]}
    unknown = [mutation_id for mutation_id in selected_ids if mutation_id not in by_id]
    if unknown:
        raise MutationError(f"unknown mutation ids: {', '.join(unknown)}")
    started_at = datetime.now(timezone.utc).isoformat()
    historical_comparison_applicable = base_commit == manifest["checkpoint"]
    base_role = (
        "historical_evaluation_checkpoint"
        if historical_comparison_applicable
        else "selected_later_commit"
    )
    results = []
    with tempfile.TemporaryDirectory(prefix="publication-mutation-run-") as temp:
        clone = clone_at_checkpoint(base_commit, Path(temp))
        reset_clone(clone, base_commit)
        baseline = run_gate_command(
            manifest["default_gate_command"],
            clone,
            timeout_seconds,
        )
        if baseline["status"] != "passed":
            return {
                "schema": RUN_SCHEMA,
                "suite_id": manifest["suite_id"],
                "experiment_kind": manifest["experiment_kind"],
                "manifest_checkpoint": manifest["checkpoint"],
                "base_ref": base_ref,
                "base_commit": base_commit,
                "base_role": base_role,
                "historical_evidence": manifest["historical_evidence"],
                "started_at": started_at,
                "completed_at": datetime.now(timezone.utc).isoformat(),
                "status": "invalid_baseline",
                "baseline": baseline,
                "mutation_ids": selected_ids,
                "results": [],
                "summary": {
                    "baseline_valid": False,
                    "run_count": 0,
                    "rejected_count": 0,
                    "escaped_count": 0,
                    "timeout_count": 0,
                    "historical_comparison_applicable": (
                        historical_comparison_applicable
                    ),
                    "historical_outcome_class_match_count": None,
                },
                "claim_ceiling": (
                    "No mutation outcome is counted because the unmutated "
                    "selected base did not pass the configured gate."
                ),
            }
        for mutation_id in selected_ids:
            reset_clone(clone, base_commit)
            operator = by_id[mutation_id]
            applied = apply_operator(clone, operator)
            changed = changed_paths(clone)
            gate = run_gate_command(
                manifest["default_gate_command"],
                clone,
                timeout_seconds,
            )
            outcome = {
                "passed": "escaped",
                "failed": "rejected",
                "timeout": "timeout",
            }[gate["status"]]
            result = {
                "id": mutation_id,
                "outcome": outcome,
                **{key: value for key, value in gate.items() if key != "status"},
            }
            result.update(
                {
                    "expected_historical_outcome": operator[
                        "expected_historical_outcome"
                    ],
                    "matches_historical_outcome_class": (
                        result["outcome"] == operator["expected_historical_outcome"]
                        if historical_comparison_applicable
                        else None
                    ),
                    "exact_original_target_registered": operator[
                        "exact_original_target_registered"
                    ],
                    "changed_paths": changed,
                    "application": applied,
                }
            )
            results.append(result)
    return {
        "schema": RUN_SCHEMA,
        "suite_id": manifest["suite_id"],
        "experiment_kind": manifest["experiment_kind"],
        "manifest_checkpoint": manifest["checkpoint"],
        "base_ref": base_ref,
        "base_commit": base_commit,
        "base_role": base_role,
        "historical_evidence": manifest["historical_evidence"],
        "started_at": started_at,
        "completed_at": datetime.now(timezone.utc).isoformat(),
        "status": "completed",
        "baseline": baseline,
        "mutation_ids": selected_ids,
        "results": results,
        "summary": {
            "baseline_valid": True,
            "run_count": len(results),
            "rejected_count": sum(row["outcome"] == "rejected" for row in results),
            "escaped_count": sum(row["outcome"] == "escaped" for row in results),
            "timeout_count": sum(row["outcome"] == "timeout" for row in results),
            "historical_comparison_applicable": historical_comparison_applicable,
            "historical_outcome_class_match_count": (
                sum(row["matches_historical_outcome_class"] for row in results)
                if historical_comparison_applicable
                else None
            ),
        },
        "claim_ceiling": (
            "These are deterministic reconstruction results on the selected "
            "base commit, not the original historical run logs or timings. "
            "A later-commit result applies only to that exact base commit."
        ),
    }


def emit(data: dict[str, Any], receipt: Path | None) -> None:
    encoded = json.dumps(data, ensure_ascii=False, indent=2) + "\n"
    if receipt is not None:
        receipt.parent.mkdir(parents=True, exist_ok=True)
        receipt.write_text(encoded, encoding="utf-8")
    print(encoded, end="")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--base-ref",
        help=(
            "commit to mutate; defaults to the manifest evaluation checkpoint. "
            "Use HEAD only for an explicitly versioned later-commit rerun"
        ),
    )
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--list", action="store_true")
    action.add_argument("--verify-operators", action="store_true")
    action.add_argument("--all", action="store_true")
    action.add_argument("--mutation", action="append", metavar="ID")
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    try:
        manifest = load_manifest(args.manifest.resolve())
        base_ref = args.base_ref or manifest["checkpoint"]
        base_commit = resolve_commit(base_ref)
        if args.list:
            emit(
                {
                    "schema": MANIFEST_SCHEMA,
                    "suite_id": manifest["suite_id"],
                    "experiment_kind": manifest["experiment_kind"],
                    "checkpoint": manifest["checkpoint"],
                    "operators": [
                        {
                            "id": row["id"],
                            "reported_class": row["reported_class"],
                            "operator_kind": row["operation"]["kind"],
                            "target_path": row["operation"]["path"],
                            "exact_original_target_registered": row[
                                "exact_original_target_registered"
                            ],
                        }
                        for row in manifest["operators"]
                    ],
                },
                args.receipt,
            )
        elif args.verify_operators:
            emit(
                verify_operators(manifest, base_ref, base_commit),
                args.receipt,
            )
        else:
            selected = (
                [row["id"] for row in manifest["operators"]]
                if args.all
                else args.mutation
            )
            run_receipt = run_mutations(
                manifest,
                selected,
                args.timeout_seconds,
                base_ref,
                base_commit,
            )
            emit(run_receipt, args.receipt)
            if run_receipt.get("status") != "completed":
                return 3
    except (MutationError, OSError, json.JSONDecodeError) as error:
        print(f"run_publication_mutations: {error}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
