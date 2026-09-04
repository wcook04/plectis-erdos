"""Deterministic provenance contracts for formal-mathematics experiments.

This module does not judge mathematics.  It keeps a computation attached to
the hypothesis that motivated it, the observation that would falsify that
hypothesis, and the exact analytic consumer of either outcome.  Lean, exact
arithmetic, or another owner verifier remains the authority for every result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, Iterable, Mapping


SCHEMA_VERSION = "formal_math_experiment_contract_v1"
RESULT_STATUSES = frozenset(
    {
        "not_run",
        "finite_support",
        "finite_counterexample",
        "mixed",
        "exact_one_way_result",
    }
)
PROGRESS_CLASSES = frozenset(
    {
        "finite_horizon_only",
        "mechanism_eliminated",
        "mechanism_opened",
        "producer_constructed",
        "one_way_theorem",
        "inconclusive",
    }
)
DEFAULT_RECEIPT_ROOTS = (Path("state/formal_math"), Path("formal_math"))


def _nonempty(label: str, value: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label} must be a nonempty string")
    return value


def _relative_ref(label: str, value: str) -> str:
    value = _nonempty(label, value)
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"{label} must be a repository-relative path")
    return path.as_posix()


def _refs(label: str, values: Iterable[str]) -> list[str]:
    result = [_relative_ref(f"{label}[{index}]", value) for index, value in enumerate(values)]
    if not result:
        raise ValueError(f"{label} must contain at least one reference")
    if len(set(result)) != len(result):
        raise ValueError(f"{label} must not contain duplicate references")
    return result


def _declarations(label: str, values: Iterable[str]) -> list[str]:
    result = [_nonempty(f"{label}[{index}]", value) for index, value in enumerate(values)]
    if len(set(result)) != len(result):
        raise ValueError(f"{label} must not contain duplicate declarations")
    return result


def _resource_bounds(values: Mapping[str, int]) -> dict[str, int]:
    """Normalize machine-readable finite-search bounds.

    These bounds are evidence about what an exact computation was allowed to
    consume, not mathematical quantifiers.  Requiring positive integer values
    keeps receipts deterministic and prevents an unbounded search from being
    presented as a bounded probe merely through prose.
    """

    if not isinstance(values, Mapping) or not values:
        raise ValueError("resource_bounds must be a nonempty object")
    result: dict[str, int] = {}
    for key, value in values.items():
        normalized_key = _nonempty("resource_bounds key", key)
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            raise ValueError(
                f"resource_bounds[{normalized_key!r}] must be a positive integer"
            )
        result[normalized_key] = value
    return dict(sorted(result.items()))


PACKET_MECHANISM_ARRAYS = ("exact_results", "negative_results", "open_producers")


def packet_scope_digest(payload: bytes, scope_ids: Iterable[str]) -> str | None:
    """Digest of only the research-packet slice a receipt actually depends on.

    A research packet is append-mostly: every landed result deposits a new entry.
    Hashing the whole file makes each deposit mark every receipt for that problem
    stale, so an unrelated probe has to be rerun -- sometimes for hours -- to
    restore a green guard, and the signal that a receipt's *own* mechanism moved
    is lost in the noise.

    The digest here covers the problem identity, the target, and exactly those
    mechanism entries the receipt bound to.  It changes when the receipt's own
    ground moved, and not when a sibling result was appended.  Returns `None`
    when the payload is not a packet or the scope is empty, in which case the
    caller falls back to the whole-file digest.
    """
    wanted = {str(x) for x in scope_ids if str(x)}
    if not wanted:
        return None
    try:
        data = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(data, Mapping):
        return None
    entries: list[list[Any]] = []
    for field in PACKET_MECHANISM_ARRAYS:
        items = data.get(field)
        if not isinstance(items, list):
            continue
        for item in items:
            if isinstance(item, Mapping) and str(item.get("id")) in wanted:
                entries.append([field, item])
    entries.sort(key=lambda pair: (pair[0], json.dumps(pair[1], sort_keys=True)))
    scoped = {
        "problem_id": data.get("problem_id"),
        "target": data.get("target"),
        "scope_ids": sorted(wanted),
        "entries": entries,
    }
    canonical = json.dumps(scoped, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def source_record(
    repo_root: Path, ref: str, *, scope_ids: Iterable[str] = ()
) -> dict[str, Any]:
    """Return a stable content record for one repository-relative source.

    When `scope_ids` is supplied and `ref` is a research packet, the record also
    carries a scoped digest over just those mechanism entries, so that appending
    an unrelated result to the packet does not mark this receipt stale.
    """

    normalized = _relative_ref("source_ref", ref)
    path = repo_root / normalized
    payload = path.read_bytes()
    record: dict[str, Any] = {
        "path": normalized,
        "byte_length": len(payload),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }
    scoped = packet_scope_digest(payload, scope_ids)
    if scoped is not None:
        record["scoped_sha256"] = scoped
        record["scope_ids"] = sorted({str(x) for x in scope_ids if str(x)})
    return record


def build_experiment_contract(
    *,
    problem_id: str,
    target_statement: str,
    claim_ceiling: str,
    hypothesis_id: str,
    hypothesis_statement: str,
    probe_id: str,
    probe_question: str,
    computation: str,
    falsifier: str,
    stop_condition: str,
    survival_consequence: str,
    falsification_consequence: str,
    consumer_ref: str,
    analysis_refs: Iterable[str],
    source_refs: Iterable[str],
    result_status: str,
    result_summary: str,
    consumer_declarations: Iterable[str] = (),
    input_receipt_refs: Iterable[str] = (),
    resource_bounds: Mapping[str, int] | None = None,
    progress_class: str | None = None,
    decision_basis: str | None = None,
    next_analytic_target: str | None = None,
) -> dict[str, Any]:
    """Build and validate the common receipt fragment used by probe scripts."""

    if result_status not in RESULT_STATUSES:
        raise ValueError(
            f"result_status must be one of {sorted(RESULT_STATUSES)}, got {result_status!r}"
        )
    contract = {
        "schema_version": SCHEMA_VERSION,
        "authority_boundary": (
            "Experiment metadata and finite computation are evidence, not proof authority; "
            "claim status changes only through Lean, an exact counterexample, or the named owner verifier."
        ),
        "problem": {
            "id": _nonempty("problem_id", problem_id),
            "target_statement": _nonempty("target_statement", target_statement),
            "claim_ceiling": _nonempty("claim_ceiling", claim_ceiling),
        },
        "hypothesis": {
            "id": _nonempty("hypothesis_id", hypothesis_id),
            "statement": _nonempty("hypothesis_statement", hypothesis_statement),
        },
        "probe": {
            "id": _nonempty("probe_id", probe_id),
            "question": _nonempty("probe_question", probe_question),
            "computation": _nonempty("computation", computation),
            "falsifier": _nonempty("falsifier", falsifier),
            "stop_condition": _nonempty("stop_condition", stop_condition),
        },
        "analytic_bridge": {
            "survival_consequence": _nonempty(
                "survival_consequence", survival_consequence
            ),
            "falsification_consequence": _nonempty(
                "falsification_consequence", falsification_consequence
            ),
            "consumer_ref": _relative_ref("consumer_ref", consumer_ref),
        },
        "links": {
            "analysis_refs": _refs("analysis_refs", analysis_refs),
            "source_refs": _refs("source_refs", source_refs),
            "input_receipt_refs": [
                _relative_ref(f"input_receipt_refs[{index}]", value)
                for index, value in enumerate(input_receipt_refs)
            ],
        },
        "result": {
            "status": result_status,
            "summary": _nonempty("result_summary", result_summary),
        },
    }
    progress_values = (progress_class, decision_basis, next_analytic_target)
    if any(value is not None for value in progress_values):
        if not all(value is not None for value in progress_values):
            raise ValueError(
                "progress_class, decision_basis, and next_analytic_target "
                "must be provided together"
            )
        if progress_class not in PROGRESS_CLASSES:
            raise ValueError(
                "progress_class must be one of "
                f"{sorted(PROGRESS_CLASSES)}, got {progress_class!r}"
            )
        contract["result"]["progress"] = {
            "class": progress_class,
            "decision_basis": _nonempty("decision_basis", decision_basis),
            "next_analytic_target": _nonempty(
                "next_analytic_target", next_analytic_target
            ),
            "authority_boundary": (
                "This classification routes research attention; it does not promote "
                "finite evidence to proof authority."
            ),
        }
    declarations = _declarations("consumer_declarations", consumer_declarations)
    if declarations:
        contract["analytic_bridge"]["consumer_declarations"] = declarations
    if resource_bounds is not None:
        contract["probe"]["resource_bounds"] = _resource_bounds(resource_bounds)
    validate_experiment_contract(contract)
    return contract


def validate_experiment_contract(
    contract: Mapping[str, Any], *, repo_root: Path | None = None
) -> None:
    """Reject incomplete, unlinked, or non-deterministically shaped contracts."""

    if contract.get("schema_version") != SCHEMA_VERSION:
        raise ValueError(f"schema_version must be {SCHEMA_VERSION!r}")
    problem = contract.get("problem")
    hypothesis = contract.get("hypothesis")
    probe = contract.get("probe")
    bridge = contract.get("analytic_bridge")
    links = contract.get("links")
    result = contract.get("result")
    for label, value in (
        ("problem", problem),
        ("hypothesis", hypothesis),
        ("probe", probe),
        ("analytic_bridge", bridge),
        ("links", links),
        ("result", result),
    ):
        if not isinstance(value, Mapping):
            raise ValueError(f"{label} must be an object")

    for label, value in (
        ("problem.id", problem.get("id")),
        ("problem.target_statement", problem.get("target_statement")),
        ("problem.claim_ceiling", problem.get("claim_ceiling")),
        ("hypothesis.id", hypothesis.get("id")),
        ("hypothesis.statement", hypothesis.get("statement")),
        ("probe.id", probe.get("id")),
        ("probe.question", probe.get("question")),
        ("probe.computation", probe.get("computation")),
        ("probe.falsifier", probe.get("falsifier")),
        ("probe.stop_condition", probe.get("stop_condition")),
        ("analytic_bridge.survival_consequence", bridge.get("survival_consequence")),
        (
            "analytic_bridge.falsification_consequence",
            bridge.get("falsification_consequence"),
        ),
        ("result.summary", result.get("summary")),
    ):
        _nonempty(label, value)

    resource_bounds = probe.get("resource_bounds")
    if resource_bounds is not None:
        _resource_bounds(resource_bounds)

    _relative_ref("analytic_bridge.consumer_ref", bridge.get("consumer_ref"))
    declarations = bridge.get("consumer_declarations", [])
    if not isinstance(declarations, list):
        raise ValueError("analytic_bridge.consumer_declarations must be an array")
    _declarations("analytic_bridge.consumer_declarations", declarations)
    status = result.get("status")
    if status not in RESULT_STATUSES:
        raise ValueError(f"result.status must be one of {sorted(RESULT_STATUSES)}")
    progress = result.get("progress")
    if progress is not None:
        if not isinstance(progress, Mapping):
            raise ValueError("result.progress must be an object")
        progress_class = progress.get("class")
        if progress_class not in PROGRESS_CLASSES:
            raise ValueError(
                "result.progress.class must be one of "
                f"{sorted(PROGRESS_CLASSES)}"
            )
        _nonempty("result.progress.decision_basis", progress.get("decision_basis"))
        _nonempty(
            "result.progress.next_analytic_target",
            progress.get("next_analytic_target"),
        )
        _nonempty(
            "result.progress.authority_boundary",
            progress.get("authority_boundary"),
        )

    normalized_refs: list[str] = []
    for field in ("analysis_refs", "source_refs"):
        values = links.get(field)
        if not isinstance(values, list):
            raise ValueError(f"links.{field} must be an array")
        normalized_refs.extend(_refs(f"links.{field}", values))
    input_refs = links.get("input_receipt_refs")
    if not isinstance(input_refs, list):
        raise ValueError("links.input_receipt_refs must be an array")
    normalized_refs.extend(
        _relative_ref(f"links.input_receipt_refs[{index}]", value)
        for index, value in enumerate(input_refs)
    )
    normalized_refs.append(
        _relative_ref("analytic_bridge.consumer_ref", bridge.get("consumer_ref"))
    )

    if repo_root is not None:
        missing = [ref for ref in normalized_refs if not (repo_root / ref).exists()]
        if missing:
            raise ValueError(f"experiment contract references missing paths: {missing}")


def _embedded_contract(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    if payload.get("schema_version") == SCHEMA_VERSION:
        return payload
    contract = payload.get("experiment_contract")
    if isinstance(contract, Mapping) and contract.get("schema_version") == SCHEMA_VERSION:
        return contract
    return None


def _bound_source_status(
    repo_root: Path,
    source_ref: str,
    source_records: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    """Compare one declared source link with the receipt's content record."""

    record = source_records.get(source_ref)
    source_path = repo_root / source_ref
    if record is None:
        return {"path": source_ref, "status": "missing_source_record"}
    if not source_path.exists():
        return {"path": source_ref, "status": "missing_source_path"}
    current = source_record(repo_root, source_ref)
    expected_digest = record.get("sha256")
    expected_length = record.get("byte_length")
    status = (
        "current"
        if expected_digest == current["sha256"]
        and expected_length == current["byte_length"]
        else "stale_source_record"
    )
    return {
        "path": source_ref,
        "status": status,
        "expected_sha256": expected_digest,
        "current_sha256": current["sha256"],
        "expected_byte_length": expected_length,
        "current_byte_length": current["byte_length"],
    }


def experiment_receipt_record(repo_root: Path, receipt_ref: str) -> dict[str, Any]:
    """Build a compact, source-current discovery record for one receipt.

    The record is navigation and integrity evidence.  It deliberately keeps
    the experiment's claim ceiling and authority boundary unchanged.
    """

    normalized_ref = _relative_ref("receipt_ref", receipt_ref)
    receipt_path = repo_root / normalized_ref
    errors: list[str] = []
    try:
        payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {
            "receipt_ref": normalized_ref,
            "status": "invalid_receipt",
            "validation_errors": [str(exc)],
        }
    if not isinstance(payload, Mapping):
        return {
            "receipt_ref": normalized_ref,
            "status": "invalid_receipt",
            "validation_errors": ["receipt must be a JSON object"],
        }
    contract = _embedded_contract(payload)
    if contract is None:
        return {
            "receipt_ref": normalized_ref,
            "status": "not_experiment_contract",
            "validation_errors": [],
        }
    try:
        validate_experiment_contract(contract, repo_root=repo_root)
    except ValueError as exc:
        errors.append(str(exc))

    links = contract.get("links") if isinstance(contract.get("links"), Mapping) else {}
    bridge = (
        contract.get("analytic_bridge")
        if isinstance(contract.get("analytic_bridge"), Mapping)
        else {}
    )
    result = contract.get("result") if isinstance(contract.get("result"), Mapping) else {}
    progress = result.get("progress") if isinstance(result.get("progress"), Mapping) else {}
    problem = contract.get("problem") if isinstance(contract.get("problem"), Mapping) else {}
    hypothesis = (
        contract.get("hypothesis")
        if isinstance(contract.get("hypothesis"), Mapping)
        else {}
    )
    probe = contract.get("probe") if isinstance(contract.get("probe"), Mapping) else {}

    source_records: dict[str, Mapping[str, Any]] = {}
    for record_key in ("sources", "source_records"):
        raw_records = payload.get(record_key)
        if not isinstance(raw_records, list):
            continue
        for item in raw_records:
            if not isinstance(item, Mapping) or not isinstance(item.get("path"), str):
                continue
            path = item["path"]
            previous = source_records.get(path)
            if previous is not None and previous != item:
                errors.append(
                    f"conflicting source records for {path!r} across receipt record arrays"
                )
                continue
            source_records[path] = item
    source_refs = list(links.get("source_refs") or [])
    source_integrity = [
        _bound_source_status(repo_root, ref, source_records)
        for ref in source_refs
        if isinstance(ref, str)
    ]
    analysis_refs = list(links.get("analysis_refs") or [])
    analysis_integrity = [
        _bound_source_status(repo_root, ref, source_records)
        for ref in analysis_refs
        if isinstance(ref, str)
    ]
    consumer_ref = bridge.get("consumer_ref")
    consumer_integrity = (
        [_bound_source_status(repo_root, consumer_ref, source_records)]
        if isinstance(consumer_ref, str)
        else []
    )
    bound_artifact_integrity = (
        source_integrity + analysis_integrity + consumer_integrity
    )
    stale_source_count = sum(
        row["status"] != "current" for row in source_integrity
    )
    stale_analysis_count = sum(
        row["status"] != "current" for row in analysis_integrity
    )
    stale_consumer_count = sum(
        row["status"] != "current" for row in consumer_integrity
    )
    stale_bound_artifact_count = sum(
        row["status"] != "current" for row in bound_artifact_integrity
    )
    status = (
        "current"
        if not errors and stale_bound_artifact_count == 0
        else "attention"
    )
    return {
        "receipt_ref": normalized_ref,
        "status": status,
        "problem_id": problem.get("id"),
        "target_statement": problem.get("target_statement"),
        "claim_ceiling": problem.get("claim_ceiling"),
        "hypothesis_id": hypothesis.get("id"),
        "hypothesis_statement": hypothesis.get("statement"),
        "probe_id": probe.get("id"),
        "probe_question": probe.get("question"),
        "computation": probe.get("computation"),
        "falsifier": probe.get("falsifier"),
        "stop_condition": probe.get("stop_condition"),
        "resource_bounds": dict(probe.get("resource_bounds") or {}),
        "result_status": result.get("status"),
        "result_summary": result.get("summary"),
        "progress_class": progress.get("class"),
        "decision_basis": progress.get("decision_basis"),
        "next_analytic_target": progress.get("next_analytic_target"),
        "survival_consequence": bridge.get("survival_consequence"),
        "falsification_consequence": bridge.get("falsification_consequence"),
        "analysis_refs": analysis_refs,
        "source_refs": source_refs,
        "input_receipt_refs": list(links.get("input_receipt_refs") or []),
        "consumer_ref": consumer_ref,
        "consumer_declarations": list(bridge.get("consumer_declarations") or []),
        "source_integrity": source_integrity,
        "analysis_integrity": analysis_integrity,
        "consumer_integrity": consumer_integrity,
        "bound_artifact_integrity": bound_artifact_integrity,
        "stale_source_count": stale_source_count,
        "stale_analysis_count": stale_analysis_count,
        "stale_consumer_count": stale_consumer_count,
        "stale_bound_artifact_count": stale_bound_artifact_count,
        "validation_errors": errors,
        "authority_boundary": contract.get("authority_boundary"),
    }


def scan_experiment_receipts(
    repo_root: Path,
    *,
    roots: Iterable[Path] = DEFAULT_RECEIPT_ROOTS,
    receipt_refs: Iterable[str] = (),
    problem_id: str | None = None,
    hypothesis_id: str | None = None,
    probe_id: str | None = None,
    progress_class: str | None = None,
    consumer_ref: str | None = None,
    contains: str | None = None,
) -> dict[str, Any]:
    """Discover embedded experiment contracts and expose their analytic graph."""

    explicit_refs = sorted(set(receipt_refs))
    candidates: list[Path] = []
    if explicit_refs:
        candidates = [repo_root / _relative_ref("receipt_ref", ref) for ref in explicit_refs]
    else:
        for root in roots:
            base = root if root.is_absolute() else repo_root / root
            if base.exists():
                candidates.extend(base.rglob("*.json"))

    records: list[dict[str, Any]] = []
    for path in sorted(set(candidates)):
        try:
            raw = path.read_bytes()
        except OSError:
            continue
        if SCHEMA_VERSION.encode() not in raw:
            continue
        ref = path.relative_to(repo_root).as_posix()
        record = experiment_receipt_record(repo_root, ref)
        if record.get("status") == "not_experiment_contract":
            continue
        exact_filters = (
            ("problem_id", problem_id),
            ("hypothesis_id", hypothesis_id),
            ("probe_id", probe_id),
            ("progress_class", progress_class),
            ("consumer_ref", consumer_ref),
        )
        if any(
            value is not None and record.get(key) != value
            for key, value in exact_filters
        ):
            continue
        if contains is not None:
            needle = contains.casefold()
            routing_fields = (
                "target_statement",
                "claim_ceiling",
                "hypothesis_statement",
                "probe_question",
                "computation",
                "falsifier",
                "stop_condition",
                "result_summary",
                "decision_basis",
                "next_analytic_target",
                "survival_consequence",
                "falsification_consequence",
            )
            if not any(
                needle in str(record.get(field) or "").casefold()
                for field in routing_fields
            ):
                continue
        records.append(record)

    attention_count = sum(row.get("status") != "current" for row in records)
    return {
        "schema_version": "formal_math_experiment_contract_scan_v0",
        "status": "current" if attention_count == 0 else "attention",
        "receipt_count": len(records),
        "current_receipt_count": len(records) - attention_count,
        "attention_receipt_count": attention_count,
        "records": records,
        "authority_boundary": (
            "This scan validates provenance and routing links; it does not promote "
            "experimental evidence to theorem authority."
        ),
    }


def _main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Discover and validate formal-math experiment contracts."
    )
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--root", action="append", type=Path, default=[])
    parser.add_argument("--receipt", action="append", default=[])
    parser.add_argument("--problem-id")
    parser.add_argument("--hypothesis-id")
    parser.add_argument("--probe-id")
    parser.add_argument("--progress-class", choices=sorted(PROGRESS_CLASSES))
    parser.add_argument("--consumer-ref")
    parser.add_argument(
        "--contains",
        help=(
            "Case-insensitive text filter over the hypothesis, probe, falsifier, "
            "stop rule, result, and analytic consequences."
        ),
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    report = scan_experiment_receipts(
        args.repo_root.resolve(),
        roots=args.root or DEFAULT_RECEIPT_ROOTS,
        receipt_refs=args.receipt,
        problem_id=args.problem_id,
        hypothesis_id=args.hypothesis_id,
        probe_id=args.probe_id,
        progress_class=args.progress_class,
        consumer_ref=args.consumer_ref,
        contains=args.contains,
    )
    json.dump(report, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 1 if args.check and report["attention_receipt_count"] else 0


if __name__ == "__main__":
    raise SystemExit(_main())
