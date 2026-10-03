#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Read-only research-return evidence assessment.

A read-only, abstention-first adapter, not a proof checker or a second registry.
The evidence index must be supplied by Type A from an independently controlled
verification lane. Hashes protect byte identity; they do NOT authenticate its
operator. Never use an index delivered by the return being assessed.

extract: preserve every non-whitespace paragraph and suggest claim candidates.
assess: consume exact-request-bound, owner-allowlisted receipts. No subprocess,
network, eval, arbitrary tactic execution, publication, or journal mutation.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
from typing import Any

SHA = re.compile(r"[0-9a-f]{64}\Z")
AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})
KERNEL_CHECKS = frozenset({"proof", "refutation", "context_refutation",
    "feasible", "new_to_old", "old_to_new", "separator_new_not_old",
    "separator_old_not_new"})
REVIEW_CHECKS = {"interpretation": "reviewed_interpretation",
    "existing_exact": "reviewed_corpus_identity",
    "existing_variant": "reviewed_corpus_identity",
    "literature_match": "reviewed_literature_comparison",
    "corpus_search": "bounded_search_record",
    "literature_search": "bounded_search_record"}
CHECKS = KERNEL_CHECKS | REVIEW_CHECKS.keys()

class GateError(ValueError):
    """Invalid or stale evidence; do not replace with a positive verdict."""

def canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")

def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()

def bytes_sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def require(condition: bool, message: str) -> None:
    if not condition:
        raise GateError(message)

def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result

def read_json(path: Path) -> Any:
    def bad_constant(value: str) -> Any:
        raise GateError(f"non-finite JSON constant: {value}")
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_pairs,
                      parse_constant=bad_constant)

def safe_file(root: Path, relative: str) -> Path:
    """Reject symlinks at every component. Caller must use an immutable checkout.

    This is not an OS sandbox and does not claim race resistance under hostile
    concurrent writes. The verification lane must freeze/unshare its inputs.
    """
    require(isinstance(relative, str) and bool(relative), "missing relative path")
    p = PurePosixPath(relative)
    require(not p.is_absolute() and all(x not in {".", ".."} for x in p.parts)
            and "\\" not in relative and str(p) == relative, "unsafe/noncanonical path")
    current = root.absolute()
    require(not current.is_symlink(), "root is a symlink")
    for part in p.parts:
        current = current / part
        require(not current.is_symlink(), f"symlink rejected: {relative}")
    require(current.is_file(), f"missing regular file: {relative}")
    return current

def hex_digest(value: Any, field: str) -> str:
    require(isinstance(value, str) and SHA.fullmatch(value) is not None,
            f"{field} must be a full lowercase SHA256")
    return value

def checked_receipts(index: dict[str, Any], root: Path, ids: list[str],
                     subject_sha: str, foundation_sha: str) -> list[dict[str, Any]]:
    """Read receipt bytes; the out-of-band index grants producer capabilities.

    A receipt self-declaring a producer/check/pass is not enough. The trusted
    index pins its bytes AND authorizes that exact producer for the check.
    """
    require(isinstance(index, dict), "evidence index must be a JSON object")
    require(index.get("schema") == "plectis-trusted-evidence-index/1", "wrong evidence index")
    require(isinstance(index.get("receipts"), dict) and isinstance(index.get("producers"), dict),
            "bad trusted-index maps")
    require(isinstance(ids, list) and all(isinstance(x, str) for x in ids), "bad receipt IDs")
    require(len(ids) == len(set(ids)), "duplicate receipt ID")
    found = []
    for rid in ids:
        row = index.get("receipts", {}).get(rid)
        require(isinstance(row, dict), f"receipt not in trusted index: {rid}")
        data = safe_file(root, row["path"]).read_bytes()
        require(bytes_sha(data) == hex_digest(row.get("sha256"), "receipt hash"),
                f"changed receipt bytes: {rid}")
        receipt = read_json(safe_file(root, row["path"]))
        require(isinstance(receipt, dict), f"receipt must be a JSON object: {rid}")
        require(receipt.get("schema") == "plectis-checked-evidence/1", "wrong receipt schema")
        require(receipt.get("subject_sha256") == subject_sha, f"receipt for another request: {rid}")
        require(receipt.get("foundation_sha256") == foundation_sha, f"stale foundation: {rid}")
        producer, check = receipt.get("producer"), receipt.get("check")
        require(isinstance(producer, str) and isinstance(check, str), "missing producer/check")
        capabilities = index.get("producers", {}).get(producer, [])
        require(isinstance(capabilities, list) and all(isinstance(c, str) for c in capabilities),
                "producer capabilities must be a list of check names")
        require(check in capabilities, f"unauthorized producer/check: {producer}/{check}")
        require(receipt.get("status") in {"checked", "unknown"}, "unsupported evidence status")
        # A log-only or atlas-only report may be preserved, but is not silently
        # promoted to either a semantic or a kernel receipt by this reader.
        found.append(receipt)
    require(len({r["check"] for r in found}) == len(found),
            "conflicting/duplicate checks: owner must resolve revisions explicitly")
    return found

def extract(path: Path) -> dict[str, Any]:
    """Lossless paragraph coverage, NOT certified semantic claim extraction."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    spans = []
    cursor = byte_cursor = 0
    for n, match in enumerate(re.finditer(r"\S[\s\S]*?(?=\n\s*\n|\Z)", text)):
        start = byte_cursor + len(text[cursor:match.start()].encode("utf-8"))
        chunk = match.group(0).encode("utf-8")
        cursor, byte_cursor = match.end(), start + len(chunk)
        spans.append({"span_id": f"p{n:04d}", "start_byte": start,
            "end_byte": start + len(chunk), "sha256": bytes_sha(chunk),
            "text": match.group(0), "candidate": bool(re.search(
                r"\b(theorem|lemma|prove[sd]?|equivalent|new|novel|claim|implies|solves?|bound)\b",
                match.group(0), flags=re.I))})
    return {"schema": "plectis-return-extraction/1", "source_sha256": bytes_sha(data),
            "source_bytes": len(data), "all_paragraphs": spans,
            "semantic_coverage": "review_required", "authority": "untrusted_return_text"}

def validate_request(request: dict[str, Any]) -> None:
    fields = {"schema", "claim_id", "source_span", "kind", "foundation_sha256",
              "context_sha256", "new_statement_sha256", "old_statement_sha256",
              "assumptions", "goals", "comparison_basis", "comparison_role"}
    require(set(request) == fields, "request fields differ from reviewed contract")
    require(request["schema"] == "plectis-gate-request/1", "wrong request schema")
    require(request["kind"] == "mathematical", "this adapter assesses mathematical claims only")
    for key in ("foundation_sha256", "context_sha256", "new_statement_sha256", "old_statement_sha256"):
        hex_digest(request[key], key)
    require(isinstance(request["claim_id"], str) and bool(request["claim_id"]), "missing claim ID")
    require(isinstance(request["assumptions"], list)
            and all(isinstance(x, str) for x in request["assumptions"]), "bad assumptions")
    require(request["comparison_basis"] in {"restricted_relation", "unrestricted_provability"},
            "unrecognized comparison basis")
    require(request["comparison_role"] in {"theorem_statement", "hypothesis_replacement", "endpoint_route"},
            "comparison role must be explicit")
    span = request["source_span"]
    require(set(span) == {"return_sha256", "start_byte", "end_byte", "span_sha256"}, "bad span")
    hex_digest(span["return_sha256"], "return hash")
    hex_digest(span["span_sha256"], "span hash")
    require(type(span["start_byte"]) is int and type(span["end_byte"]) is int
            and 0 <= span["start_byte"] < span["end_byte"], "bad byte span")
    require(isinstance(request["goals"], dict) and set(request["goals"]) <= KERNEL_CHECKS,
            "unknown goal binding")
    for sha in request["goals"].values():
        hex_digest(sha, "elaborated goal hash")

def assess(request: dict[str, Any], index: dict[str, Any], evidence_root: Path,
           receipt_ids: list[str], return_path: Path) -> dict[str, Any]:
    validate_request(request)
    raw = return_path.read_bytes()
    span = request["source_span"]
    require(bytes_sha(raw) == span["return_sha256"], "return bytes changed")
    require(span["end_byte"] <= len(raw), "span outside return")
    require(bytes_sha(raw[span["start_byte"]:span["end_byte"]]) == span["span_sha256"],
            "claimed source span changed")
    subject = digest(request)
    receipts = checked_receipts(index, evidence_root, receipt_ids, subject,
                                request["foundation_sha256"])
    admitted: dict[str, dict[str, Any]] = {}
    for r in receipts:
        check = r["check"]
        require(check in CHECKS, f"unknown gate check: {check}")
        if r["status"] != "checked":
            continue
        if check in KERNEL_CHECKS:
            require(r.get("evidence_class") == "kernel_checked", "nonkernel logical verdict")
            require(request["goals"].get(check) is not None and
                    r.get("goal_sha256") == request["goals"][check], "wrong elaborated goal")
            axioms = r.get("axioms")
            require(isinstance(axioms, list) and all(isinstance(a, str) for a in axioms)
                    and set(axioms) <= AXIOMS, "disallowed or missing axiom audit")
            for key in ("proof_sha256", "checker_sha256", "dependency_manifest_sha256"):
                hex_digest(r.get(key), key)
        else:
            require(r.get("evidence_class") == REVIEW_CHECKS[check], "wrong review evidence class")
            if check.endswith("search"):
                require(isinstance(r.get("scope"), dict) and bool(r["scope"])
                        and isinstance(r.get("unsearched"), list), "search coverage absent")
        admitted[check] = r
    result: dict[str, Any] = {"schema": "plectis-gate-verdict/1", "claim_id": request["claim_id"],
        "request_sha256": subject, "comparison_role": request["comparison_role"], "interpretation": "pending", "formal_correctness": "unknown",
        "relation": "unknown", "feasibility": "unknown", "corpus_status": "unassessed",
        "literature_status": "unassessed", "assumptions": request["assumptions"],
        "action": "review_interpretation", "new_mathematical_credit": "not_authorized",
        "evidence_checks": sorted(admitted)}
    if "interpretation" not in admitted:
        return result
    result["interpretation"] = "reviewed_and_bound"
    has = admitted.__contains__
    # The fixed goal contract is pointwise over one shared context Γ:
    # proof = Supplied Γ N; refutation = Refuted Γ N; feasible = Feasible Γ N.
    # Supply and refutation together imply an EMPTY context, not a kernel
    # inconsistency. A separator/feasibility witness makes it inconsistent.
    empty_context = has("context_refutation") or (has("proof") and has("refutation"))
    context_witness = any(has(k) for k in ("feasible", "separator_new_not_old", "separator_old_not_new"))
    conflicts = ((empty_context and context_witness)
        or (has("feasible") and has("refutation"))
        or (has("new_to_old") and has("separator_new_not_old"))
        or (has("old_to_new") and has("separator_old_not_new"))
        or (has("proof") and has("separator_old_not_new"))
        or (has("refutation") and has("separator_new_not_old")))
    if conflicts:
        result.update(action="quarantine_evidence_conflict", formal_correctness="evidence_conflict")
        return result
    if empty_context:
        result.update(feasibility="context_refuted", action="retain_vacuous_statement_no_endpoint_credit",
            vacuity_basis="explicit_context_refutation" if has("context_refutation") else
                           "derived_from_supply_and_refutation_in_shared_context")
        return result
    if has("refutation"):
        result.update(formal_correctness="refuted", action="reject_claim_preserve_return")
        return result
    if has("proof"):
        result["formal_correctness"] = "kernel_checked_in_declared_context"
    if has("feasible"):
        result["feasibility"] = "witness_checked"
    # Equivalence of arbitrary closed true propositions is not identity or novelty.
    if request["comparison_basis"] == "restricted_relation":
        forward, backward = has("new_to_old"), has("old_to_new")
        if forward and backward:
            result["relation"] = "equivalent_under_declared_context"
        elif forward:
            result["relation"] = ("strictly_stronger" if has("separator_old_not_new")
                                  else "sufficient_converse_unknown")
        elif backward:
            result["relation"] = ("strictly_weaker" if has("separator_new_not_old")
                                  else "necessary_converse_unknown")
    else:
        result["relation"] = "provability_only_not_a_novelty_comparison"
    if has("existing_exact"):
        result["corpus_status"] = "existing_exact_statement"
    elif has("existing_variant"):
        result["corpus_status"] = "existing_reviewed_variant_or_specialization"
    elif has("corpus_search"):
        result["corpus_status"] = "not_located_in_recorded_search"
        result["corpus_search_scope"] = admitted["corpus_search"]["scope"]
        result["corpus_unsearched"] = admitted["corpus_search"]["unsearched"]
    if has("literature_match"):
        result["literature_status"] = "matched_reviewed_prior_result"
    elif has("literature_search"):
        result["literature_status"] = "not_located_in_recorded_search"
        result["literature_search_scope"] = admitted["literature_search"]["scope"]
        result["literature_unsearched"] = admitted["literature_search"]["unsearched"]
    if result["corpus_status"].startswith("existing_"):
        result["action"] = "retain_provenance_no_duplicate_statement_credit"
    elif result["relation"] == "equivalent_under_declared_context":
        result["action"] = "assess_representation_utility_separately"
    elif has("proof"):
        result["action"] = "review_natural_generality_and_assimilation"
    else:
        result["action"] = "retain_conditional_or_unproved_candidate"
    return result

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    e = sub.add_parser("extract"); e.add_argument("return_file", type=Path)
    a = sub.add_parser("assess")
    a.add_argument("request", type=Path); a.add_argument("--return-file", type=Path, required=True)
    a.add_argument("--evidence-index", type=Path, required=True)
    a.add_argument("--evidence-root", type=Path, required=True)
    a.add_argument("--receipt", action="append", default=[])
    args = parser.parse_args()
    try:
        value = extract(args.return_file) if args.command == "extract" else assess(
            read_json(args.request), read_json(args.evidence_index), args.evidence_root,
            args.receipt, args.return_file)
        print(json.dumps(value, indent=2, ensure_ascii=False)); return 0
    except (GateError, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({"status": "invalid_input_or_evidence", "error": str(error)})); return 2

if __name__ == "__main__":
    raise SystemExit(main())
