#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Read-only checker for a fixed mathematical assimilation cut.

Checks a FIXED reviewed mathematical-assimilation cut against Type A's trusted
receipt index. It does not write Lean, run Comparator, post PRs or prove prose.
Trusted receipt producers must be implemented and independently reviewed
before production admission.

A `source_consistent_external_pending` cut is not a completed Comparator review.
Source correctness, external comparison and remote publication are separate.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any
from research_return_gate import (GateError, bytes_sha, checked_receipts, digest,
                                  hex_digest, read_json, require, safe_file)

ROLES = ("lean", "claims", "graph", "frontier", "short_paper", "long_record",
         "paper_lean_ledger", "route_memory", "contrasts", "reader_summary", "comparator_queue")
GLOBAL_CHECKS = {"impact_analysis", "natural_generality_review", "release_checks",
                 "record_parent", "claim_gate"}

def validate(cut: dict[str, Any], checkout: Path, evidence_index: dict[str, Any],
             evidence_root: Path, receipt_ids: list[str]) -> dict[str, Any]:
    require(set(cut) == {"schema", "cut_id", "foundation_sha256", "formal_source_commit",
                        "record_parent_sha256", "claims", "files", "consumers"},
            "cut fields differ from reviewed contract")
    require(cut["schema"] == "plectis-assimilation-cut/1", "wrong cut schema")
    foundation = hex_digest(cut["foundation_sha256"], "foundation")
    hex_digest(cut["record_parent_sha256"], "record parent")
    require(isinstance(cut["formal_source_commit"], str)
            and len(cut["formal_source_commit"]) == 40
            and all(c in "0123456789abcdef" for c in cut["formal_source_commit"]),
            "formal-source commit must be exact")
    require(isinstance(cut["cut_id"], str) and bool(cut["cut_id"]), "missing cut ID")
    claims = cut["claims"]
    require(isinstance(claims, list) and bool(claims)
            and all(isinstance(c, str) and c for c in claims)
            and len(claims) == len(set(claims)), "bad or duplicate claim IDs")
    require(isinstance(cut["files"], dict) and bool(cut["files"]), "empty input closure")
    for path, sha in cut["files"].items():
        require(bytes_sha(safe_file(checkout, path).read_bytes()) == hex_digest(sha, path),
                f"changed artifact or dependency: {path}")
    # Claims, tools, templates, definitions, toolchain and dependency locks must
    # all be included by the independently checked impact-analysis producer.
    # Listing just outputs does not constitute that closure.
    subject = digest(cut)
    receipts = checked_receipts(evidence_index, evidence_root, receipt_ids, subject, foundation)
    admitted: dict[str, dict[str, Any]] = {}
    for r in receipts:
        check = r["check"]
        require(check in GLOBAL_CHECKS or check in {"comparator_result", "remote_publication"}
                or check.startswith("consumer/"), f"unexpected assimilation check: {check}")
        if r["status"] != "checked":
            continue
        require(r.get("evidence_class") == "owner_verified_assimilation", "wrong assimilation evidence")
        for field in ("validator_sha256", "inputs_sha256"):
            hex_digest(r.get(field), field)
        require(r["inputs_sha256"] == digest(cut["files"]), "receipt has another dependency closure")
        admitted[check] = r
    require(GLOBAL_CHECKS <= admitted.keys(), "missing checked global obligations: "
            + ",".join(sorted(GLOBAL_CHECKS - admitted.keys())))
    consumers = cut["consumers"]
    require(isinstance(consumers, list), "bad consumers")
    seen: set[tuple[str, str]] = set()
    deferred = []
    for row in consumers:
        require(set(row) == {"claim_id", "role", "disposition", "paths", "reason", "owner", "trigger"},
                "bad consumer row")
        claim, role = row["claim_id"], row["role"]
        require(claim in claims and role in ROLES, "consumer outside declared policy")
        key = (claim, role)
        require(key not in seen, "duplicate consumer binding"); seen.add(key)
        require(row["disposition"] in {"updated", "unchanged", "not_applicable", "deferred"},
                "bad consumer disposition")
        check = f"consumer/{claim}/{role}"
        require(check in admitted, f"missing verified consumer obligation: {check}")
        require(isinstance(row["paths"], list) and all(isinstance(p, str) for p in row["paths"]),
                "bad consumer paths")
        require(set(row["paths"]) <= cut["files"].keys(), "consumer path outside dependency closure")
        if row["disposition"] in {"updated", "unchanged"}:
            require(bool(row["paths"]), "active consumer has no bound artifact")
        if row["disposition"] in {"not_applicable", "deferred"}:
            require(isinstance(row["reason"], str) and bool(row["reason"].strip()), "missing disposition reason")
        if row["disposition"] == "deferred":
            require(role == "comparator_queue", "core source consistency may not be deferred")
            require(isinstance(row["owner"], str) and bool(row["owner"].strip())
                    and isinstance(row["trigger"], str) and bool(row["trigger"].strip()),
                    "deferral needs owner and observable trigger")
            deferred.append(check)
        # NA is an owner-reviewed exception, never an unreviewed return flag.
        # Essential mathematical consumers are mandatory for this fixed policy.
        if role in {"lean", "claims", "graph", "frontier", "short_paper", "long_record", "paper_lean_ledger", "reader_summary"}:
            require(row["disposition"] != "not_applicable", f"essential consumer cannot be NA: {role}")
    expected = {(claim, role) for claim in claims for role in ROLES}
    require(seen == expected, "missing consumer coverage: " + repr(sorted(expected - seen)))
    allowed_consumer_checks = {f"consumer/{claim}/{role}" for claim, role in expected}
    require(all(not c.startswith("consumer/") or c in allowed_consumer_checks for c in admitted),
            "receipt describes an undeclared consumer")
    compared = "comparator_result" in admitted
    require(not (deferred and compared), "Comparator result conflicts with deferred queue state")
    return {"schema": "plectis-assimilation-check/1", "cut_sha256": subject,
            "claims": claims, "consumer_obligations": len(expected),
            "source_status": "consistent_under_owner_verified_obligations",
            "comparator_status": "compared" if compared else "pending_not_claimed_passed",
            "remote_publication": "verified" if "remote_publication" in admitted else "not_established",
            "round_status": "closed" if compared and "remote_publication" in admitted else "not_fully_closed",
            "production_admission": False,
            "journal_append": {"expected_parent_sha256": cut["record_parent_sha256"],
                               "cut_sha256": subject},
            "authority_boundary": "No mutation. Native research_record owner must perform CAS/append after verification."}

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("cut", type=Path); p.add_argument("--checkout", type=Path, required=True)
    p.add_argument("--evidence-index", type=Path, required=True)
    p.add_argument("--evidence-root", type=Path, required=True)
    p.add_argument("--receipt", action="append", default=[])
    a = p.parse_args()
    try:
        value = validate(read_json(a.cut), a.checkout, read_json(a.evidence_index),
                         a.evidence_root, a.receipt)
        print(json.dumps(value, indent=2)); return 0
    except (GateError, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({"status": "blocked", "error": str(error)})); return 2

if __name__ == "__main__":
    raise SystemExit(main())
