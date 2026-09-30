#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Offline claim-evidence join below paper_evidence, never a second proof authority.

The existing coverage inventory, resolved evidence, associations, dependency index,
and claims owner are the inputs. All checks in this module are structural. A passing
join is NOT a new Lean/Comparator execution or an informal-to-formal semantic review.
A diagnostic build writes its gaps; the admission command returns 1 on any gap.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any, Callable

import check_lean_paper_propagation as propagation
import paper_evidence as native

SCHEMA = "claim_evidence/1"
REPORT_SCHEMA = "plectis-claim-evidence-report/1"
POLICY_SCHEMA = "plectis-claim-evidence-policy/1"
POLICY_KEY = "paper_claim_evidence"
OUTPUT = "evidence/claim_evidence.json"
INDEX = "docs/lean_dependency_index.json"
CLAIMS = "docs/claims.json"
ANN = "evidence/nonformal_claim_evidence.json"
STATUS_PATTERN = re.compile(r"\\claimstatus\{([^{}]+)\}\{([^{}]+)\}")
PROBLEM_IDS = (68, 243, 249, 251, 257, 269, 1041, 1049)
OWNERS = {
    "inventory": "docs/paper_lean_coverage.json / paper maintainer",
    "declaration": "scripts/check_lean_paper_propagation.py / Lean source maintainer",
    "index": "scripts/build_lean_dependency_index.py / dependency-export maintainer",
    "comparator": "evidence/comparator/associations.json / Comparator evidence maintainer",
    "nonformal": "docs/claims.json::paper_claim_evidence / paper and proof-review maintainer",
    "status": "scripts/paper_evidence.py / paper writer",
    "identity": "scripts/paper_evidence.py / release evidence maintainer",
}
REQUIRED = ("paper_id", "claim_locator", "statement_hash", "evidence_class",
            "lean_declaration", "comparator_receipt", "ordinary_proof_locator",
            "status_phrase_required")


def digest(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def canonical(data: Any) -> bytes:
    return (json.dumps(data, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode()


def safe_relative(path: str) -> str:
    if not isinstance(path, str) or not path or any(x in path for x in ("\x00", "\n", "\r", "\\")):
        raise ValueError(f"invalid evidence path: {path!r}")
    pp = PurePosixPath(path)
    if pp.is_absolute() or ".." in pp.parts or ".git" in pp.parts or str(pp) != path:
        raise ValueError(f"unsafe evidence path: {path!r}")
    return path


class Inputs:
    """Cache exact bytes from the caller's worktree, staged tree or pinned reader."""
    def __init__(self, read: Callable[[str], bytes]):
        self.read = read
        self.cache: dict[str, bytes] = {}

    def blob(self, path: str) -> bytes:
        path = safe_relative(path)
        if path not in self.cache:
            self.cache[path] = self.read(path)
        return self.cache[path]

    def text(self, path: str) -> str:
        return self.blob(path).decode("utf-8")

    def data(self, path: str) -> dict:
        obj = json.loads(self.text(path))
        if not isinstance(obj, dict):
            raise ValueError(f"{path}: expected an object")
        return obj

    def span(self, locator: dict) -> str:
        """Review/computation anchors bind the exact bytes of a nonempty line range."""
        if not isinstance(locator, dict):
            raise ValueError("evidence locator must be an object")
        path = locator.get("path")
        lines = self.text(path).splitlines(keepends=True)
        start, end = locator.get("start_line"), locator.get("end_line")
        if type(start) is not int or type(end) is not int or not 1 <= start <= end <= len(lines):
            raise ValueError(f"{path}: invalid evidence span")
        content = "".join(lines[start - 1:end])
        if digest(content.encode()) != locator.get("sha256"):
            raise ValueError(f"{path}:{start}-{end}: evidence span digest mismatch")
        return content


def root_reader(root: Path) -> Callable[[str], bytes]:
    # Reuse the publication reader's no-symlink boundary, after path containment.
    from publication_contract import RepositoryReader
    reader = RepositoryReader(root)
    return lambda p: reader.read_bytes(safe_relative(p))


def unique_rows(values: Any, key: str, label: str) -> dict[str, dict]:
    if not isinstance(values, list):
        raise ValueError(f"{label}: expected a list")
    result = {}
    for value in values:
        if not isinstance(value, dict) or not isinstance(value.get(key), str) or not value[key]:
            raise ValueError(f"{label}: missing {key}")
        if value[key] in result:
            raise ValueError(f"{label}: duplicate {key} {value[key]}")
        result[value[key]] = value
    return result


def receipt_errors(receipt: dict, assoc: dict, config: dict) -> list[str]:
    """Check recorded receipt identity, not its truth by rerunning the verifier."""
    errors = []
    expect = {
        "schema": native.RECEIPT_SCHEMA, "entry": assoc.get("entry"),
        "exit": 0, "process_exit": 0, "render_audit_exit": 0,
        "kernel_acceptance": {"lean_default": True, "nanoda": True},
    }
    for key, expected in expect.items():
        got = receipt.get(key)
        if got != expected or (type(expected) is int and type(got) is not int):
            errors.append(key)
    kernel = receipt.get("kernel_acceptance", {})
    if not isinstance(kernel, dict) or any(kernel.get(k) is not True for k in ("lean_default", "nanoda")):
        errors.append("kernel_acceptance_flags")
    github = receipt.get("github") or {}
    if github.get("repository") != "wcook04/plectis-erdos-lean":
        errors.append("repository")
    if github.get("sha") != config.get("corpus_commit"):
        errors.append("corpus_commit")
    if str(github.get("run_id")) != str(config.get("replay", {}).get("run_id")):
        errors.append("run_id")
    if receipt.get("verification", {}).get("outcome") != "passed":
        errors.append("outcome")
    if sorted(receipt.get("permitted_axioms") or []) != sorted(native.PERMITTED_AXIOMS):
        errors.append("permitted_axioms")
    if sorted(receipt.get("axiom_audit", {}).get("permitted_axioms") or []) != sorted(native.PERMITTED_AXIOMS):
        errors.append("axiom_audit")
    names = receipt.get("theorem_names")
    if not isinstance(names, list) or len(names) != len(set(names)) or assoc.get("challenge") not in names:
        errors.append("selected_theorem")
    if not isinstance(names, list) or type(receipt.get("theorem_count")) is not int or receipt.get("theorem_count") != len(names):
        errors.append("theorem_count")
    entries = receipt.get("entry_digests") or {}
    for name in ("Challenge.lean", "comparator.json", "formalization.yaml"):
        if not re.fullmatch(r"[0-9a-f]{64}", str(entries.get(name, ""))):
            errors.append(f"missing_digest:{name}")
    files = receipt.get("solution", {}).get("files") or {}
    if not files or assoc.get("solution_path") not in files:
        errors.append("solution_path")
    for path, sha in files.items():
        try:
            safe_relative(path)
        except ValueError:
            errors.append("unsafe_solution_path")
        if not re.fullmatch(r"[0-9a-f]{64}", str(sha)):
            errors.append("solution_digest")
    return errors


def nonformal_class(inputs: Inputs, ann: dict, row: dict) -> tuple[str, dict, list[str]]:
    """Typed, statement-bound attestations; no class is inferred from narrative prose."""
    errors = []
    if ann.get("statement_hash") != row.get("statement_sha256"):
        errors.append("nonformal attestation is for another statement")
    cls = ann.get("evidence_class")
    if cls not in ("ordinary_reviewed", "computed", "cited"):
        errors.append("unsupported nonformal evidence class")
    for key in {"ordinary_reviewed": ("proof", "review"), "computed": ("computation",),
                "cited": ("source",)}.get(cls, ()):
        try:
            inputs.span(ann.get(key))
        except (OSError, ValueError, TypeError, UnicodeError) as error:
            errors.append(str(error))
    if cls == "ordinary_reviewed":
        if ann.get("reviewer_kind") not in ("human", "ai") or not ann.get("reviewer_id"):
            errors.append("ordinary review must identify reviewer and human/AI kind")
        if not ann.get("review_scope") or ann.get("review_outcome") != "accepted":
            errors.append("ordinary review needs explicit scope and accepted outcome")
        # A matching review blob is an attestation, not authentication of a person.
    if cls == "computed" and (not ann.get("domain") or not ann.get("command")):
        errors.append("computed evidence must retain its domain and command")
    if cls == "cited" and (not ann.get("source_version") or not ann.get("theorem_locator")):
        errors.append("cited evidence requires a source version and theorem locator")
    if not isinstance(ann.get("assumptions", []), list):
        errors.append("assumptions must be a list")
    return cls, ann, errors


def status_phrase(row: dict) -> str:
    cls = row["evidence_class"]
    if cls == "evidence_gap":
        return "Evidence binding incomplete; consult the named evidence gaps before asserting a verification status."
    if row["conditional"] and cls in ("lean", "comparator"):
        names = "; ".join(row["named_inputs"]) or row.get("scope") or "the stated named inputs"
        return "Conditional formal evidence recorded; assumptions remain: " + names + "."
    return {
        "lean": "Lean evidence recorded for the listed declaration(s); no fresh kernel replay is claimed here.",
        "comparator": "Comparator replay recorded for every listed declaration; this is not a review of the prose correspondence.",
        "ordinary_reviewed": "Ordinary proof with a recorded " + (row.get("reviewer_kind") or "unspecified") + " review; not a Lean or Comparator check.",
        "computed": "Computed evidence on the recorded domain; this does not certify the general theorem.",
        "cited": "Cited result at the recorded source version and theorem locator; not a local verification.",
    }[cls]


def allowed_statuses(row: dict) -> set[str]:
    # Capabilities, not a total order: citation and computation never imply proof.
    cls = row["evidence_class"]
    permitted = {"evidence_gap"} if cls == "evidence_gap" else {cls}
    if cls == "comparator":
        permitted.add("lean")
    if cls in ("lean", "comparator") and row.get("conditional"):
        permitted.discard("lean")
        permitted.discard("comparator")
        permitted.add("conditional_lean")
    return permitted


def status_errors(row: dict, tag: str) -> list[str]:
    return [] if tag in allowed_statuses(row) else [
        f"{row['id']}: status {tag!r} exceeds or misstates the bound evidence; "
        f"allowed tags: {', '.join(sorted(allowed_statuses(row)))}"]


def project(read: Callable[[str], bytes], *, source_commit: str = "worktree",
            claims_override: dict | None = None) -> dict:
    inputs = Inputs(read)
    ledger = inputs.data(native.LEDGER)
    resolved = inputs.data(native.EVIDENCE_MAP)
    associations = inputs.data(native.ASSOCIATIONS)
    config = inputs.data(native.CONFIG)
    dependency = inputs.data(INDEX)
    original_claims = inputs.data(CLAIMS)
    claims = original_claims if claims_override is None else claims_override
    if claims != original_claims:
        inputs.cache[CLAIMS] = canonical(claims)
    policy = claims.get(POLICY_KEY) or {}
    if policy and policy.get("schema") != POLICY_SCHEMA:
        raise ValueError("unrecognized claim-evidence policy schema")
    owners = {**OWNERS, **policy.get("owners", {})}
    annotations = inputs.data(policy["nonformal_evidence"]) if policy.get("nonformal_evidence") else {"rows": {}}
    if policy.get("nonformal_evidence") and annotations.get("schema") != "plectis-nonformal-claim-evidence/1":
        raise ValueError("nonformal evidence schema")
    if not isinstance(annotations.get("rows"), dict):
        raise ValueError("nonformal evidence rows must be keyed by claim id")
    rows_by_id = unique_rows(ledger.get("rows"), "id", "coverage")
    paper_by_id = unique_rows(ledger.get("papers"), "paper_id", "papers")
    nodes = unique_rows(dependency.get("nodes"), "handle", "dependency index")
    # The unresolved atlas includes local/private names repeated across modules.
    # It is diagnostic context, never authority for a successful name resolution.
    unresolved: dict[tuple[str, str], set[str]] = {}
    for item in dependency.get("unresolved_atlas_declarations", []):
        unresolved.setdefault((item.get("handle"), item.get("module")), set()).add(
            str(item.get("resolution_status", "unresolved")))
    resolved_papers = unique_rows(resolved.get("papers"), "paper_id", "resolved papers")
    prior = unique_rows([r for p in resolved_papers.values() for r in p.get("results", [])], "id", "resolved evidence")
    gaps = []

    def gap(code: str, owner: str, detail: str, row_id: str | None = None) -> None:
        gaps.append({"code": code, "owner": owners[owner], "detail": detail,
                     "claim_id": row_id, "paper_id": rows_by_id.get(row_id, {}).get("paper_id")})

    for error in propagation.ledger_integrity_failures(ledger):
        gap("ledger_integrity", "inventory", error)
    expected_portfolio = {(p, side) for p in PROBLEM_IDS for side in ("short", "long")}
    actual_portfolio = {(p.get("problem"), p.get("side")) for p in paper_by_id.values()}
    if policy.get("require_sixteen_papers", False) and (actual_portfolio != expected_portfolio or len(paper_by_id) != 16):
        gap("portfolio", "inventory", f"expected all eight short/long pairs; got {sorted(actual_portfolio)}")
    if set(prior) != set(rows_by_id):
        gap("resolved_inventory", "identity", f"missing {sorted(set(rows_by_id)-set(prior))}; orphan {sorted(set(prior)-set(rows_by_id))}")
    if set(resolved_papers) != set(paper_by_id):
        gap("resolved_papers", "identity", "resolved paper inventory differs from coverage")
    for cid in annotations["rows"]:
        if cid not in rows_by_id:
            gap("orphan_nonformal", "nonformal", cid)
    for document, label in ((resolved, "resolved evidence"), (dependency, "dependency index")):
        pin = document.get("lean_pin") or document.get("formal_source", {}).get("ref")
        if pin != ledger.get("lean_pin"):
            gap("formal_pin", "identity", f"{label} pin differs from coverage")
    if claims.get("release", {}).get("formal_source", {}).get("ref") != ledger.get("lean_pin"):
        gap("formal_pin", "identity", "canonical claims formal-source pin differs from coverage")
    if associations.get("corpus_commit") != config.get("corpus_commit") or \
            str(associations.get("run_id")) != str(config.get("replay", {}).get("run_id")):
        gap("comparator_pin", "comparator", "association corpus/run differs from config")
    if resolved.get("corpus_commit") != config.get("corpus_commit"):
        gap("comparator_pin", "comparator", "resolved corpus differs from config")
    currency, texts = propagation.locate_rows(ledger, inputs.text)
    for detail in currency.missing + currency.unrowed:
        gap("paper_inventory", "inventory", detail)
    for cid, source, line in currency.drift:
        gap("line_drift", "inventory", f"{source} moved to {line}; restamp after review", cid)

    parsed: dict[str, native.LeanFile] = {}
    receipts: dict[str, dict] = {}
    output = []
    for cid, raw in rows_by_id.items():
        start_gaps = len(gaps)
        old = prior.get(cid, {})
        if old.get("statement_sha256") != raw.get("statement_sha256"):
            gap("statement_hash", "identity", "resolved prose hash differs from inventory", cid)
        if old.get("source") != raw.get("source"):
            gap("source_locator", "inventory", "resolved source locator differs from inventory", cid)
        if old.get("lean", {}).get("status") != raw.get("lean", {}).get("status"):
            gap("lean_status", "identity", "resolved Lean status differs from inventory", cid)
        if cid not in currency.located:
            gap("statement_missing", "inventory", "current paper does not contain this statement hash", cid)
        declarations = raw.get("lean", {}).get("declarations", [])
        names = [d.get("name") for d in declarations]
        if len(names) != len(set(names)):
            gap("duplicate_declaration", "declaration", "duplicate declaration in claim", cid)
        old_decls = {d["name"]: d for d in old.get("lean", {}).get("declarations", [])}
        if set(old_decls) != set(names):
            gap("resolved_declarations", "identity", "resolved declaration set differs from inventory", cid)
        bindings = []
        for d in declarations:
            name, path = d["name"], d["file"]
            node = nodes.get(name)
            miss = "; ".join(sorted(unresolved.get((name, path), {"absent_from_index"})))
            item = {"name": name, "path": path, "dependency_index_status": "indexed" if node else miss}
            if node is None:
                gap("dependency_index", "index", f"{name}: {miss}; source presence is not loaded-root membership", cid)
            elif node.get("module") != path:
                gap("index_path", "index", f"{name}: index module differs from coverage source", cid)
            try:
                if path not in parsed:
                    parsed[path] = native.LeanFile(inputs.text(path))
                decl = native.lean_declaration(parsed[path], path, name, allow_suffix=False)
                item.update({"line": decl.line, "kind": decl.kind, "module_sha256": digest(inputs.blob(path)),
                             "statement_sha256": digest(decl.normalised.encode())})
                if old_decls.get(name, {}).get("path") != path:
                    gap("resolved_path", "identity", f"{name}: resolved path differs", cid)
                # Non-proposition support is checked by native complete source closure,
                # not by pretending its header is a theorem.
                if decl.kind in native.PROPOSITION_KINDS:
                    expected = old_decls.get(name, {}).get("statement_sha256", "")
                    if item["statement_sha256"].removeprefix("sha256:") != expected.removeprefix("sha256:"):
                        gap("formal_statement_hash", "identity", f"{name}: current statement differs from recorded formal statement", cid)
                else:
                    item["role"] = "support_not_existence_proof"
                    supporting_record = old_decls.get(name, {})
                    item["recorded_support_identity"] = supporting_record.get("support_identity")
                    if supporting_record.get("identity_rule") != native.SUPPORT_SCHEMA:
                        gap("support_identity", "identity", f"{name}: complete native support identity missing", cid)
                    if not any(x.get("kind") in native.PROPOSITION_KINDS for x in old_decls.values()):
                        gap("support_not_proof", "declaration", f"{name}: support alone supplies no proposition proof", cid)
                if node and node.get("line") != decl.line:
                    gap("index_line", "index", f"{name}: index line {node.get('line')} differs from current line {decl.line}", cid)
            except (OSError, ValueError, UnicodeError, native.EvidenceError) as error:
                gap("declaration_missing", "declaration", str(error), cid)
            bindings.append(item)
        recorded_class = "comparator" if raw.get("comparator", {}).get("status") == "compared" else "lean" if declarations else "evidence_gap"
        receipt_paths = []
        if raw.get("comparator", {}).get("status") == "compared":
            old_comparator = old.get("comparator", {})
            old_checks = {v["declaration"]: v for v in old_comparator.get("checks", [])}
            if not declarations or set(old_checks) != set(names):
                gap("comparator_coverage", "comparator", "every declaration needs its own selected check", cid)
            if old_comparator.get("commit") != config.get("corpus_commit") or \
                    str(old_comparator.get("run_id")) != str(config.get("replay", {}).get("run_id")):
                gap("comparator_pin", "comparator", "resolved Comparator row has a different commit or run", cid)
            for name in names:
                assoc = associations.get("declarations", {}).get(name)
                if not isinstance(assoc, dict):
                    gap("association_missing", "comparator", name, cid)
                    continue
                try:
                    entry = assoc["entry"]
                    if not re.fullmatch(r"[A-Za-z0-9_-]+", entry):
                        raise ValueError("unsafe Comparator entry")
                    path = safe_relative(config["replay"]["receipts"] + "/receipt-" + entry + ".json")
                    if path not in receipts:
                        receipts[path] = inputs.data(path)
                    rec = receipts[path]
                    errors = receipt_errors(rec, assoc, config)
                    check = old_checks.get(name, {})
                    if check.get("entry") != entry or check.get("receipt") != path or \
                            check.get("challenge", {}).get("declaration") != assoc.get("challenge"):
                        errors.append("resolved_association")
                    # Native paper_evidence resolves the exact Challenge-named theorem
                    # by scanning the checked Solution closure. The association may name
                    # an implementation module instead. Preserve these different roles;
                    # requiring their paths to be equal produces false alarms.
                    solution = check.get("solution", {})
                    if solution.get("declaration") != assoc.get("challenge") or \
                            solution.get("path") not in rec.get("solution", {}).get("files", {}):
                        errors.append("resolved_solution_identity")
                    target_binding = next(b for b in bindings if b["name"] == name)
                    target_binding["comparator"] = {
                        "receipt": path, "entry": entry, "selected_theorem": assoc["challenge"],
                        "association_solution_path": assoc.get("solution_path"),
                        "resolved_declaring_path": solution.get("path"),
                        "different_path_roles": assoc.get("solution_path") != solution.get("path"),
                        "interpretation": "both_paths_recorded_in_checked_solution_closure; no_local_replay"}

                    if errors:
                        gap("receipt_binding", "comparator", f"{name} / {path}: {', '.join(errors)}", cid)
                    receipt_paths.append(path)
                except (OSError, ValueError, KeyError, UnicodeError) as error:
                    gap("receipt_missing", "comparator", str(error), cid)
        ann = annotations["rows"].get(cid)
        review_info = {}
        if ann:
            cls, review_info, errors = nonformal_class(inputs, ann, raw)
            for error in errors:
                gap("nonformal_binding", "nonformal", error, cid)
            if declarations:
                gap("conflicting_class", "nonformal", "nonformal annotation cannot silently replace formal inventory", cid)
            if not errors and not declarations:
                recorded_class = cls
        elif not declarations:
            gap("nonformal_missing", "nonformal", "no typed statement-bound proof-review, computation or citation record; ledger reason is retained as reported evidence", cid)
        conditional = raw.get("lean", {}).get("status") == "modulo_named_input" or bool(review_info.get("assumptions"))
        row = {
            "id": cid, "paper_id": raw["paper_id"], "problem": raw["problem"], "side": raw["side"],
            "claim_locator": raw["source"] + "#" + str(raw.get("label", "")),
            "statement_hash": raw["statement_sha256"],
            "evidence_class": recorded_class if len(gaps) == start_gaps else "evidence_gap",
            "lean_declaration": names[0] if len(names) == 1 else None,
            "comparator_receipt": next(iter(set(receipt_paths))) if len(set(receipt_paths)) == 1 else None,
            "ordinary_proof_locator": review_info.get("proof"),
            "recorded_evidence_class": recorded_class,
            "binding_status": "bound" if len(gaps) == start_gaps else "gap",
            "conditional": conditional,
            "named_inputs": raw.get("lean", {}).get("named_inputs", []) or review_info.get("assumptions", []),
            "scope": raw.get("lean", {}).get("scope"),
            "reviewer_kind": review_info.get("reviewer_kind"),
            "reported_reason": raw.get("lean", {}).get("reason"),
            "recorded_lean_status": raw.get("lean", {}).get("status"),
            "recorded_comparator_status": raw.get("comparator", {}).get("status"),
            "binding_extension": {"schema": "claim_evidence_bindings/1", "declarations": bindings,
                                  "statement_span": ({"path": currency.located[cid].path,
                                      "start_line": currency.located[cid].line,
                                      "end_line": currency.located[cid].end_line} if cid in currency.located else None),
                                  "comparator_receipts": sorted(set(receipt_paths)), "nonformal": review_info or None},
            "validation": {"local": "structural_join", "lean_compilation": "UNRUN",
                           "comparator_execution": "UNRUN", "historical_corpus_bytes": "not_replayed_here",
                           "prose_correspondence": "authored_mapping_not_semantically_revalidated",
                           "reviewer_identity": "recorded_not_authenticated"},
            "gap_codes": sorted({g["code"] for g in gaps[start_gaps:]}),
        }
        row["status_phrase_required"] = status_phrase(row)
        output.append(row)
    # Explicit status requests are checked against capabilities. Arbitrary natural
    # language is not automatically interpreted or claimed to be semantically safe.
    by_output = {r["id"]: r for r in output}
    status_requests = policy.get("status_assertions", {})
    if not isinstance(status_requests, dict):
        raise ValueError("status_assertions must be keyed by claim id")
    for cid, tags in status_requests.items():
        if cid not in by_output or not isinstance(tags, list) or any(not isinstance(t, str) for t in tags):
            gap("status_request", "status", "unknown claim or malformed status request: " + cid)
            continue
        for tag in tags:
            for error in status_errors(by_output[cid], tag):
                gap("overstatement", "status", error, cid)
    for paper in paper_by_id.values():
        labelled = {r.get("label"): r["id"] for r in rows_by_id.values() if r["paper_id"] == paper["paper_id"]}
        for path in paper["sources"]:
            for label, tag in STATUS_PATTERN.findall(propagation.counter_view(texts.get(path, ""))):
                cid = labelled.get(label)
                if cid is None:
                    gap("unknown_status_label", "status", f"{path}: {label}")
                else:
                    for error in status_errors(by_output[cid], tag):
                        gap("overstatement", "status", error, cid)
    global_failure = any(g["claim_id"] is None for g in gaps)
    bad_ids = {g["claim_id"] for g in gaps}
    for row in output:
        if global_failure or row["id"] in bad_ids:
            row["binding_status"] = "gap"
            row["gap_codes"] = sorted(set(row["gap_codes"]) | {g["code"] for g in gaps if g["claim_id"] == row["id"]})
    coverage = []
    for paper in paper_by_id.values():
        rs = [r for r in output if r["paper_id"] == paper["paper_id"]]
        coverage.append({"paper_id": paper["paper_id"], "problem": paper["problem"], "side": paper["side"],
                         "rows": len(rs), "bound": sum(r["binding_status"] == "bound" for r in rs),
                         "gap_rows": sum(r["binding_status"] == "gap" for r in rs),
                         "recorded_classes": dict(sorted(Counter(r["recorded_evidence_class"] for r in rs).items())),
                         "dependency_gap_rows": sum("dependency_index" in r["gap_codes"] for r in rs)})
    return {"schema": REPORT_SCHEMA, "row_schema": SCHEMA, "source_commit": source_commit,
            "formal_source_commit": ledger.get("lean_pin"), "authority": "structural_binding_of_recorded_evidence_only",
            "scope": "registered_asserting_environments_and_labelled_spans_in_sixteen_problem_papers",
            "not_covered": ["unregistered theorem claims in free prose", "semantic equivalence of prose and Lean",
                            "new kernel or Comparator executions", "authentication of review identities"],
            "passed": not gaps, "rows": output, "coverage": coverage, "gaps": gaps,
            "input_sha256": {p: digest(b) for p, b in sorted(inputs.cache.items())},
            "summary": {"rows": len(output), "papers": len(coverage),
                        "bound": sum(r["binding_status"] == "bound" for r in output),
                        "gap_rows": sum(r["binding_status"] == "gap" for r in output),
                        "gap_findings": len(gaps), "gap_codes": dict(sorted(Counter(g["code"] for g in gaps).items()))}}


def report_errors(report: dict) -> list[str]:
    return [f"{g['claim_id'] or 'portfolio'} [{g['code']}] owner={g['owner']}: {g['detail']}" for g in report["gaps"]]


def coverage_markdown(report: dict) -> str:
    lines = ["# Claim-evidence coverage", "", "Structural checks of recorded evidence; no fresh Lean or Comparator run.",
             "", f"Source: `{report['source_commit']}`. Formal-source pin: `{report['formal_source_commit']}`.", "",
             "| Problem | Side | Results | Bound | Gap rows | Dependency-index gap rows |",
             "|---|---|---:|---:|---:|---:|"]
    for p in report["coverage"]:
        lines.append(f"| {p['problem']} | {p['side']} | {p['rows']} | {p['bound']} | {p['gap_rows']} | {p['dependency_gap_rows']} |")
    lines += ["", "Counts are claim occurrences; short and long occurrences are separate. Gaps can overlap.",
              "Index gaps do not establish that a declaration failed to compile or that its theorem is false.",
              "", "## Gap codes", ""]
    lines += [f"- `{k}`: {v}" for k, v in report["summary"]["gap_codes"].items()]
    return "\n".join(lines) + "\n"


def validate_writer_manifest(manifest: dict, report: dict, read: Callable[[str], bytes]) -> list[str]:
    """Check authored status spans next to each exact registered paper statement.

    Legacy field 'rendered_span' is a SOURCE span, not a PDF observation. This
    checks the controlled writer contract; unannotated prose and TeX rendering
    still require review. A sidecar decoy does not satisfy this contract.
    """
    errors = []
    inputs = Inputs(read)
    try:
        rows = unique_rows(manifest.get("rows"), "claim_id", "writer status manifest")
    except ValueError as e:
        return [str(e)]
    generated = {r["id"]: r for r in report["rows"]}
    if manifest.get("schema") != "claim_evidence_writer/1":
        errors.append("writer manifest schema")
    if manifest.get("require_complete") is not True:
        errors.append("writer admission requires complete registered claim coverage")
    if set(rows) != set(generated):
        errors.append("writer status manifest must cover exactly the registered claim ids")
    for cid, row in rows.items():
        if cid not in generated:
            continue
        claim = generated[cid]
        if row.get("statement_hash") != claim["statement_hash"]:
            errors.append(f"{cid}: stale writer statement hash")
        if row.get("phrase") != claim["status_phrase_required"]:
            errors.append(f"{cid}: rendered status phrase exceeds or differs from allowed phrase")
        try:
            locator = row["rendered_span"]
            statement = claim.get("binding_extension", {}).get("statement_span") or {}
            if locator.get("path") != statement.get("path"):
                errors.append(f"{cid}: status must occur in the claim's actual paper source, not a sidecar")
            last = statement.get("end_line", -1)
            start = locator.get("start_line", -1)
            if type(last) is not int or type(start) is not int or not last < start <= last + 12:
                errors.append(f"{cid}: status must follow the statement within twelve source lines")
            for other in generated.values():
                span = other.get("binding_extension", {}).get("statement_span") or {}
                if other["id"] != cid and span.get("path") == locator.get("path") and \
                        last < span.get("start_line", -1) <= locator.get("end_line", -1):
                    errors.append(f"{cid}: status span crosses the next registered claim")
            text = inputs.span(locator)
            if row.get("phrase") not in text or text.strip() != row.get("phrase"):
                errors.append(f"{cid}: span must contain only the generated status phrase")
        except (OSError, ValueError, KeyError, TypeError, UnicodeError) as e:
            errors.append(f"{cid}: {e}")
        if claim["binding_status"] != "bound":
            errors.append(f"{cid}: evidence gaps block writer admission")
    return errors


def publication_errors(read: Callable[[str], bytes], claims: dict) -> list[str]:
    """Called by the native publication contract against that same reader snapshot."""
    if POLICY_KEY not in claims:
        return []  # old source cuts retain their old contract
    try:
        report = project(read, claims_override=claims)
        errors = report_errors(report)
        stored = json.loads(read(OUTPUT))
        # Commit is a reporting label. Byte fingerprints, rows and gaps are authority.
        for key in ("rows", "coverage", "gaps", "input_sha256", "summary"):
            if stored.get(key) != report[key]:
                errors.append(f"{OUTPUT}: stale {key}; rebuild with paper_evidence.py claim-build")
        writer = claims[POLICY_KEY].get("writer_manifest")
        if writer:
            errors.extend(validate_writer_manifest(json.loads(read(safe_relative(writer))), report, read))
        return errors
    except (OSError, ValueError, KeyError, TypeError, UnicodeError) as e:
        return [f"claim-evidence admission failed closed; owner={OWNERS['identity']}: {e}"]


def cli(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("claim-build", "claim-check", "claim-writer-check"))
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--source-commit", help="read this exact full Git commit instead of the worktree")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--writer-manifest", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.source_commit:
            if not re.fullmatch(r"[0-9a-f]{40}", args.source_commit):
                raise ValueError("--source-commit must be a full lowercase Git commit id")
            from publication_contract import RepositoryReader
            reader = RepositoryReader(args.root, git_ref=args.source_commit)
            read = reader.read_bytes
        else:
            read = root_reader(args.root)
        report = project(read, source_commit=args.source_commit or "worktree")
        errors = report_errors(report)
        if args.command == "claim-build":
            out = args.output or args.root / OUTPUT
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_bytes(canonical(report))
            out.with_suffix(".md").write_text(coverage_markdown(report), encoding="utf-8")
        elif args.command == "claim-writer-check":
            if args.writer_manifest is None:
                parser.error("--writer-manifest is required")
            errors += validate_writer_manifest(json.loads(args.writer_manifest.read_text()), report, read)
        elif args.output:
            args.output.write_bytes(canonical(report))
        print(json.dumps({**report["summary"], "passed": not errors,
                          "command": args.command, "validation": "structural_only"}, sort_keys=True))
        if args.command != "claim-build":
            for error in errors:
                print(error, file=sys.stderr)
        # Building a diagnostic report successfully is different from admitting it.
        return 0 if args.command == "claim-build" else int(bool(errors))
    except (OSError, ValueError, KeyError, TypeError, UnicodeError, native.EvidenceError) as e:
        print(f"claim-evidence failed closed: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(cli(sys.argv[1:]))
