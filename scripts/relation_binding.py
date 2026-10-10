#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Replay the exact context/endpoints of authored relation rows against Lean.

The atlas owner checks declaration identity and the type head. This adapter
adds a DIFFERENT obligation: the actual predicate arguments in the JSON must
elaborate to a type inhabited by the cited certificate. Emit is read-only apart
from its explicit output directory. Replay invokes the existing kernel-probe
owner, in a maintainer-provisioned environment. It is NOT a sandbox for untrusted
Lean, a clean-build receipt, or a release authorization.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tempfile
from pathlib import Path
from typing import Any

import relation_registry as registry
import research_decision as decision
import run_kernel_probes as probes

HEADS = {
    "equivalent": "Equivalent", "endpoint_route": "EndpointRoute",
    "slot_replacement": "SlotReplacement", "strictly_stronger": "StrictlyStronger",
    "separates": "Separates", "refuted": "Refuted", "feasible": "Feasible", "supplied": "Supplied",
}
UNARY = {"refuted", "feasible", "supplied"}
# Explicit rendering adapters for the supplied registry. These are syntax
# choices, not evidence: Lean must still check the emitted full predicates.
BINDERS = {"off_switch_region_feasible": "v"}
OPENS = [
    "ErdosProblems.ArgumentGraph.Contracts",
    "ErdosProblems.ArgumentGraph.RelationCertificates",
    "ErdosProblems.Erdos1049", "ErdosProblems.Erdos1049.PaperR7",
    "ErdosProblems.Erdos1049.PaperR10", "ErdosProblems.Erdos1049.PaperR11",
    "ErdosProblems.Erdos1049.PaperCompleteR21",
    "ErdosProblems.Erdos1041.PaperCompleteR21",
    "ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord",
]
NAMESPACE = "PlectisRelationBinding"
BINDING_INPUTS = {"scripts/relation_binding.py", "scripts/run_kernel_probes.py"}


def _binding_inputs(root: Path) -> set[str]:
    return decision._integrity_inputs(root) | BINDING_INPUTS


def _single_expression(text: Any) -> str:
    if not isinstance(text, str) or not text.strip():
        raise decision.DecisionError("relation expression must be nonempty text")
    if any(x in text for x in ("\n", "\r", "--", "/-", "-/", ":=", ";")):
        raise decision.DecisionError("unsupported relation rendering; review and write an explicit Lean probe")
    return text.strip()


def predicate_parts(row: dict[str, Any]) -> tuple[str, str, str, str | None]:
    context = _single_expression(row["context"])
    # The one annotated context in the supplied registry is `Alias: fun ...`.
    # Use the full lambda, NOT the alias, so changing the stated guard changes
    # the type that the kernel must check.
    if not context.startswith("fun ") and ": fun " in context:
        alias, context = context.split(": ", 1)
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", alias):
            raise decision.DecisionError("invalid annotated context")
    match = re.fullmatch(r"fun\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(.+?)\s*=>\s*(.+)", context)
    if not match:
        raise decision.DecisionError("context requires an explicit typed lambda; no guessed scope")
    binder = BINDERS.get(row["id"], match[1])
    left = _single_expression(row["left"])
    right = None if row["relation"] in UNARY else _single_expression(row["right"])
    return context, binder, left, right


def emit(root: Path) -> tuple[str, dict[str, Any]]:
    root = Path(root).resolve()
    paths = _binding_inputs(root)
    stamp = decision.snapshot(root, paths)
    report = registry.check(root)
    if not report["ok"]:
        raise decision.DecisionError("relation registry rejected: " + "; ".join(report["errors"][:5]))
    rows = registry.load_registry(root)["rows"]
    if not rows:
        raise decision.DecisionError("refuse an empty binding probe")
    imports = sorted({registry.module_id(r["certificate"]["module"]) for r in rows})
    lines = ["-- Generated from exact relation-row predicates. No new mathematical claim."]
    lines += ["import " + m for m in imports]
    lines += ["", "set_option autoImplicit false", "noncomputable section"]
    lines += ["open " + name for name in OPENS]
    lines += ["", f"namespace {NAMESPACE}"]
    expected = []
    for index, row in enumerate(rows):
        relation = row["relation"]
        if relation not in HEADS:
            raise decision.DecisionError(f"unsupported relation kind: {relation}")
        context, binder, left, right = predicate_parts(row)
        target = f"{HEADS[relation]} ({context}) (fun {binder} => {left})"
        if right is not None:
            target += f" (fun {binder} => {right})"
        cert = row["certificate"]["declaration"]
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", cert):
            raise decision.DecisionError("certificate must be a declaration name")
        name = f"binding_{index}"
        lines += [f"", f"-- row-sha256: {decision.digest(row)}", f"theorem {name} :",
                  f"    {target} :=", f"  {cert}", f"#print axioms {name}"]
        expected.append({"row_id": row["id"], "row_sha256": decision.digest(row),
                         "declaration": f"{NAMESPACE}.{name}", "expected_type": target,
                         "certificate": cert})
    lines += ["", f"end {NAMESPACE}", ""]
    source = "\n".join(lines)
    decision.verify_snapshot(root, stamp)
    if paths != _binding_inputs(root):
        raise decision.DecisionError("binding source inventory changed")
    manifest = {"schema": "plectis-relation-bindings/1", "snapshot": stamp,
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "obligations": expected,
                "state": "generated_not_compiled",
                "boundary": "exact predicate obligations; no acceptance from a filename/hash alone"}
    return source, manifest


def checked_result(root: Path, source: str, manifest: dict[str, Any], result: dict[str, Any]) -> dict[str, Any]:
    """Called ONLY with the result of the local native runner, not a return's JSON.

    Digest/shape checks are not authentication. Imported .olean provenance is
    the existing source-bound build lane's responsibility, not this adapter's.
    """
    decision.verify_snapshot(root, manifest["snapshot"])
    if set(manifest["snapshot"]["files"]) != _binding_inputs(Path(root).resolve()):
        raise decision.DecisionError("binding source inventory changed")
    wanted = {r["declaration"] for r in manifest["obligations"]}
    source_sha = hashlib.sha256(source.encode()).hexdigest()
    reasons = []
    if source_sha != manifest["source_sha256"] or result.get("source_sha256") != source_sha:
        reasons.append("probe identity mismatch")
    if result.get("accepted") is not True:
        reasons.append("native kernel-probe owner did not accept")
    if not wanted.issubset(result.get("axioms_printed", {})):
        reasons.append("missing per-binding axiom output")
    for name in wanted:
        if set(result.get("axioms_printed", {}).get(name, [])) - probes.STANDARD_AXIOMS:
            reasons.append(f"nonstandard axiom in {name}")
    return {"schema": "plectis-relation-binding-result/1",
            "state": "rejected" if reasons else "binding_in_invoked_environment",
            "errors": reasons, "manifest": manifest, "probe_result": result,
            "release_authorization": False, "environment_replayed": False,
            "boundary": "requires source-bound build and independent intended-meaning review before release"}


def replay(root: Path, timeout: int = 1800) -> dict[str, Any]:
    root = Path(root).resolve()
    source, manifest = emit(root)
    # A temporary probe inside the checkout satisfies the existing runner's
    # relative-path contract; it is removed even when Lean fails or times out.
    parent = root / "research" / "probes"
    parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="relation-binding-", dir=parent) as temp:
        path = Path(temp) / "RelationBindings.lean"
        path.write_text(source, encoding="utf-8")
        result = probes.run_probe(path, timeout, root=root)
    result.pop("_output", None)
    return checked_result(root, source, manifest, result)


def return_gate(root: Path, capsule: dict[str, Any], candidate: dict[str, Any]) -> dict[str, Any]:
    """Conservative triage. It never certifies novelty or admits a theorem.

    A new proof of an already registered OPEN statement must not be discarded
    as a duplicate merely because its statement is known.
    """
    decision.check_decision(root, capsule)
    if not isinstance(candidate, dict):
        raise decision.DecisionError("candidate must be a JSON object")
    kind = candidate.get("contribution")
    if not isinstance(kind, str) or kind not in {"new_statement", "new_proof", "representation_gain", "transfer_evidence"}:
        raise decision.DecisionError("candidate needs an explicit contribution kind")
    statement = candidate.get("statement")
    if not isinstance(statement, str) or not statement.strip():
        raise decision.DecisionError("candidate needs a statement")
    normalized = " ".join(statement.split())
    matches = [r for r in capsule["claims"] if " ".join(r.get("statement", "").split()) == normalized]
    if matches and kind == "new_statement":
        disposition = "registered_text_not_a_new_statement"
    elif matches and kind == "new_proof":
        disposition = "proof_of_registered_statement_requires_verification"
    elif kind in {"representation_gain", "transfer_evidence"}:
        disposition = "requires_fixed_baseline_and_consumer_test"
    else:
        disposition = "not_matched_in_selected_claims_unknown"
    return {"schema": "plectis-research-return-triage/1", "disposition": disposition,
            "matching_claims": [{"id": r["id"], "status": r["status"]} for r in matches],
            "decision_sha256": capsule["decision_sha256"],
            "required_contrasts": capsule["contrasts"],
            "publication_admitted": False, "novelty": "not_established",
            "relation_test": "exact scoped implication/converse/refutation probes remain required",
            "literature": "external source comparison remains required"}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    sub = p.add_subparsers(dest="command", required=True)
    e = sub.add_parser("emit"); e.add_argument("--out", type=Path, required=True)
    r = sub.add_parser("replay"); r.add_argument("--timeout", type=int, default=1800)
    g = sub.add_parser("gate"); g.add_argument("--decision", type=Path, required=True)
    g.add_argument("--candidate", type=Path, required=True)
    args = p.parse_args()
    try:
        if args.command == "emit":
            source, manifest = emit(args.root)
            args.out.mkdir(parents=True, exist_ok=True)
            (args.out / "RelationBindings.lean").write_text(source, encoding="utf-8")
            (args.out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
            print(json.dumps({"state": manifest["state"], "obligations": len(manifest["obligations"])}))
            return 0
        result = replay(args.root, args.timeout) if args.command == "replay" else return_gate(
            args.root, json.loads(args.decision.read_text()), json.loads(args.candidate.read_text()))
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 2 if result.get("state") == "rejected" else 0
    except (ValueError, OSError, KeyError) as exc:
        print(f"relation_binding: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
