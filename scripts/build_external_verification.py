#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the claim-owned External Verification Packet projections.

The semantic owner is ``docs/claims.json::external_verification_packet``.
Lean remains proof authority.  This builder validates the owner, checks the
statement-isolation boundary, and projects the small Comparator config, the
whole-eight-problem disclosure, and reviewer/outreach surfaces.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS_PATH = ROOT / "docs/claims.json"
PROBLEM_SOURCE_PATH = ROOT / "docs/problem_index_source.json"
PROBLEM_PROJECTION_PATH = ROOT / "docs/problems.json"
OUTPUTS = {
    "config": ROOT / "verification/comparator.json",
    "negative_config": ROOT / "verification/comparator-negative-mismatch.json",
    "formalization": ROOT / "formalization.yaml",
    "packet": ROOT / "docs/external_verification_packet.json",
    "human": ROOT / "docs/EXTERNAL_VERIFICATION.md",
    "outreach": ROOT / "docs/OUTREACH_EVIDENCE_CAPSULES.md",
}

IMPORT_LINE_RE = re.compile(r"^import\s+([^\n]+)$", re.M)


def imports_in_text(text: str) -> list[str]:
    """Return every module token, including multi-module import lines."""
    return [token for body in IMPORT_LINE_RE.findall(text) for token in body.split()]


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_owner() -> tuple[dict, dict, dict, dict]:
    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    packet = claims.get("external_verification_packet")
    if not isinstance(packet, dict):
        raise ValueError("docs/claims.json lacks external_verification_packet")
    if packet.get("scope") != "all_eight_public_problem_programmes":
        raise ValueError("external verification scope must cover all eight programmes")
    source = json.loads(PROBLEM_SOURCE_PATH.read_text(encoding="utf-8"))
    projection = json.loads(PROBLEM_PROJECTION_PATH.read_text(encoding="utf-8"))
    expected_ids = packet.get("problem_ids")
    source_ids = [row.get("problem_id") for row in source.get("problems", [])]
    projection_ids = [row.get("problem_id") for row in projection.get("problems", [])]
    if source_ids != expected_ids or projection_ids != expected_ids:
        raise ValueError("external verification problem_ids must match both canonical problem indexes")
    if source.get("problem_count", len(source_ids)) != 8 or projection.get("problem_count") != 8:
        raise ValueError("canonical problem indexes must cover exactly eight programmes")
    if any(row.get("status") != "open" for row in projection["problems"]):
        raise ValueError("every canonical problem-index row must retain status=open")
    return claims, packet, source, projection


def declaration_exists(source: str, full_name: str) -> bool:
    path = ROOT / source
    short = full_name.rsplit(".", 1)[-1]
    if not path.is_file():
        return False
    text = path.read_text(encoding="utf-8")
    return re.search(
        rf"^\s*(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
        rf"(?:theorem|def|abbrev|structure|class)\s+{re.escape(short)}\b",
        text,
        re.M,
    ) is not None


def module_path(module: str) -> Path | None:
    path = ROOT / (module.replace(".", "/") + ".lean")
    return path if path.is_file() else None


def internal_import_closure(start_module: str) -> list[Path]:
    queue = [start_module]
    seen_modules: set[str] = set()
    paths: list[Path] = []
    while queue:
        module = queue.pop(0)
        if module in seen_modules:
            continue
        seen_modules.add(module)
        path = module_path(module)
        if path is None:
            continue
        paths.append(path)
        for imported in imports_in_text(path.read_text(encoding="utf-8")):
            if module_path(imported) is not None:
                queue.append(imported)
    return sorted(paths)


def validate(packet: dict, problem_source: dict) -> tuple[list[Path], list[str]]:
    errors: list[str] = []
    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))["claims"]
    claim_by_id = {row["id"]: row for row in claims}
    expected_results = [
        "totient_kernel_finite_rank",
        "totient_kernel_infinite_rank",
        "mersenne_achievement_measure_one",
        "erdos_borwein_full_support",
    ]
    if [row.get("id") for row in packet.get("main_results", [])] != expected_results:
        errors.append(f"flagship result set drifted from the exact four-result contract: {expected_results}")
    if {row.get("problem") for row in packet.get("main_results", [])} != {249, 257}:
        errors.append("flagship Comparator results must remain scoped to problems 249 and 257")
    wrapper_sources = {
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
    }
    for result in packet["main_results"]:
        claim = claim_by_id.get(result["claim_id"])
        if claim is None:
            errors.append(f"unknown flagship claim_id: {result['claim_id']}")
            continue
        original = result["original_declaration"]
        source = result["original_source"]
        if not declaration_exists(source, original):
            errors.append(f"missing original declaration {original} in {source}")
        short_original = original.rsplit(".", 1)[-1]
        if not any(d.get("name") == short_original and d.get("module") == source
                   for d in claim.get("declarations", [])):
            errors.append(f"flagship {result['id']} is not owned by claim {result['claim_id']}")
        wrapper = result["wrapper_declaration"]
        for wrapper_source in wrapper_sources:
            if not declaration_exists(wrapper_source, wrapper):
                errors.append(f"missing wrapper {wrapper} in {wrapper_source}")

    for row in problem_source["problems"]:
        required = row.get("required_note_declarations", [])
        if not required:
            errors.append(f"problem {row['erdos_number']} has no required note declarations")
        for declaration in required:
            source = declaration["module"].replace(".", "/") + ".lean"
            full_name = declaration["module"].rsplit(".", 1)[0] + "." + declaration["declaration"]
            if not declaration_exists(source, full_name):
                errors.append(
                    f"problem {row['erdos_number']} required declaration is missing: "
                    f"{full_name} in {source}"
                )

    closure = internal_import_closure(packet["comparator"]["challenge_module"])
    closure_rel = [path.relative_to(ROOT).as_posix() for path in closure]
    expected = [
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Statements.lean",
    ]
    if closure_rel != expected:
        errors.append(f"challenge internal import closure drifted: {closure_rel!r}")
    for path in closure:
        text = path.read_text(encoding="utf-8")
        for imported in imports_in_text(text):
            if imported.startswith("Erdos249257.") or imported.startswith("ErdosProblems."):
                errors.append(f"proof-bearing import leaked into challenge closure: {path}: {imported}")
    workflow = (ROOT / ".github/workflows/lean.yml").read_text(encoding="utf-8")
    for tool, revision in packet["comparator"]["pins"].items():
        if revision not in workflow:
            errors.append(f"workflow does not bind the claim-owned {tool} revision {revision}")
    return closure, errors


def comparator_config(packet: dict) -> dict:
    cmp = packet["comparator"]
    return {
        "challenge_module": cmp["challenge_module"],
        "solution_module": cmp["solution_module"],
        "theorem_names": [row["wrapper_declaration"] for row in packet["main_results"]],
        "permitted_axioms": cmp["permitted_axioms"],
        "enable_nanoda": cmp["enable_nanoda"],
    }


def negative_config(packet: dict) -> dict:
    first = packet["main_results"][0]
    return {
        "challenge_module": packet["comparator"]["challenge_module"],
        "solution_module": "ExternalVerification.NegativeSolution",
        "theorem_names": [first["wrapper_declaration"]],
        "permitted_axioms": packet["comparator"]["permitted_axioms"],
        "enable_nanoda": False,
    }


def quote(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def render_formalization(packet: dict, problem_projection: dict) -> str:
    lines = [
        "# Generated from docs/claims.json::external_verification_packet.",
        "# Refresh: python3 scripts/build_external_verification.py",
        "version: \"v0.3\"",
        "project:",
        "  name: \"Eight open Erdős problems: checked subsidiary mathematics\"",
        "  authors:",
        "    - \"Will Cook\"",
        "  license: \"Apache-2.0\"",
        "  repository: \"https://github.com/wcook04/plectis-lean-erdos249-257\"",
        "sources:",
        "  - title: \"Erdős Problems 68, 243, 249, 251, 257, 269, 1041, and 1049\"",
        "    authors:",
        "      - \"Paul Erdős and collaborators\"",
        "    id: \"https://www.erdosproblems.com/\"",
        "    type: \"open-problem index\"",
        "    license: \"external source; see source site\"",
        "    author_contacted: \"n/a\"",
        "  - title: \"Repository problem notes and cited-source registry\"",
        "    authors:",
        "      - \"Will Cook\"",
        "    id: \"docs/papers/corpus.json\"",
        "    type: \"source registry and mathematical exposition\"",
        "    license: \"CC-BY-4.0\"",
        "    author_contacted: \"n/a\"",
        "status:",
        "  scope: >-",
        "    All eight covered Erdős problems remain open. This repository checks",
        "    subsidiary theorems, formalises selected known results, verifies finite",
        "    instances, and records conditional reductions and method barriers.",
        "  sorry_count: 4",
        "  sorry_in_definitions: 0",
        "  trusted_challenge_sorry_count: 4",
        "  sorry_boundary: \"All four sorries occur only in the statement-isolated Comparator challenge; every listed result declaration and solution wrapper has sorry_count 0.\"",
        "  axioms:",
    ]
    for axiom in packet["comparator"]["permitted_axioms"]:
        lines.append(f"    - {quote(axiom)}")
    lines.append("  main_results:")
    for row in packet["main_results"]:
        lines.extend([
            f"    - declaration: {quote(row['original_declaration'])}",
            f"      file: {quote(row['original_source'])}",
            "      sorry_count: 0",
            "      axioms:",
        ])
        for axiom in packet["comparator"]["permitted_axioms"]:
            lines.append(f"        - {quote(axiom)}")
        lines.extend([
            f"      comparator_config: {quote(packet['comparator']['config'])}",
            "      literature_dependencies: []",
            f"      contribution_class: {quote(row['contribution_class'])}",
            f"      statement: {quote(row['statement'])}",
            f"      boundary: {quote(row['boundary'])}",
            f"      comparator_declaration: {quote(row['wrapper_declaration'])}",
        ])
    lines.extend([
        "automation:",
        "  methods:",
        "    - method: \"agent\"",
        "      models: [\"OpenAI Codex and other disclosed agent systems\"]",
        "      framework: \"agent-assisted Lean formalisation and proof engineering\"",
        "      tool_setup: \"Repository-specific generators, release guards, and focused Lean builds\"",
        "    - method: \"other\"",
        "      framework: \"Pinned Lean kernel and statement-isolated Comparator CI\"",
        "review:",
        "  status: \"self-assessed\"",
        "  reviewers: []",
        f"  notes: {quote(packet['review_status'])}",
        "fidelity:",
        "  divergences: >-",
        "    The checked results are subsidiary results or formalised prior mathematics; none is the open problem statement. Comparator checks formal statement identity and axioms, not informal significance, novelty, or source fidelity.",
        "alignment:",
        "  namespace: \"Erdos249257.ExternalVerification\"",
        "  statements:",
    ])
    for row in packet["main_results"]:
        lines.extend([
            f"    - source: {quote(row['statement'])}",
            f"      lean: {quote(row['original_declaration'])}",
            f"      module: {quote(row['original_source'])}",
            "      status: \"proved\"",
            f"      note: {quote(row['boundary'])}",
        ])
    lines.extend([
        "acknowledgements: \"Michael Rothgang identified contribution clarity and cheap external proof inspection as necessary review surfaces.\"",
        "external_verification:",
        "  owner: \"docs/claims.json::external_verification_packet\"",
        f"  problem_index: {quote(packet['problem_index_projection'])}",
        f"  problem_index_digest: {quote(sha256_path(PROBLEM_PROJECTION_PATH))}",
        f"  problem_count: {problem_projection['problem_count']}",
        "  problems:",
    ])
    for problem in problem_projection["problems"]:
        lines.extend([
            f"    - id: {quote(problem['problem_id'])}",
            f"      erdos_number: {problem['erdos_number']}",
            f"      status: {quote(problem['status'])}",
            f"      checked_frontier: {quote(problem['what_is_checked'][0])}",
            f"      open_frontier: {quote(problem['what_is_not_checked'][0])}",
            f"      claim_registry_status: {quote(problem['claim_registry_status'])}",
        ])
    lines.extend([
        "  trusted_challenge_holes: 4",
        "  packet: \"docs/EXTERNAL_VERIFICATION.md\"",
        "  receipt_contract: \"docs/external_verification_packet.json::receipt_contract\"",
        "",
    ])
    return "\n".join(lines)


def render_human(packet: dict, problem_source: dict, problem_projection: dict) -> str:
    source_by_id = {row["problem_id"]: row for row in problem_source["problems"]}
    rows = []
    for row in problem_projection["problems"]:
        source = source_by_id[row["problem_id"]]
        representative = source["required_note_declarations"][0]
        full_name = representative["module"].rsplit(".", 1)[0] + "." + representative["declaration"]
        rows.append(
            f"| #{row['erdos_number']} | `{full_name}` | "
            f"{row['what_is_checked'][0]} | {row['what_is_not_checked'][0]} |"
        )
    flags = []
    for row in packet["main_results"]:
        flags.append(
            f"- `{row['wrapper_declaration']}` — {row['contribution_class']}: "
            f"{row['statement']} **Boundary:** {row['boundary']}"
        )
    return "\n".join([
        "<!-- Generated by scripts/build_external_verification.py; do not edit. -->",
        "# External Verification Packet",
        "",
        packet["purpose"],
        "",
        "**Scope:** all eight public problem programmes. **Status:** all eight remain open.",
        "The eight-programme rows below are projected from `docs/problems.json`; they are a navigation disclosure, not a promotion of unregistered expansion declarations into reviewed claims.",
        "",
        "| Problem | Representative checked declaration | Checked frontier | Still open |",
        "|---|---|---|---|",
        *rows,
        "",
        "## Statement-isolated Comparator review unit",
        "",
        *flags,
        "",
        "The trusted challenge imports only `ExternalVerification.Statements` and Mathlib.",
        "The proof-bearing modules occur only in `ExternalVerification.Solution`.",
        "CI runs the pinned real Linux sandbox and uploads a commit-bound JSON receipt.",
        "",
        "Use the precise phrase **Comparator-checked against a separately declared statement and axiom budget** only when the receipt for the displayed commit is green. Do not replace it with “independently verified”.",
        "",
        f"Review posture: {packet['review_status']}.",
        "",
    ])


def render_outreach(packet: dict) -> str:
    return "\n".join([
        "<!-- Generated by scripts/build_external_verification.py; do not edit. -->",
        "# Outreach evidence capsules",
        "",
        "These are reusable evidence paragraphs only. Openings, mathematical motivation, and questions must remain recipient-specific and written in Will's own words.",
        "",
        "## Post-green generic capsule",
        "",
        "> To make the formal part easy to inspect, the repository includes a root `formalization.yaml` recording its provenance, automation, current review status, and the checked frontier for all eight covered problems. A small Comparator packet checks the theorem named above against a separately declared statement and axiom budget, then Lean's kernel checks the submitted proof. The attached CI receipt is bound to the repository commit. It does not claim that any of the eight Erdős problems is solved.",
        "",
        "## #249 boundary capsule",
        "",
        "> The checked result is the exact rank `2^e+1` of the dyadic totient kernel through level `e`, together with infinite-dimensionality of the full kernel. Comparator checks those statements and their axiom budget. The missing step is still a rationality-to-finite-rank or unbounded-certificate bridge; Erdős #249 remains open.",
        "",
        "## #257 boundary capsule",
        "",
        "> The checked result is the measure-one geometry of the Mersenne achievement set, plus a separate formalisation of the classical full-support Erdős–Borwein irrationality theorem. Comparator checks those statements and their axiom budget. Universal Erdős #257, including the rational targets `1/2` and `1/21`, remains open.",
        "",
    ])


def render_packet(
    packet: dict,
    problem_source: dict,
    problem_projection: dict,
    closure: list[Path],
    config_bytes: bytes,
) -> str:
    result = json.loads(json.dumps(packet))
    result["authority_posture"] = "generated_projection_not_proof_or_claim_authority"
    result["source_owner"] = "docs/claims.json::external_verification_packet"
    result["problem_index"] = {
        "owner": packet["problem_index_owner"],
        "owner_digest": sha256_path(PROBLEM_SOURCE_PATH),
        "projection": packet["problem_index_projection"],
        "projection_digest": sha256_path(PROBLEM_PROJECTION_PATH),
        "schema": problem_projection["schema"],
        "problem_count": problem_projection["problem_count"],
        "authority_posture": problem_projection["authority_posture"],
        "problems": problem_projection["problems"],
    }
    result["challenge_import_closure"] = {
        "internal_paths": [path.relative_to(ROOT).as_posix() for path in closure],
        "digest": sha256_bytes(
            b"".join(
                path.relative_to(ROOT).as_posix().encode() + b"\0" + path.read_bytes() + b"\0"
                for path in closure
            )
        ),
        "proof_bearing_internal_import_count": 0,
    }
    result["trusted_build_inputs"] = {
        path: sha256_path(ROOT / path)
        for path in ("lakefile.toml", "lean-toolchain", "lake-manifest.json")
    }
    result["config_digest"] = sha256_bytes(config_bytes)
    result["solution_source_digest"] = sha256_path(ROOT / "ExternalVerification/Solution.lean")
    return json.dumps(result, indent=2, ensure_ascii=False) + "\n"


def build_outputs(
    packet: dict, problem_source: dict, problem_projection: dict, closure: list[Path]
) -> dict[Path, bytes]:
    config_bytes = (json.dumps(comparator_config(packet), indent=2) + "\n").encode()
    negative_bytes = (json.dumps(negative_config(packet), indent=2) + "\n").encode()
    return {
        OUTPUTS["config"]: config_bytes,
        OUTPUTS["negative_config"]: negative_bytes,
        OUTPUTS["formalization"]: render_formalization(packet, problem_projection).encode(),
        OUTPUTS["packet"]: render_packet(
            packet, problem_source, problem_projection, closure, config_bytes
        ).encode(),
        OUTPUTS["human"]: render_human(packet, problem_source, problem_projection).encode(),
        OUTPUTS["outreach"]: render_outreach(packet).encode(),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    _, packet, problem_source, problem_projection = load_owner()
    closure, errors = validate(packet, problem_source)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    outputs = build_outputs(packet, problem_source, problem_projection, closure)
    stale: list[str] = []
    for path, content in outputs.items():
        if args.check:
            if not path.is_file() or path.read_bytes() != content:
                stale.append(path.relative_to(ROOT).as_posix())
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
            print(path.relative_to(ROOT).as_posix())
    if stale:
        print("stale external-verification projections: " + ", ".join(stale), file=sys.stderr)
        return 1
    if args.check:
        print("external-verification projections are current and challenge isolation is intact")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
