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
PRIOR_RESULT_RE = re.compile(r"formalisation|known geometry", re.I)


def canonical_claim_status(result: dict) -> str:
    """Keep Comparator selection distinct from canonical claim registration."""
    return (
        f"supports_registered_claim_family:{result['claim_id']}"
        if result.get("claim_id")
        else "comparator_interface_not_registered_as_canonical_claim"
    )


def source_fidelity(packet: dict, row_id: str) -> dict | None:
    mapping = packet.get("source_fidelity", {}).get(row_id)
    return mapping if isinstance(mapping, dict) else None


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
    expected_problems = {68, 243, 249, 251, 257, 269, 1041, 1049}
    results = packet.get("main_results", [])
    if len(results) < len(expected_problems):
        errors.append("Comparator must expose at least one exact interface for every problem")
    if {row.get("problem") for row in results} != expected_problems:
        errors.append("Comparator result coverage must equal the eight-problem portfolio")
    matrix_by_problem = {
        row["problem"]: {family["id"]: family for family in row.get("families", [])}
        for row in packet.get("review_matrix", [])
    }
    if set(matrix_by_problem) != expected_problems:
        errors.append("review_matrix coverage must equal the eight-problem portfolio")
    wrapper_sources = {
        "ExternalVerification/Challenge.lean",
        "ExternalVerification/Solution.lean",
    }
    for result in results:
        family = matrix_by_problem.get(result["problem"], {}).get(result.get("review_family"))
        if family is None:
            errors.append(f"Comparator result {result['id']} lacks a review_matrix family owner")
        if "original theoretical result" in result.get("contribution_class", "").lower():
            errors.append(
                f"result {result['id']} infers originality from local proof provenance"
            )
        if PRIOR_RESULT_RE.search(result.get("contribution_class", "")):
            mapping = source_fidelity(packet, result["id"]) or source_fidelity(
                packet, result.get("review_family", "")
            )
            if not mapping or not mapping.get("source_statement") or not mapping.get("mapping"):
                errors.append(f"prior-result interface {result['id']} lacks source fidelity")
        claim_id = result.get("claim_id")
        claim = claim_by_id.get(claim_id) if claim_id else None
        if claim_id and claim is None:
            errors.append(f"unknown claim_id: {claim_id}")
        original = result["original_declaration"]
        source = result["original_source"]
        if not declaration_exists(source, original):
            errors.append(f"missing original declaration {original} in {source}")
        short_original = original.rsplit(".", 1)[-1]
        if claim is not None and not any(
            d.get("name") == short_original and d.get("module") == source
            for d in claim.get("declarations", [])
        ):
            errors.append(f"result {result['id']} is not owned by claim {claim_id}")
        wrapper = result["wrapper_declaration"]
        for wrapper_source in wrapper_sources:
            if not declaration_exists(wrapper_source, wrapper):
                errors.append(f"missing wrapper {wrapper} in {wrapper_source}")

    for problem, families in matrix_by_problem.items():
        for family_id, family in families.items():
            contribution_class = family.get("contribution_class", "")
            if "original theoretical result" in contribution_class.lower():
                errors.append(
                    f"family {problem}/{family_id} infers originality from local proof provenance"
                )
            if PRIOR_RESULT_RE.search(contribution_class):
                mapping = source_fidelity(packet, family_id)
                if not mapping or not mapping.get("source_statement") or not mapping.get("mapping"):
                    errors.append(f"prior-result family {problem}/{family_id} lacks source fidelity")

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
    fixture = next(
        row for row in packet["main_results"]
        if row["id"] == "totient_kernel_finite_rank"
    )
    return {
        "challenge_module": packet["comparator"]["challenge_module"],
        "solution_module": "ExternalVerification.NegativeSolution",
        "theorem_names": [fixture["wrapper_declaration"]],
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
        "  proof_corpus_sorry_count: 0",
        "  sorry_count: 1",
        "  sorry_in_definitions: 0",
        "  trusted_challenge_sorry_count: 1",
        "  sorry_boundary: \"The only sorry is the trusted proposition package in the statement-isolated Comparator challenge. It is the fixture against which Comparator checks the proof-bearing solution; the proof corpus and every solution wrapper have sorry_count 0.\"",
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
            f"      canonical_claim_status: {quote(canonical_claim_status(row))}",
            "      local_proof_provenance: \"proved_in_this_repository\"",
            "      novelty_status: \"unassessed_no_priority_claim\"",
            f"      contribution_class: {quote(row['contribution_class'])}",
            f"      statement: {quote(row['statement'])}",
            f"      boundary: {quote(row['boundary'])}",
            f"      comparator_declaration: {quote(row['wrapper_declaration'])}",
        ])
        fidelity = source_fidelity(packet, row["id"]) or source_fidelity(
            packet, row.get("review_family", "")
        )
        lines.append("      literature_dependencies:")
        if fidelity:
            for reference in fidelity.get("references", []):
                lines.append(f"        - {quote(reference)}")
            lines.extend([
                f"      source_statement: {quote(fidelity['source_statement'])}",
                f"      source_mapping: {quote(fidelity['mapping'])}",
                f"      historical_attribution: {quote(fidelity['historical_attribution'])}",
                f"      logical_dependency: {quote(fidelity['logical_dependency'])}",
            ])
        else:
            lines[-1] = "      literature_dependencies: []"
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
    lines.append("claim_review_matrix:")
    for problem in packet["review_matrix"]:
        lines.append(f"  - problem: {problem['problem']}")
        lines.append(f"    paper: {quote(problem['paper'])}")
        lines.append("    families:")
        for family in problem["families"]:
            lines.extend([
                f"      - id: {quote(family['id'])}",
                f"        contribution_class: {quote(family['contribution_class'])}",
                f"        evidence_mode: {quote(family['evidence_mode'])}",
                f"        comparator_disposition: {quote(family['comparator_disposition'])}",
                f"        summary: {quote(family['summary'])}",
                f"        boundary: {quote(family['boundary'])}",
            ])
            fidelity = source_fidelity(packet, family["id"])
            if fidelity:
                lines.extend([
                    f"        source_statement: {quote(fidelity['source_statement'])}",
                    f"        source_mapping: {quote(fidelity['mapping'])}",
                    f"        historical_attribution: {quote(fidelity['historical_attribution'])}",
                    f"        logical_dependency: {quote(fidelity['logical_dependency'])}",
                ])
    lines.extend([
        "acknowledgements: null",
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
        "  trusted_challenge_holes: 1",
        "  packet: \"docs/EXTERNAL_VERIFICATION.md\"",
        "  receipt_contract: \"docs/external_verification_packet.json::receipt_contract\"",
        "",
    ])
    return "\n".join(lines)


def _md_breakable_code(name: str) -> str:
    """Render a long Lean path so GitHub can wrap it instead of overflowing."""
    # GitHub strips most CSS, but <wbr> inside <code> is kept and wraps at dots.
    escaped = (
        name.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
    )
    return (
        "<code>"
        + escaped.replace(".", ".<wbr>").replace("_", "_<wbr>")
        + "</code>"
    )


def render_human(packet: dict, problem_source: dict, problem_projection: dict) -> str:
    source_by_id = {row["problem_id"]: row for row in problem_source["problems"]}
    programme_blocks: list[str] = []
    for row in problem_projection["problems"]:
        source = source_by_id[row["problem_id"]]
        representative = source["required_note_declarations"][0]
        full_name = representative["module"].rsplit(".", 1)[0] + "." + representative["declaration"]
        programme_blocks.extend(
            [
                f"### #{row['erdos_number']}",
                "",
                f"- **Representative checked declaration:** {_md_breakable_code(full_name)}",
                f"- **Checked frontier:** {row['what_is_checked'][0]}",
                f"- **Still open:** {row['what_is_not_checked'][0]}",
                "",
            ]
        )
    flags = []
    for row in packet["main_results"]:
        status = canonical_claim_status(row)
        flags.append(
            f"- {_md_breakable_code(row['wrapper_declaration'])} — {row['contribution_class']}: "
            f"{row['statement']} **Canonical claim status:** `{status}`. "
            f"**Novelty:** unassessed; no priority claim. **Boundary:** {row['boundary']}"
        )
    family_blocks: list[str] = []
    for problem in packet["review_matrix"]:
        family_blocks.extend([f"### #{problem['problem']}", ""])
        for family in problem["families"]:
            family_blocks.extend(
                [
                    f"#### `{family['id']}`",
                    "",
                    f"- **Contribution class:** {family['contribution_class']}",
                    f"- **What is contributed:** {family['summary']}",
                    f"- **Evidence:** {family['evidence_mode']}",
                    f"- **Comparator disposition:** `{family['comparator_disposition']}`",
                    f"- **Boundary:** {family['boundary']}",
                    "",
                ]
            )
    return "\n".join([
        "<!-- Generated by scripts/build_external_verification.py; do not edit. -->",
        "# External Verification Packet",
        "",
        "**Scope:** all eight public problem programmes. **Status:** all eight remain open.",
        "The eight-programme rows below are projected from `docs/problems.json`; they are a navigation disclosure, not a promotion of unregistered expansion declarations into reviewed claims.",
        "",
        "## Programme disclosure",
        "",
        *programme_blocks,
        "## Contribution and evidence matrix",
        "",
        "Every substantial contribution family is listed here. Comparator is used only for exact Lean-owned propositions that can be isolated without importing their proofs; paper deductions, cited theorems, and external computations retain their own evidence classes.",
        "",
        *family_blocks,
        "## Nineteen statement-isolated Comparator interfaces",
        "",
        *flags,
        "",
        "The `main_results` key in `formalization.yaml` is the format's list of selected executable interfaces. It is not the canonical claim registry and does not make an unregistered declaration a principal result.",
        "The nineteen exact interfaces cover all eight programmes. Local proof provenance is recorded separately from novelty, which remains unassessed unless a source-fidelity row says otherwise. The trusted challenge contains one proposition-package fixture and imports only `ExternalVerification.Statements` and Mathlib.",
        "The proof-bearing modules occur only in `ExternalVerification.Solution`.",
        "CI runs the pinned real Linux sandbox and uploads a commit-bound JSON receipt.",
        "For a reviewer-run Linux check and the immutable release-asset contract, see `docs/EXTERNAL_VERIFICATION_REPLAY.md`.",
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
    for row in result["main_results"]:
        row["canonical_claim_status"] = canonical_claim_status(row)
        row["local_proof_provenance"] = "proved_in_this_repository"
        row["novelty_status"] = "unassessed_no_priority_claim"
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
