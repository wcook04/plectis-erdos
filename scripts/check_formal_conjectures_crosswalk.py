#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the pinned Formal Conjectures crosswalk and its human projection.

The authored JSON records statement-level comparisons only.  It deliberately
does not turn syntactic similarity, a source hash, or a possible proof adapter
into a semantic-equivalence or contribution-readiness claim.

The default check is offline and validates the pinned identity, controlled
vocabulary, local question ownership, adapter boundary, and generated Markdown.
Pass ``--upstream-checkout`` to additionally hash and inspect an exact checkout
of google-deepmind/formal-conjectures at the recorded commit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
CROSSWALK_PATH = ROOT / "docs" / "formal_conjectures_crosswalk.json"
PROJECTION_PATH = ROOT / "docs" / "FORMAL_CONJECTURES_CROSSWALK.md"
PROBLEM_INDEX_PATH = ROOT / "docs" / "problem_index_source.json"

SCHEMA = "formal-conjectures-crosswalk/1"
UPSTREAM_REPOSITORY = "https://github.com/google-deepmind/formal-conjectures"
UPSTREAM_COMMIT = "37993ec3ed2163822e02bb32eef0fc8c9a9dc7b8"
EXPECTED_PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)
ADAPTER_CANDIDATES = {257, 1049}
NOT_READY = "not_ready_to_submit"
REQUIRED_COMPARISON_AXES = {
    "statement_scope",
    "indexing",
    "casts_and_ambient_types",
    "answer_and_proof_status",
    "conservative_verdict",
    "machine_checked_equivalence",
}

EXPECTED_UPSTREAM: dict[int, dict[str, Any]] = {
    68: {
        "path": "FormalConjectures/ErdosProblems/68.lean",
        "sha256": "ae87fc60cac529122b9a08cbae11df1c98889461372368a3a1b508b84bff11aa",
        "primary_declaration": "Erdos68.erdos_68",
        "declaration_line": 33,
    },
    243: {
        "path": "FormalConjectures/ErdosProblems/243.lean",
        "sha256": "c9689f42fe49827990e61113996e89a14ebbca502095b6334cb4be8e9d9f8117",
        "primary_declaration": "Erdos243.erdos_243",
        "declaration_line": 38,
    },
    249: {
        "path": "FormalConjectures/ErdosProblems/249.lean",
        "sha256": "f7f24be33d689fff45c8ecbb6d3ed026eea9e770db87f3c108f5b5ff0c2c5943",
        "primary_declaration": "Erdos249.erdos_249",
        "declaration_line": 35,
    },
    251: {
        "path": "FormalConjectures/ErdosProblems/251.lean",
        "sha256": "d2ab131b7662a7ea25717dc65ca227be0927c63d954c74c5d43680194d633184",
        "primary_declaration": "Erdos251.erdos_251",
        "declaration_line": 31,
    },
    257: {
        "path": "FormalConjectures/ErdosProblems/257.lean",
        "sha256": "bde5d5e3940b45ad4ca53b706f9fb6cf1a5636650c8fbc218904e43c3c35c66c",
        "primary_declaration": "Erdos257.erdos_257",
        "declaration_line": 35,
    },
    269: {
        "path": "FormalConjectures/ErdosProblems/269.lean",
        "sha256": "7816216886e47aca258974227a526165a2d99e4e6491cdf700b692292ebe45af",
        "primary_declaration": "Erdos269.erdos_269.variants.irrational",
        "declaration_line": 73,
    },
    1041: {
        "path": "FormalConjectures/ErdosProblems/1041.lean",
        "sha256": "368e0cf749e5b0e50ea300f215199375c4f79b8bf325d3fb7877e48f2d9628ca",
        "primary_declaration": "Erdos1041.erdos_1041",
        "declaration_line": 67,
    },
    1049: {
        "path": "FormalConjectures/ErdosProblems/1049.lean",
        "sha256": "f2eb2ab5016f7c37ef9d9000c066362296dfafe11786b6bec9b2d1b96bf5222c",
        "primary_declaration": "Erdos1049.erdos_1049",
        "declaration_line": 40,
    },
}

EXPECTED_ADAPTER_TARGETS = {
    257: "Erdos257.erdos_257.variants.tsum_top",
    1049: "Erdos1049.erdos_1049.variants.geq_2_integer",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_token(full_name: str) -> str:
    """Return the source token after the enclosing namespace."""
    parts = full_name.split(".")
    return ".".join(parts[1:]) if len(parts) > 1 else full_name


def declaration_line_error(
    lines: list[str], name: str, line_number: int, label: str
) -> str | None:
    if line_number < 1 or line_number > len(lines):
        return f"{label}: declaration line {line_number} is outside the source"
    token = declaration_token(name)
    line = lines[line_number - 1]
    if re.search(rf"\b(?:theorem|lemma|def|abbrev)\s+{re.escape(token)}\b", line):
        return None
    return f"{label}: line {line_number} does not declare {name}"


def local_evidence_errors(evidence: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    path = ROOT / str(evidence.get("path", ""))
    label = str(evidence.get("path", "<missing path>"))
    if not path.is_file():
        return [f"adapter evidence path is missing: {label}"]
    lines = path.read_text(encoding="utf-8").splitlines()
    name = str(evidence.get("declaration", ""))
    line_number = evidence.get("line")
    if not isinstance(line_number, int):
        return [f"{label}: adapter evidence line is not an integer"]
    error = declaration_line_error(lines, name, line_number, label)
    if error:
        errors.append(error)
    return errors


def crosswalk_errors(
    manifest: dict[str, Any],
    problem_index: dict[str, Any],
    projection_text: str | None,
) -> list[str]:
    """Return offline contract and projection failures."""
    errors: list[str] = []
    if manifest.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA}")

    upstream = manifest.get("upstream", {})
    if upstream.get("repository") != UPSTREAM_REPOSITORY:
        errors.append("upstream repository identity drifted")
    if upstream.get("commit") != UPSTREAM_COMMIT:
        errors.append("upstream commit pin drifted")
    if upstream.get("license") != "Apache-2.0":
        errors.append("upstream license identity drifted")

    policy = manifest.get("policy", {})
    if policy.get("adapter_candidate_problems") != [257, 1049]:
        errors.append("adapter candidate list must be exactly [257, 1049]")
    if policy.get("human_semantic_review_required") is not True:
        errors.append("policy must require human semantic review")
    if policy.get("automated_submission_readiness") is not False:
        errors.append("automated submission readiness must remain false")
    if policy.get("only_submission_status") != NOT_READY:
        errors.append(f"only submission status must be {NOT_READY}")

    indexed = {
        row.get("erdos_number"): row for row in problem_index.get("problems", [])
    }
    rows = manifest.get("problems", [])
    observed = tuple(row.get("problem") for row in rows)
    if observed != EXPECTED_PROBLEMS:
        errors.append(
            "problem order and coverage must be exactly "
            + ", ".join(map(str, EXPECTED_PROBLEMS))
        )

    for row in rows:
        problem = row.get("problem")
        label = f"problem {problem}"
        if problem not in EXPECTED_UPSTREAM:
            errors.append(f"{label}: unexpected problem")
            continue

        local = indexed.get(problem)
        if local is None:
            errors.append(f"{label}: missing from local problem index")
        else:
            if row.get("local_problem_id") != local.get("problem_id"):
                errors.append(f"{label}: local problem id drifted")
            if local.get("status") != "open":
                errors.append(f"{label}: local problem must remain open")
            if not str(local.get("question", "")).strip():
                errors.append(f"{label}: local question is empty")

        source = row.get("upstream_source", {})
        expected = EXPECTED_UPSTREAM[problem]
        for key, value in expected.items():
            if source.get(key) != value:
                errors.append(f"{label}: upstream {key} drifted")
        if source.get("proof_status") != "sorry":
            errors.append(f"{label}: primary upstream proof status must be sorry")
        anchors = source.get("signature_anchors", [])
        if not isinstance(anchors, list) or not anchors or not all(
            isinstance(anchor, str) and anchor.strip() for anchor in anchors
        ):
            errors.append(f"{label}: signature anchors must be nonempty strings")

        comparison = row.get("comparison", {})
        if not REQUIRED_COMPARISON_AXES.issubset(comparison):
            missing = sorted(REQUIRED_COMPARISON_AXES - set(comparison))
            errors.append(f"{label}: missing comparison axes: {', '.join(missing)}")
        if comparison.get("machine_checked_equivalence") != "none":
            errors.append(f"{label}: crosswalk must not claim checked equivalence")
        expected_verdict = (
            "candidate_adapter_alignment_requires_human_review"
            if problem in ADAPTER_CANDIDATES
            else "statement_level_alignment_only"
        )
        if comparison.get("conservative_verdict") != expected_verdict:
            errors.append(f"{label}: conservative verdict drifted")

        if row.get("human_semantic_review_required") is not True:
            errors.append(f"{label}: human semantic review must remain required")
        if row.get("submission_status") != NOT_READY:
            errors.append(f"{label}: submission status must be {NOT_READY}")

        adapter = row.get("adapter", {})
        if problem in ADAPTER_CANDIDATES:
            if adapter.get("status") != "candidate_requires_human_semantic_review":
                errors.append(f"{label}: adapter must require human semantic review")
            if adapter.get("target_declaration") != EXPECTED_ADAPTER_TARGETS[problem]:
                errors.append(f"{label}: adapter target drifted")
            if adapter.get("candidate_is_a_proof") is not False:
                errors.append(f"{label}: adapter candidate must not be called a proof")
            obligations = adapter.get("unproved_bridge_obligations", [])
            if not isinstance(obligations, list) or len(obligations) < 3:
                errors.append(f"{label}: adapter bridge obligations are incomplete")
            evidence = adapter.get("local_evidence", [])
            if not isinstance(evidence, list) or not evidence:
                errors.append(f"{label}: adapter lacks local evidence")
            else:
                for item in evidence:
                    errors.extend(local_evidence_errors(item))
        elif adapter.get("status") != "not_a_candidate":
            errors.append(f"{label}: only #257 and #1049 may be adapter candidates")

    # Render only after structural validation.  A malformed authored row should
    # be reported as a contract failure, not escape as a projection KeyError.
    if projection_text is not None and not errors:
        expected_projection = render_markdown(manifest, problem_index)
        if projection_text != expected_projection:
            errors.append(
                "docs/FORMAL_CONJECTURES_CROSSWALK.md drifted; regenerate with "
                "scripts/check_formal_conjectures_crosswalk.py --write"
            )
    return errors


def upstream_checkout_errors(
    manifest: dict[str, Any], checkout: Path
) -> list[str]:
    """Verify the pinned commit, bytes, anchors, and declaration coordinates."""
    errors: list[str] = []
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=checkout,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        return [f"upstream checkout is not a Git worktree: {checkout}"]
    observed_commit = completed.stdout.strip()
    if observed_commit != UPSTREAM_COMMIT:
        errors.append(
            f"upstream checkout HEAD is {observed_commit}, expected {UPSTREAM_COMMIT}"
        )

    for row in manifest.get("problems", []):
        problem = row.get("problem")
        source = row.get("upstream_source", {})
        relative = str(source.get("path", ""))
        path = checkout / relative
        label = f"problem {problem} upstream source"
        if not path.is_file():
            errors.append(f"{label} is missing: {relative}")
            continue
        data = path.read_bytes()
        observed_hash = sha256_bytes(data)
        if observed_hash != source.get("sha256"):
            errors.append(
                f"{label} SHA-256 is {observed_hash}, expected {source.get('sha256')}"
            )
        text = data.decode("utf-8")
        for anchor in source.get("signature_anchors", []):
            if anchor not in text:
                errors.append(f"{label} lost signature anchor: {anchor!r}")
        lines = text.splitlines()
        coordinate_rows = [
            {
                "name": source.get("primary_declaration", ""),
                "line": source.get("declaration_line"),
            },
            *source.get("related_declarations", []),
        ]
        for declaration in coordinate_rows:
            line_number = declaration.get("line")
            if not isinstance(line_number, int):
                errors.append(f"{label}: declaration line is not an integer")
                continue
            error = declaration_line_error(
                lines, str(declaration.get("name", "")), line_number, label
            )
            if error:
                errors.append(error)
    return errors


def render_markdown(
    manifest: dict[str, Any], problem_index: dict[str, Any]
) -> str:
    """Render the human crosswalk from the authored JSON."""
    indexed = {
        row["erdos_number"]: row for row in problem_index.get("problems", [])
    }
    upstream = manifest["upstream"]
    commit = upstream["commit"]
    repository = upstream["repository"]
    lines = [
        "<!-- Generated by scripts/check_formal_conjectures_crosswalk.py; do not edit. -->",
        "# Formal Conjectures crosswalk",
        "",
        manifest["purpose"],
        "",
        f"**Upstream:** [{repository}]({repository}) at exact commit "
        f"[`{commit}`]({repository}/commit/{commit}). Source hashes are SHA-256 over exact file bytes.",
        "",
        "**Boundary:** this is statement-identity and adapter-review metadata, not a Lean equivalence proof, novelty finding, contribution claim, or submission-readiness decision. Every problem remains open. Every row is `not_ready_to_submit`.",
        "",
        "| Problem | Formal Conjectures source | Primary declaration | Comparison | Adapter |",
        "|---:|---|---|---|---|",
    ]
    for row in manifest["problems"]:
        problem = row["problem"]
        source = row["upstream_source"]
        source_url = f"{repository}/blob/{commit}/{source['path']}#L{source['declaration_line']}"
        adapter = row["adapter"]["status"]
        lines.append(
            f"| #{problem} | [`{source['path']}`]({source_url})<br>`sha256:{source['sha256']}` | "
            f"`{source['primary_declaration']}` | `{row['comparison']['conservative_verdict']}` | "
            f"`{adapter}` |"
        )

    lines.extend(["", "## Per-problem comparison", ""])
    for row in manifest["problems"]:
        problem = row["problem"]
        source = row["upstream_source"]
        comparison = row["comparison"]
        lines.extend(
            [
                f"### Erdős #{problem}",
                "",
                f"Local question: {indexed[problem]['question']}",
                "",
                f"- Upstream declaration: `{source['primary_declaration']}` at `{source['path']}:{source['declaration_line']}`; proof status `{source['proof_status']}`.",
                f"- Statement scope: {comparison['statement_scope']}",
                f"- Indexing: {comparison['indexing']}",
                f"- Casts and ambient types: {comparison['casts_and_ambient_types']}",
                f"- Answer/proof status: {comparison['answer_and_proof_status']}",
                f"- Machine-checked equivalence: `{comparison['machine_checked_equivalence']}`.",
                f"- Submission status: `{row['submission_status']}`.",
                "",
            ]
        )

    lines.extend(["## Adapter candidates", ""])
    for row in manifest["problems"]:
        if row["problem"] not in ADAPTER_CANDIDATES:
            continue
        adapter = row["adapter"]
        lines.extend(
            [
                f"### Erdős #{row['problem']}: `{adapter['target_declaration']}`",
                "",
                "Candidate only; human semantic review is required and this is not ready to submit.",
                "",
                "Local evidence:",
                "",
            ]
        )
        for evidence in adapter["local_evidence"]:
            lines.append(
                f"- `{evidence['declaration']}` in `{evidence['path']}:{evidence['line']}`"
            )
        lines.extend(["", "Unproved bridge obligations:", ""])
        for obligation in adapter["unproved_bridge_obligations"]:
            lines.append(f"- {obligation}")
        lines.append("")

    lines.extend(
        [
            "## Reproduction",
            "",
            "Offline contract and projection check:",
            "",
            "```console",
            "python3 scripts/check_formal_conjectures_crosswalk.py",
            "```",
            "",
            "Byte-level verification against an exact upstream checkout:",
            "",
            "```console",
            "python3 scripts/check_formal_conjectures_crosswalk.py --upstream-checkout /path/to/formal-conjectures",
            "```",
            "",
        ]
    )
    return "\n".join(lines)


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write",
        action="store_true",
        help="refresh the generated Markdown projection after validating JSON",
    )
    parser.add_argument(
        "--upstream-checkout",
        type=Path,
        help="verify exact upstream bytes, anchors, and source coordinates",
    )
    args = parser.parse_args(argv)

    try:
        manifest = load_json(CROSSWALK_PATH)
        problem_index = load_json(PROBLEM_INDEX_PATH)
    except (OSError, json.JSONDecodeError) as error:
        print(f"formal-conjectures crosswalk input error: {error}", file=sys.stderr)
        return 1

    projection_text = None
    if not args.write:
        if not PROJECTION_PATH.is_file():
            print(f"missing generated projection: {PROJECTION_PATH}", file=sys.stderr)
            return 1
        projection_text = PROJECTION_PATH.read_text(encoding="utf-8")

    errors = crosswalk_errors(manifest, problem_index, projection_text)
    if args.upstream_checkout is not None:
        errors.extend(upstream_checkout_errors(manifest, args.upstream_checkout.resolve()))
    if errors:
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    if args.write:
        PROJECTION_PATH.write_text(
            render_markdown(manifest, problem_index), encoding="utf-8"
        )

    suffix = " with exact upstream byte verification" if args.upstream_checkout else ""
    print(
        "Formal Conjectures crosswalk is current: 8/8 problems, exact commit pin, "
        f"2 human-review-only adapter candidates, 0 submission-ready rows{suffix}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
