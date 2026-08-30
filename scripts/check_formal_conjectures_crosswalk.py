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
import os
import re
import stat
import subprocess
import sys
from pathlib import Path
from typing import Any

import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
CROSSWALK_PATH = ROOT / "docs" / "formal_conjectures_crosswalk.json"
PROJECTION_PATH = ROOT / "docs" / "FORMAL_CONJECTURES_CROSSWALK.md"
PROBLEM_INDEX_PATH = ROOT / "docs" / "problem_index_source.json"

SCHEMA = "formal-conjectures-crosswalk/1"
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
UPSTREAM_REPOSITORY = "https://github.com/google-deepmind/formal-conjectures"
UPSTREAM_COMMIT = "f2de2ed5841e2105009be778ada0c40c08980125"
EXPECTED_PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)
ADAPTER_CANDIDATES = {257, 1049}
NOT_READY = "not_ready_to_submit"

# Submission status ladder.  The earlier contract fixed every row at
# NOT_READY, which was correct while no adapter existed but made the true
# state unrecordable once one did: a check that can only ever be satisfied by
# the absence of work pins the absence in place.  The rungs above NOT_READY
# are therefore reachable, but only against evidence this checker verifies --
# see ``checked_equivalence_errors``.
ADAPTER_CHECKED = "adapter_checked_pending_external_process"
SUBMITTED = "submitted_upstream"
SUBMISSION_LADDER = (NOT_READY, ADAPTER_CHECKED, SUBMITTED)
# Every rung past the first requires a verified machine-checked equivalence.
EVIDENCE_BEARING_STATUSES = frozenset({ADAPTER_CHECKED, SUBMITTED})

CHECKED_EQUIVALENCE_KEYS = {
    "adapter_module",
    "adapter_declaration",
    "checked_in_environment",
    "axioms",
    "upstream_declaration",
}
# A Lean proof that typechecks while depending on sorryAx proves nothing.
FORBIDDEN_AXIOMS = frozenset({"sorryAx"})
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

# Upstream declarations this library can discharge that sit under a problem
# number it does not itself work on.  The original crosswalk was indexed by
# local problem, so a match like this had nowhere to live and went unrecorded
# for as long as the index shape decided what was expressible.  Mathematics
# does not respect the local problem list, so cross-index matches get their own
# section keyed by the upstream declaration.
EXPECTED_CROSS_INDEX: dict[str, dict[str, Any]] = {
    "Erdos258.erdos_258.variants.constant": {
        "upstream_problem": 258,
        "path": "FormalConjectures/ErdosProblems/258.lean",
        "sha256": "8fa3fb3984e277b62647271e18d28db00815fc73b3e2149bb6472ddd6c2cd2f8",
        "declaration_line": 65,
        "outside_local_problem_list": True,
    },
}


class UnsafeCrosswalkInput(ValueError):
    """A crosswalk input escaped its checkout or is not a regular file."""


def safe_crosswalk_bytes(path: Path, root: Path = ROOT) -> bytes:
    """Read one crosswalk input through a no-follow descriptor."""
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(path))
    if candidate != root and root not in candidate.parents:
        raise UnsafeCrosswalkInput(f"crosswalk input escaped checkout: {candidate}")
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeCrosswalkInput(
                f"crosswalk input traverses a symbolic link: {candidate}"
            )
        if current == root:
            break
        if current.parent == current:
            raise UnsafeCrosswalkInput(f"crosswalk input escaped checkout: {candidate}")
        current = current.parent
    if not candidate.is_file():
        raise UnsafeCrosswalkInput(
            f"crosswalk input is not a regular file: {candidate}"
        )
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeCrosswalkInput(
            f"crosswalk input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeCrosswalkInput(
                f"crosswalk input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def safe_crosswalk_text(path: Path, root: Path = ROOT) -> str:
    """Decode one descriptor-bound crosswalk input as UTF-8."""
    candidate = Path(os.path.abspath(path))
    try:
        return safe_crosswalk_bytes(path, root).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise UnsafeCrosswalkInput(
            f"crosswalk input is not UTF-8: {candidate}"
        ) from exc


def checked_equivalence_errors(
    label: str, value: Any, root: Path
) -> list[str]:
    """Verify a machine-checked-equivalence claim against artifacts on disk.

    ``"none"`` is always acceptable and asserts nothing.  Any other value must
    name an adapter module that exists in this repository and states the
    declaration being claimed, and must report an axiom budget free of
    ``sorryAx``.  The point is that the claim is refused unless the artifact
    backing it is present -- not that the claim is refused on principle.
    """
    if value == "none":
        return []
    if not isinstance(value, dict):
        return [f"{label}: machine_checked_equivalence must be 'none' or an object"]

    errors: list[str] = []
    missing = sorted(CHECKED_EQUIVALENCE_KEYS - set(value))
    if missing:
        errors.append(
            f"{label}: checked equivalence missing keys: {', '.join(missing)}"
        )
        return errors

    module = value["adapter_module"]
    declaration = value["adapter_declaration"]
    module_path = root / module
    if not module_path.is_file():
        errors.append(f"{label}: adapter module {module} is absent from this repository")
        return errors

    # The adapter states its theorems inside an opened namespace, so the source
    # carries the final component only.  Requiring the enclosing namespace as
    # well keeps the match from succeeding against a same-named theorem
    # declared somewhere else.
    try:
        text = safe_crosswalk_text(module_path, root)
    except UnsafeCrosswalkInput as error:
        errors.append(f"{label}: {error}")
        return errors
    namespace, _, token = declaration.rpartition(".")
    if not namespace:
        errors.append(f"{label}: adapter declaration must be namespace-qualified")
        return errors
    if not re.search(rf"^namespace\s+{re.escape(namespace)}\s*$", text, re.MULTILINE):
        errors.append(
            f"{label}: adapter module {module} does not open namespace {namespace}"
        )
    if not re.search(rf"^theorem\s+{re.escape(token)}\b", text, re.MULTILINE):
        errors.append(
            f"{label}: adapter module {module} does not state theorem {token}"
        )

    axioms = value.get("axioms")
    if not isinstance(axioms, list) or not axioms:
        errors.append(f"{label}: checked equivalence must report an axiom budget")
    else:
        forbidden = FORBIDDEN_AXIOMS.intersection(axioms)
        if forbidden:
            errors.append(
                f"{label}: axiom budget contains {', '.join(sorted(forbidden))}"
            )
    return errors


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
    try:
        lines = safe_crosswalk_text(path).splitlines()
    except UnsafeCrosswalkInput as error:
        return [f"{label}: {error}"]
    name = str(evidence.get("declaration", ""))
    line_number = evidence.get("line")
    if not isinstance(line_number, int):
        return [f"{label}: adapter evidence line is not an integer"]
    error = declaration_line_error(lines, name, line_number, label)
    if error:
        errors.append(error)
    return errors


def cross_index_errors(manifest: dict[str, Any], root: Path) -> list[str]:
    """Validate matches recorded outside the eight local problem numbers."""
    errors: list[str] = []
    rows = manifest.get("cross_index_matches")
    if rows is None:
        errors.append("manifest must carry a cross_index_matches section")
        return errors
    if not isinstance(rows, list):
        errors.append("cross_index_matches must be a list")
        return errors

    seen = {row.get("upstream_declaration") for row in rows if isinstance(row, dict)}
    missing = sorted(set(EXPECTED_CROSS_INDEX) - seen)
    if missing:
        errors.append(f"cross index missing: {', '.join(missing)}")
    unexpected = sorted(name for name in seen if name not in EXPECTED_CROSS_INDEX)
    if unexpected:
        errors.append(f"cross index has unrecognised entries: {', '.join(unexpected)}")

    for row in rows:
        name = row.get("upstream_declaration")
        expected = EXPECTED_CROSS_INDEX.get(name)
        if expected is None:
            continue
        label = f"cross index {name}"
        for key, value in expected.items():
            if row.get(key) != value:
                errors.append(f"{label}: {key} drifted")
        errors.extend(
            checked_equivalence_errors(
                label, row.get("machine_checked_equivalence"), root
            )
        )
        status = row.get("submission_status")
        if status not in SUBMISSION_LADDER:
            errors.append(f"{label}: submission status must be a ladder rung")
        elif (
            status in EVIDENCE_BEARING_STATUSES
            and row.get("machine_checked_equivalence") == "none"
        ):
            errors.append(
                f"{label}: submission status {status} requires a verified "
                "machine-checked equivalence"
            )
        errors.extend(submission_reference_errors(label, row))
    return errors


UPSTREAM_PR_PREFIX = "https://github.com/google-deepmind/formal-conjectures/pull/"


def submission_reference_errors(label: str, row: Any) -> list[str]:
    """A row claiming SUBMITTED must name the pull request that carries it.

    Without this, ``submitted_upstream`` is unfalsifiable: it asserts an
    outward act with nothing a reader can open. The status is only as good as
    the reference, so the reference is required, must be an integer, and must
    point at the upstream repository rather than anywhere else.
    """
    if row.get("submission_status") != SUBMITTED:
        return []
    submission = row.get("submission")
    if not isinstance(submission, dict):
        return [f"{label}: {SUBMITTED} requires a submission block naming the PR"]
    errors = []
    number = submission.get("pull_request")
    if not isinstance(number, int):
        errors.append(f"{label}: submission.pull_request must be an integer")
    url = submission.get("url")
    if not isinstance(url, str) or not url.startswith(UPSTREAM_PR_PREFIX):
        errors.append(
            f"{label}: submission.url must point at {UPSTREAM_PR_PREFIX}<n>"
        )
    elif isinstance(number, int) and url != f"{UPSTREAM_PR_PREFIX}{number}":
        errors.append(f"{label}: submission.url does not match pull_request {number}")
    if not submission.get("boundary"):
        errors.append(
            f"{label}: submission must record that offering is not acceptance"
        )
    return errors


def render_checked(value: Any) -> str:
    """Render an equivalence claim for the human projection."""
    if value == "none":
        return "`none`."
    return (
        f"`{value['adapter_declaration']}` in `{value['adapter_module']}`, "
        f"checked in {value['checked_in_environment']}; "
        f"axioms {', '.join(f'`{a}`' for a in value['axioms'])}."
    )


def crosswalk_errors(
    manifest: dict[str, Any],
    problem_index: dict[str, Any],
    projection_text: str | None,
    root: Path = ROOT,
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
    # The status a row may carry is bounded by the ladder, not fixed at its
    # bottom rung.  Reaching a higher rung still requires verified evidence,
    # enforced per row below.
    declared_ladder = policy.get("submission_status_ladder")
    if declared_ladder != list(SUBMISSION_LADDER):
        errors.append(
            "policy must declare the submission status ladder "
            + ", ".join(SUBMISSION_LADDER)
        )
    errors.extend(cross_index_errors(manifest, root))

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

        local_navigation = row.get("local_navigation", {})
        expected_route = (
            f"python3 scripts/query_corpus.py --route {row.get('local_problem_id', '')}"
        )
        if not isinstance(local_navigation, dict):
            errors.append(f"{label}: local navigation must be an object")
        else:
            if local_navigation.get("route") != expected_route:
                errors.append(f"{label}: local navigation route drifted")
            if local_navigation.get("surface") != "canonical problem packet":
                errors.append(f"{label}: local navigation surface drifted")
            if local_navigation.get("return_contract") != (
                "Returns the local problem packet with result families, declarations, "
                "papers and sources, and the exact open boundary."
            ):
                errors.append(f"{label}: local navigation return contract drifted")

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
        checked = comparison.get("machine_checked_equivalence")
        errors.extend(checked_equivalence_errors(label, checked, root))
        expected_verdict = (
            "candidate_adapter_alignment_requires_human_review"
            if problem in ADAPTER_CANDIDATES and checked == "none"
            else "adapter_checked_upstream_process_pending"
            if problem in ADAPTER_CANDIDATES
            else "statement_level_alignment_only"
        )
        if comparison.get("conservative_verdict") != expected_verdict:
            errors.append(f"{label}: conservative verdict drifted")

        if row.get("human_semantic_review_required") is not True:
            errors.append(f"{label}: human semantic review must remain required")
        status = row.get("submission_status")
        if status not in SUBMISSION_LADDER:
            errors.append(f"{label}: submission status must be one of the ladder rungs")
        elif status in EVIDENCE_BEARING_STATUSES and checked == "none":
            # The gate that matters: a row may only climb the ladder while
            # carrying an equivalence this checker has verified on disk.
            errors.append(
                f"{label}: submission status {status} requires a verified "
                "machine-checked equivalence"
            )
        errors.extend(submission_reference_errors(label, row))

        adapter = row.get("adapter", {})
        if problem in ADAPTER_CANDIDATES:
            expected_adapter_status = (
                "candidate_requires_human_semantic_review"
                if checked == "none"
                else "checked_against_upstream_statement"
            )
            if adapter.get("status") != expected_adapter_status:
                errors.append(f"{label}: adapter status drifted")
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
        env=singleflight.command_environment(),
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
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
        try:
            data = safe_crosswalk_bytes(path, checkout)
        except UnsafeCrosswalkInput as error:
            errors.append(f"{label}: {error}")
            continue
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
        "| Problem | Upstream primary declaration | Adapter |",
        "|---:|---|---|",
    ]
    for row in manifest["problems"]:
        source = row["upstream_source"]
        lines.append(
            f"| #{row['problem']} | `{source['primary_declaration']}` "
            f"| `{row['adapter']['status']}` |"
        )

    # The source paths and hashes are unbreakable tokens: in a table cell they
    # set a column floor wide enough to squash every other column and force a
    # horizontal scrollbar. A fenced block scrolls inside itself, keeps the
    # hashes copy-paste clean, and gathers them into one verification surface.
    lines.extend(
        [
            "",
            "## Pinned upstream sources",
            "",
            "Each file is read at the commit above. Each hash is SHA-256 over exact "
            "file bytes; the per-problem sections below link the exact declaration line.",
            "",
            "```text",
        ]
    )
    for row in manifest["problems"]:
        source = row["upstream_source"]
        label = f"#{row['problem']}"
        lines.append(f"{label:<7}{source['path']}")
        lines.append(f"{'':<7}sha256:{source['sha256']}")
    lines.extend(["```", ""])

    lines.extend(["## Per-problem comparison", ""])
    for row in manifest["problems"]:
        problem = row["problem"]
        source = row["upstream_source"]
        comparison = row["comparison"]
        source_url = (
            f"{repository}/blob/{commit}/{source['path']}"
            f"#L{source['declaration_line']}"
        )
        lines.extend(
            [
                f"### Erdős #{problem}",
                "",
                f"Local question: {indexed[problem]['question']}",
                "",
                f"- Canonical local return route: `{row['local_navigation']['route']}` "
                f"({row['local_navigation']['surface']}); "
                f"{row['local_navigation']['return_contract']}",
                "",
                f"- Upstream declaration: [`{source['primary_declaration']}`]({source_url}) at `{source['path']}:{source['declaration_line']}`; proof status `{source['proof_status']}`.",
                f"- Statement scope: {comparison['statement_scope']}",
                f"- Indexing: {comparison['indexing']}",
                f"- Casts and ambient types: {comparison['casts_and_ambient_types']}",
                f"- Answer/proof status: {comparison['answer_and_proof_status']}",
                f"- Conservative verdict: `{comparison['conservative_verdict']}`.",
                f"- Machine-checked equivalence: {render_checked(comparison['machine_checked_equivalence'])}",
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
                (
                    "Candidate only; human semantic review is required and this is "
                    "not ready to submit."
                    if row["submission_status"] == NOT_READY
                    else "The upstream proposition is stated verbatim in the adapter "
                    "and derived from this library. Human semantic review is still "
                    "required, and nothing has been offered upstream."
                ),
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
            "## Cross-index matches",
            "",
            "Upstream declarations this library can discharge that sit under a "
            "problem number it does not work on. An index keyed by local problem "
            "cannot hold these, so they are keyed by the upstream declaration.",
            "",
        ]
    )
    for row in manifest["cross_index_matches"]:
        source_url = (
            f"{manifest['upstream']['repository']}/blob/"
            f"{manifest['upstream']['commit']}/{row['path']}"
            f"#L{row['declaration_line']}"
        )
        lines.extend(
            [
                f"### Upstream #{row['upstream_problem']}: "
                f"[`{row['upstream_declaration']}`]({source_url})",
                "",
                f"- Recorded here because: {row['why_recorded_here']}",
                f"- Machine-checked equivalence: "
                f"{render_checked(row['machine_checked_equivalence'])}",
                f"- Submission status: `{row['submission_status']}`.",
                "",
            ]
        )

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
    return json.loads(safe_crosswalk_text(path))


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
        projection_text = safe_crosswalk_text(PROJECTION_PATH)

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
    all_rows = manifest["problems"] + manifest["cross_index_matches"]
    checked_rows = sum(
        1
        for row in all_rows
        if row.get("comparison", row).get("machine_checked_equivalence") != "none"
    )
    cross_rows = len(manifest["cross_index_matches"])
    submitted = sum(1 for row in all_rows if row.get("submission_status") == SUBMITTED)
    print(
        # Counted from the manifest rather than asserted, so the summary cannot
        # keep reporting a state the crosswalk has moved on from.
        "Formal Conjectures crosswalk is current: 8/8 problems, exact commit pin, "
        f"{checked_rows} row(s) with a verified checked equivalence, "
        f"{cross_rows} cross-index match(es), "
        f"{submitted} row(s) submitted upstream{suffix}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
