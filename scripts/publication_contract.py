#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Validation helpers for the public publication-artifact contract."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import subprocess
import tomllib
from pathlib import Path
from typing import Any

import validation_singleflight as singleflight


CONTRACT_PATH = "docs/publication_contract.json"
EVIDENCE_PATH = "docs/publication_evidence.json"
ENTRY_SOURCE_PATH = "docs/publication_entry_source.json"
ENTRY_PACKET_PATH = "docs/publication_entry_packet.json"
MUTATION_MANIFEST_PATH = "experiments/publication_mutations.json"
MUTATION_HARNESS_PATH = "scripts/run_publication_mutations.py"
CLAIMS_PATH = "docs/claims.json"
PROBLEMS_PATH = "docs/problems.json"
METHODOLOGY_PATH = "docs/methodology.json"
AGENT_ENTRY_PATH = "AGENTS.md"
MAKEFILE_PATH = "paper/Makefile"
REUSE_PATH = "REUSE.toml"
MANUSCRIPT_LICENSE = "CC-BY-4.0"
NOTE_ARTIFACT_CLASS = "problem_note"
SPDX_LICENSE_HEADER = "SPDX-License-" "Identifier: "
SCHEMA = "erdos249257-publication-contract/1"
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
EVIDENCE_SCHEMA = "erdos249257-publication-evidence/1"
ENTRY_SOURCE_SCHEMA = "erdos249257-publication-entry-source/1"
ENTRY_PACKET_SCHEMA = "erdos249257-publication-entry-packet/1"
MUTATION_MANIFEST_SCHEMA = "erdos249257-publication-mutation-operators/1"
EXPECTED_INVARIANT_FAMILIES = (
    "proof_trust",
    "registry_structure",
    "source_coordinates",
    "paper_anchoring",
    "boundary_language",
    "projection_freshness",
    "byte_budgets",
)
EXPECTED_MUTATION_MATRIX = {
    "M1": ("rejected", "projection_freshness", (), 139.4),
    "M2": ("rejected", "boundary_language", (), 171.5),
    "M3": (
        "rejected",
        "source_coordinates",
        ("projection_freshness",),
        239.1,
    ),
    "M4": (
        "rejected",
        "source_coordinates",
        ("projection_freshness",),
        192.2,
    ),
    "M5": (
        "rejected",
        "registry_structure",
        ("source_coordinates", "projection_freshness"),
        121.4,
    ),
    "M6": ("rejected", "projection_freshness", (), 184.8),
    "M7": ("rejected", "proof_trust", (), 4.7),
    "M8": ("escaped", None, (), 176.0),
    "M9": (
        "rejected",
        "paper_anchoring",
        ("source_coordinates", "projection_freshness"),
        122.8,
    ),
    "M10": ("rejected", "byte_budgets", ("projection_freshness",), 210.5),
}
REQUIRED_ARTIFACT_FIELDS = {
    "id",
    "title",
    "artifact_class",
    "source_path",
    "source_content_digest",
    "rendered_path",
    "rendered_content_digest",
    "authority_posture",
    "claim_scope",
    "architecture_ref",
    "entry_route_id",
    "validation",
}


class RepositoryReader:
    """Read either the worktree or one committed/staged Git snapshot."""

    def __init__(
        self,
        root: Path,
        git_ref: str | None = None,
        byte_overrides: dict[str, bytes] | None = None,
    ) -> None:
        self.root = root
        self.git_ref = git_ref
        self.byte_overrides = byte_overrides or {}

    def _git_spec(self, relative: str) -> str:
        return f":{relative}" if self.git_ref == ":" else f"{self.git_ref}:{relative}"

    def _git_run(self, *args: str, text: bool = False) -> subprocess.CompletedProcess[Any]:
        """Read a committed snapshot without inheriting ambient Git state."""
        return subprocess.run(
            ["git", *args],
            cwd=self.root,
            capture_output=True,
            check=False,
            text=text,
            timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
            env=singleflight.command_environment(),
        )

    @staticmethod
    def _has_symlink_component(path: Path) -> bool:
        """Reject worktree reads that traverse a substituted path component."""
        current = Path(os.path.abspath(path))
        while True:
            if current.is_symlink():
                return True
            if current.parent == current:
                return False
            current = current.parent

    def read_bytes(self, relative: str) -> bytes:
        if relative in self.byte_overrides:
            return self.byte_overrides[relative]
        if self.git_ref is None:
            path = self.root / relative
            if self._has_symlink_component(path):
                raise ValueError(
                    f"worktree source path must not traverse symbolic links: {relative}"
                )
            return path.read_bytes()
        completed = self._git_run("show", self._git_spec(relative))
        if completed.returncode != 0:
            detail = completed.stderr.decode("utf-8", errors="replace").strip()
            raise FileNotFoundError(detail or relative)
        return completed.stdout

    def read_text(self, relative: str) -> str:
        return self.read_bytes(relative).decode("utf-8")

    def exists(self, relative: str) -> bool:
        try:
            self.read_bytes(relative)
        except (FileNotFoundError, OSError, UnicodeError):
            return False
        return True

    def git_object_exists(self, object_name: str) -> bool:
        return (
            self._git_run(
                "cat-file",
                "-e",
                f"{object_name}^{{commit}}",
            ).returncode
            == 0
        )

    def is_shallow_repository(self) -> bool:
        completed = self._git_run(
            "rev-parse",
            "--is-shallow-repository",
            text=True,
        )
        return completed.returncode == 0 and completed.stdout.strip() == "true"

    @staticmethod
    def git_object_unavailable_message(
        object_name: str,
        *,
        shallow: bool,
    ) -> str:
        if shallow:
            return (
                f"{object_name} is outside this shallow clone; run "
                "`git fetch --unshallow origin` and rerun the check"
            )
        return f"{object_name} is absent"

    def git_object_unavailable_detail(self, object_name: str) -> str | None:
        if self.git_object_exists(object_name):
            return None
        return self.git_object_unavailable_message(
            object_name,
            shallow=self.is_shallow_repository(),
        )


def sha256(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def canonical_json_bytes(data: dict[str, Any]) -> bytes:
    return (
        json.dumps(data, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    ).encode("utf-8")


def load_json(reader: RepositoryReader, relative: str) -> dict[str, Any]:
    return json.loads(reader.read_text(relative))


def makefile_papers(text: str) -> set[str]:
    logical = text.replace("\\\n", " ")
    match = re.search(r"(?m)^PAPERS\s*=\s*(.+)$", logical)
    if not match:
        return set()
    return {token for token in match.group(1).split() if token}


def reuse_manuscript_pdfs(data: dict[str, Any]) -> set[str]:
    paths: set[str] = set()
    for annotation in data.get("annotations", []):
        if annotation.get("SPDX-License-Identifier") != "CC-BY-4.0":
            continue
        raw_paths = annotation.get("path", [])
        if isinstance(raw_paths, str):
            raw_paths = [raw_paths]
        for path in raw_paths:
            if (
                isinstance(path, str)
                and path.endswith(".pdf")
                and "/" not in path
                and "*" not in path
            ):
                paths.add(path)
    return paths


def reuse_manuscript_override_errors(
    data: dict[str, Any], registered_pdfs: set[str]
) -> list[str]:
    """Bind registered manuscript PDFs to one explicit REUSE override."""
    annotations = [
        row
        for row in data.get("annotations", [])
        if row.get("SPDX-License-Identifier") == MANUSCRIPT_LICENSE
    ]
    if len(annotations) != 1:
        return [
            "publication manuscript PDFs must use one CC-BY-4.0 REUSE annotation"
        ]
    annotation = annotations[0]
    errors: list[str] = []
    if annotation.get("precedence") != "override":
        errors.append(
            "publication manuscript CC-BY-4.0 annotation must use "
            "precedence = override"
        )
    if reuse_manuscript_pdfs(data) != registered_pdfs:
        errors.append(
            "publication manuscript CC-BY-4.0 override must cover exactly "
            "the registered root PDFs"
        )
    return errors


def manuscript_source_license_errors(path: str, text: str) -> list[str]:
    """Require a registered manuscript source to declare the manuscript licence."""
    header = "\n".join(text.splitlines()[:12])
    expected = f"{SPDX_LICENSE_HEADER}{MANUSCRIPT_LICENSE}"
    if expected not in header:
        return [
            f"publication manuscript source {path!r} must declare "
            f"{MANUSCRIPT_LICENSE} in its SPDX header"
        ]
    if f"{SPDX_LICENSE_HEADER}Apache-2.0" in header:
        return [
            f"publication manuscript source {path!r} must not use the "
            "Apache-2.0 software licence"
        ]
    return []


def normalize_latex_evidence(text: str) -> str:
    """Flatten stable prose anchors without pretending to parse all of TeX."""
    normalized = (
        text.replace("{,}", ",")
        .replace("~", " ")
        .replace("$", "")
        .replace(r"\_", "_")
    )
    for _ in range(3):
        normalized = re.sub(
            r"\\(?:emph|textbf|texttt)\{([^{}]*)\}",
            r"\1",
            normalized,
        )
    normalized = normalized.replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", normalized).strip().lower()


def validate_systems_evidence_source(
    artifact: dict[str, Any],
    source_text: str,
) -> list[str]:
    """Keep the public paper architecture-first while linking its evidence owner."""
    errors: list[str] = []
    normalized = normalize_latex_evidence(source_text)
    required_patterns = {
        "plain architecture title": (
            r"from lean proofs to public claims"
        ),
        "formal source owner": r"erdos249257\.lean",
        "reviewed claim owner": r"docs/claims\.json",
        "paper inventory owner": r"docs/publication_contract\.json",
        "historical evidence owner": r"docs/publication_evidence\.json",
        "release program": r"scripts/check_release\.py",
        "continuous-integration owner": r"\.github/workflows/lean\.yml",
        "human judgement boundary": (
            r"does not technically force a second independent mathematician"
        ),
        "coverage boundary": r"coverage boundary, not a reliability score",
        "post-repair example": (
            r"post-repair witness accepts the current readme and rejects a "
            r"test copy containing the false clause"
        ),
    }
    for label, pattern in required_patterns.items():
        if not re.search(pattern, normalized):
            errors.append(
                f"systems artifact {artifact['id']!r} source lost its "
                f"{label} evidence anchor"
            )
    for pattern in (
        r"\bm(?:10|[1-9])\b",
        r"\b9/10\b",
        r"\b5,207\b",
        r"\bunbounded quantifier\b",
    ):
        if re.search(pattern, normalized):
            errors.append(
                f"architecture artifact {artifact['id']!r} exposes private or "
                f"score-like shorthand {pattern!r}"
            )
    return errors


def validate_mutation_evidence_receipt(
    receipt: dict[str, Any],
    artifact: dict[str, Any],
    reader: RepositoryReader,
) -> list[str]:
    """Validate the immutable reported mutation matrix and its claim ceiling."""
    errors: list[str] = []
    if receipt.get("schema") != EVIDENCE_SCHEMA:
        errors.append(f"{EVIDENCE_PATH} must use schema {EVIDENCE_SCHEMA}")
    if receipt.get("record_kind") != (
        "structured_transcription_of_reported_historical_runs"
    ):
        errors.append("publication evidence record kind drifted")
    if receipt.get("authority_posture") != (
        "historical_systems_evidence_not_Lean_proof_authority_and_not_a_fresh_rerun"
    ):
        errors.append("publication evidence authority posture drifted")
    if receipt.get("publication_artifact_id") != artifact["id"]:
        errors.append("publication evidence points at the wrong artifact")

    source = receipt.get("source", {})
    if source.get("manuscript") != artifact["source_path"]:
        errors.append("publication evidence manuscript path drifted")
    if source.get("contract") != CONTRACT_PATH:
        errors.append("publication evidence lost its contract owner")

    provenance = receipt.get("provenance", {})
    raw_logs = provenance.get("raw_run_logs_registered")
    operators = provenance.get("executable_mutation_operators_registered")
    if raw_logs is not False:
        paths = provenance.get("raw_run_log_paths", [])
        if not paths or any(not reader.exists(path) for path in paths):
            errors.append(
                "publication evidence may claim registered raw logs only when "
                "all raw_run_log_paths exist"
            )
    if operators is not False:
        manifest = provenance.get("mutation_operator_manifest")
        if not isinstance(manifest, str) or not reader.exists(manifest):
            errors.append(
                "publication evidence may claim executable mutation operators "
                "only with an existing mutation_operator_manifest"
            )
    if provenance.get("reconstructed_executable_mutation_operators_registered") is not True:
        errors.append(
            "publication evidence must register the deterministic mutation reconstruction"
        )
    reconstruction_manifest = provenance.get("reconstruction_manifest")
    reconstruction_harness = provenance.get("reconstruction_harness")
    if reconstruction_manifest != MUTATION_MANIFEST_PATH:
        errors.append("publication evidence reconstruction manifest path drifted")
    if reconstruction_harness != MUTATION_HARNESS_PATH:
        errors.append("publication evidence reconstruction harness path drifted")
    for relative, digest_field in (
        (MUTATION_MANIFEST_PATH, "reconstruction_manifest_digest"),
        (MUTATION_HARNESS_PATH, "reconstruction_harness_digest"),
    ):
        if not reader.exists(relative):
            errors.append(f"publication evidence reconstruction path is missing: {relative}")
            continue
        actual = sha256(reader.read_bytes(relative))
        if provenance.get(digest_field) != actual:
            errors.append(
                f"publication evidence {digest_field} drifted: "
                f"expected {provenance.get(digest_field)}, actual {actual}"
            )
    try:
        reconstruction = load_json(reader, MUTATION_MANIFEST_PATH)
    except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
        errors.append(f"{MUTATION_MANIFEST_PATH}: {error}")
        reconstruction = {}
    if reconstruction.get("schema") != MUTATION_MANIFEST_SCHEMA:
        errors.append(
            f"{MUTATION_MANIFEST_PATH} must use schema {MUTATION_MANIFEST_SCHEMA}"
        )
    if reconstruction.get("experiment_kind") != (
        "deterministic_reconstruction_not_exact_historical_replay"
    ):
        errors.append("publication mutation manifest lost its reconstruction boundary")
    if reconstruction.get("checkpoint") != artifact["evidence_boundary"][
        "evaluation_checkpoint"
    ]:
        errors.append("publication mutation manifest checkpoint drifted")
    if reconstruction.get("historical_evidence") != EVIDENCE_PATH:
        errors.append("publication mutation manifest lost its historical evidence owner")
    reconstructed_rows = reconstruction.get("operators", [])
    reconstructed_ids = [
        row.get("id") for row in reconstructed_rows if isinstance(row, dict)
    ]
    if reconstructed_ids != list(EXPECTED_MUTATION_MATRIX):
        errors.append("publication mutation manifest must register M1 through M10")
    exact_target_ids = {
        row.get("id")
        for row in reconstructed_rows
        if isinstance(row, dict) and row.get("exact_original_target_registered") is True
    }
    if exact_target_ids != {"M6", "M8", "M10"}:
        errors.append("publication mutation exact-target provenance drifted")
    if provenance.get("operator_verification") != (
        "python3 scripts/run_publication_mutations.py --verify-operators"
    ):
        errors.append("publication evidence operator-verification route drifted")
    claim_ceiling = str(provenance.get("claim_ceiling", "")).lower()
    for phrase in (
        "not a fresh rerun",
        "does not reconstruct missing raw run logs",
        "does not treat deterministic replacement targets as the exact original edits",
    ):
        if phrase not in claim_ceiling:
            errors.append(
                f"publication evidence provenance lost claim ceiling phrase: {phrase}"
            )

    evaluation = receipt.get("evaluation", {})
    contract_evidence = artifact["evidence_boundary"]
    if evaluation.get("checkpoint") != contract_evidence["evaluation_checkpoint"]:
        errors.append("publication evidence checkpoint drifted from the contract")
    baseline = evaluation.get("baseline", {})
    if baseline.get("release_check_count") != contract_evidence[
        "release_check_count_at_evaluation"
    ]:
        errors.append("publication evidence release-check baseline drifted")
    if baseline.get("wall_time_seconds") != 144.5:
        errors.append("publication evidence baseline timing drifted")
    if baseline.get("result") != "all_checks_passed":
        errors.append("publication evidence baseline result drifted")
    if baseline.get("negative_fixture_count") != 69:
        errors.append("publication evidence negative-fixture count drifted")

    corpus_snapshot = evaluation.get("corpus_snapshot", {})
    checkpoint = str(evaluation.get("checkpoint") or "")
    unavailable_detail = reader.git_object_unavailable_detail(checkpoint)
    checkpoint_claims: dict[str, Any] | None = None
    checkpoint_atlas: dict[str, Any] | None = None
    if unavailable_detail is None:
        try:
            checkpoint_reader = RepositoryReader(reader.root, checkpoint)
            checkpoint_claims = load_json(checkpoint_reader, CLAIMS_PATH)
            checkpoint_atlas = load_json(
                checkpoint_reader,
                "docs/declaration_atlas.json",
            )
        except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
            errors.append(
                f"publication evidence checkpoint census is unreadable: {error}"
            )
            checkpoint_claims = None
            checkpoint_atlas = None
    if checkpoint_claims is not None and checkpoint_atlas is not None:
        atlas_summary = checkpoint_atlas["summary"]
        assembly = checkpoint_claims["machine_readable_paper"][
            "publication_assembly"
        ]
        derived_snapshot = {
            "snapshot_kind": "evaluation_checkpoint_not_current_tree",
            "claims_source": CLAIMS_PATH,
            "declaration_atlas_source": "docs/declaration_atlas.json",
            "module_count": atlas_summary["module_count"],
            "declaration_count": atlas_summary["declaration_count"],
            "theorem_like_count": atlas_summary["theorem_like_count"],
            "generated_certificate_declaration_count": atlas_summary[
                "generated_certificate_declaration_count"
            ],
            "curated_claim_count": len(checkpoint_claims["claims"]),
            "contribution_family_count": len(assembly["contribution_families"]),
            "status_count": len(checkpoint_claims["status_taxonomy"]),
            "remaining_open_proposition_count": len(
                checkpoint_claims["remaining_open_propositions"]
            ),
        }
        if corpus_snapshot != derived_snapshot:
            errors.append(
                "publication evidence corpus snapshot drifted from the "
                "evaluation-checkpoint claims and declaration atlas"
            )

    protocol = evaluation.get("protocol", {})
    expected_protocol = {
        "worktree_posture": "isolated_worktree_pinned_at_evaluation_checkpoint",
        "application_mode": "one_mutation_at_a_time",
        "tree_restored_between_runs": True,
        "full_release_gate_run_after_each_mutation": True,
        "mutation_author_relationship": "mutations_authored_by_checker_author",
    }
    for field, expected in expected_protocol.items():
        if protocol.get(field) != expected:
            errors.append(f"publication evidence protocol field drifted: {field}")

    families = evaluation.get("invariant_families", [])
    family_ids = [row.get("id") for row in families if isinstance(row, dict)]
    if tuple(family_ids) != EXPECTED_INVARIANT_FAMILIES:
        errors.append("publication evidence invariant-family order or coverage drifted")

    mutations = evaluation.get("mutations", [])
    mutation_ids = [
        row.get("id") for row in mutations if isinstance(row, dict)
    ]
    if mutation_ids != list(EXPECTED_MUTATION_MATRIX):
        errors.append("publication evidence mutation ids or order drifted")
    mutations_by_id = {
        row.get("id"): row for row in mutations if isinstance(row, dict)
    }
    for mutation_id, expected in EXPECTED_MUTATION_MATRIX.items():
        row = mutations_by_id.get(mutation_id)
        if row is None:
            continue
        actual = (
            row.get("outcome"),
            row.get("first_detector"),
            tuple(row.get("additional_detectors", [])),
            row.get("wall_time_seconds"),
        )
        if actual != expected:
            errors.append(
                f"publication evidence matrix row drifted: {mutation_id}; "
                f"expected={expected}, actual={actual}"
            )
        detectors = [
            row.get("first_detector"),
            *row.get("additional_detectors", []),
        ]
        if any(
            detector is not None and detector not in EXPECTED_INVARIANT_FAMILIES
            for detector in detectors
        ):
            errors.append(
                f"publication evidence matrix row names an unknown detector: "
                f"{mutation_id}"
            )
        if not isinstance(row.get("description"), str) or not row["description"]:
            errors.append(
                f"publication evidence matrix row lacks a description: {mutation_id}"
            )

    m7 = mutations_by_id.get("M7", {})
    if m7.get("checks_before_rejection") != 639:
        errors.append("publication evidence M7 early-rejection count drifted")
    m8 = mutations_by_id.get("M8", {})
    if m8.get("gate_result") != "all_checks_passed":
        errors.append("publication evidence must preserve the M8 green-gate escape")

    rejected_ids = [
        row.get("id") for row in mutations if row.get("outcome") == "rejected"
    ]
    escaped_ids = [
        row.get("id") for row in mutations if row.get("outcome") == "escaped"
    ]
    summary = evaluation.get("summary", {})
    if summary.get("authored_mutation_count") != len(mutations):
        errors.append("publication evidence authored-mutation summary is not derived")
    if summary.get("rejected_mutation_count") != len(rejected_ids):
        errors.append("publication evidence rejected-mutation summary is not derived")
    if summary.get("escaped_mutation_ids") != escaped_ids:
        errors.append("publication evidence escaped-mutation summary is not derived")
    if summary.get("observed_detection_ratio") != "9/10":
        errors.append("publication evidence observed detection ratio drifted")
    if summary.get("coverage_depth_posture") != (
        "one_deep_coverage_not_family_depth"
    ):
        errors.append("publication evidence lost its one-deep coverage ceiling")

    post_repair = receipt.get("post_repair", {})
    if post_repair.get("intact_baseline_rechecked") is not True:
        errors.append("publication evidence lost the post-repair baseline recheck")
    if post_repair.get("rerun_mutation_ids") != ["M8"]:
        errors.append("publication evidence must preserve M8 as the only rerun mutation")
    if post_repair.get("other_original_mutations_rerun") is not False:
        errors.append("publication evidence must not claim the other mutations were rerun")
    if post_repair.get("post_repair_detection_ratio") is not None:
        errors.append("publication evidence must not report a post-repair ratio")
    if "no post-repair ten-of-ten" not in str(
        post_repair.get("claim_ceiling", "")
    ).lower():
        errors.append("publication evidence lost the post-repair ten-of-ten ceiling")

    threats = receipt.get("threats_to_validity", [])
    if not isinstance(threats, list) or len(threats) < 5:
        errors.append("publication evidence threats-to-validity record is incomplete")
    return errors


def all_entrypoints(
    claims: dict[str, Any], contract: dict[str, Any]
) -> list[dict[str, Any]]:
    return [
        *claims["machine_readable_paper"]["entrypoints"],
        *contract.get("entrypoints", []),
    ]


def build_research_frontier_route(
    reader: RepositoryReader, source: dict[str, Any]
) -> dict[str, Any]:
    """Project the indexed research frontier without promoting its status."""
    route = source.get("research_frontier_route")
    if not isinstance(route, dict):
        raise ValueError("publication entry research frontier route is missing")
    problem_id = route.get("problem_id")
    if not isinstance(problem_id, str) or not problem_id:
        raise ValueError("publication entry research frontier problem id is missing")
    problems = load_json(reader, PROBLEMS_PATH).get("problems", [])
    problem = next(
        (
            row
            for row in problems
            if isinstance(row, dict) and row.get("problem_id") == problem_id
        ),
        None,
    )
    if problem is None:
        raise ValueError(f"publication entry research problem is absent: {problem_id}")
    research = problem.get("research_corpus")
    if not isinstance(research, dict):
        raise ValueError(f"publication entry research corpus is absent: {problem_id}")
    indexed_files = research.get("files")
    if not isinstance(indexed_files, dict):
        raise ValueError("publication entry research corpus files are absent")
    files: dict[str, dict[str, str]] = {}
    for key in ("frontier", "strongest_results", "manifest", "checkpoint"):
        indexed = indexed_files.get(key)
        if not isinstance(indexed, dict):
            raise ValueError(f"publication entry research file is absent: {key}")
        raw_path = indexed.get("path")
        if not isinstance(raw_path, str) or not raw_path:
            raise ValueError(f"publication entry research file path is invalid: {key}")
        relative = Path(raw_path)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"publication entry research file escapes root: {raw_path}")
        digest = sha256(reader.read_bytes(raw_path))
        if digest != indexed.get("content_digest"):
            raise ValueError(f"publication entry research file is stale: {raw_path}")
        files[key] = {"path": raw_path, "content_digest": digest}
    summary = research.get("strongest_result_summary")
    checkpoint = research.get("checkpoint_summary")
    if not isinstance(summary, dict) or not isinstance(checkpoint, dict):
        raise ValueError("publication entry research summaries are absent")
    reading_order = route.get("reading_order")
    if not isinstance(reading_order, list) or not reading_order:
        raise ValueError("publication entry research reading order is missing")
    return {
        "problem_id": problem_id,
        "query": route.get("query"),
        "directory": research.get("directory"),
        "authority_posture": research.get("authority_posture"),
        "reading_rule": research.get("reading_rule"),
        "reading_order": list(reading_order),
        "files": files,
        "strongest_result_summary": copy.deepcopy(summary),
        "checkpoint_summary": copy.deepcopy(checkpoint),
        "source_index": {
            "path": PROBLEMS_PATH,
            "content_digest": sha256(reader.read_bytes(PROBLEMS_PATH)),
        },
        "promotion_boundary": route.get("promotion_boundary"),
    }


def build_publication_entry_packet(reader: RepositoryReader) -> dict[str, Any]:
    """Build the bounded agent packet from canonical publication owners."""
    source = load_json(reader, ENTRY_SOURCE_PATH)
    contract = load_json(reader, CONTRACT_PATH)
    evidence = load_json(reader, EVIDENCE_PATH)
    claims = load_json(reader, CLAIMS_PATH)
    mutation_manifest = load_json(reader, MUTATION_MANIFEST_PATH)

    systems_artifact = next(
        row
        for row in contract["artifacts"]
        if row["id"] == "repository_architecture_guide"
    )
    release = claims["release"]
    evaluation = evidence["evaluation"]
    current_assembly = claims["machine_readable_paper"]["publication_assembly"]
    current_snapshot = {
        "snapshot_kind": "current_canonical_owners",
        "curated_claim_count": len(claims["claims"]),
        "contribution_family_count": len(
            current_assembly["contribution_families"]
        ),
        "status_count": len(claims["status_taxonomy"]),
        "remaining_open_proposition_count": len(
            claims["remaining_open_propositions"]
        ),
    }
    research_frontier = build_research_frontier_route(reader, source)

    owner_paths = [
        ENTRY_SOURCE_PATH,
        CONTRACT_PATH,
        EVIDENCE_PATH,
        CLAIMS_PATH,
        METHODOLOGY_PATH,
        MUTATION_MANIFEST_PATH,
        MUTATION_HARNESS_PATH,
        PROBLEMS_PATH,
        systems_artifact["source_path"],
        systems_artifact["rendered_path"],
        *[row["path"] for row in research_frontier["files"].values()],
    ]
    content_hashes = {
        path: sha256(reader.read_bytes(path))
        for path in sorted(set(owner_paths))
    }

    provenance = evidence["provenance"]
    exact_target_ids = [
        row["id"]
        for row in mutation_manifest["operators"]
        if row.get("exact_original_target_registered") is True
    ]
    active_residuals: list[dict[str, Any]] = []
    if provenance.get("raw_run_logs_registered") is not True:
        active_residuals.append(
            {
                "id": "original_raw_mutation_logs_absent",
                "kind": "evidence_boundary",
                "status": "known_absence",
                "statement": (
                    "The original mutation run logs are not registered; "
                    "historical timings remain a structured transcription."
                ),
                "reentry_condition": (
                    "Register authenticated original logs and bind their "
                    "content identities before changing this boundary."
                ),
            }
        )
    if len(exact_target_ids) != len(mutation_manifest["operators"]):
        active_residuals.append(
            {
                "id": "exact_original_mutation_targets_partial",
                "kind": "evidence_boundary",
                "status": "known_absence",
                "statement": (
                    "Only the explicitly named mutation operators preserve "
                    "exact original targets; the remaining targets are "
                    "deterministic reconstructions."
                ),
                "exact_original_target_count": len(exact_target_ids),
                "reentry_condition": (
                    "Recover and authenticate an original target before "
                    "marking another operator exact."
                ),
            }
        )
    if evidence["post_repair"].get("other_original_mutations_rerun") is not True:
        active_residuals.append(
            {
                "id": "historical_post_repair_full_rerun_absent",
                "kind": "evaluation_boundary",
                "status": "not_run",
                "statement": (
                    "The historical study did not rerun the other nine "
                    "deliberately altered copies after the false README "
                    "edit was repaired."
                ),
                "reentry_condition": (
                    "Keep later deterministic reconstructions separate from "
                    "the historical result unless the original experiment is "
                    "rerun with equivalent targets and archived logs."
                ),
            }
        )
    active_residuals.extend(copy.deepcopy(source.get("manual_residuals", [])))

    commands = list(source["validation_commands"])
    for command in contract.get("reproducibility", {}).values():
        if command not in commands:
            commands.append(command)

    return {
        "schema": ENTRY_PACKET_SCHEMA,
        "artifact_role": "generated_bounded_agent_entry_projection",
        "authority_posture": (
            "navigation_projection_not_Lean_proof_authority_and_not_"
            "historical_evidence_authority"
        ),
        "architecture_summary": {
            "purpose": source["thesis"],
            "five_parts": [
                "Lean source",
                "human-reviewed public claims",
                "authored reader documents",
                "generated navigation views",
                "release checks and GitHub continuous integration",
            ],
            "decision_boundary": (
                "Lean checks formal proofs; people review public meaning; "
                "release software preserves only relationships that people "
                "explicitly recorded."
            ),
            "human_start": "ARCHITECTURE.md",
            "printable_start": systems_artifact["rendered_path"],
        },
        "thesis": source["thesis"],
        "five_sentence_summary": source["five_sentence_summary"],
        "revision_and_identity": {
            "release_version": release["version"],
            "release_tag": release["tag"],
            "release_date": release["date"],
            "lean_toolchain": release["lean_toolchain"],
            "repository": release["repository"],
            "formal_source": release["formal_source"],
            "evaluation_checkpoint": evaluation["checkpoint"],
            "current_checkout_revision_command": "git rev-parse HEAD",
            "revision_embedding_boundary": (
                "A tracked file cannot contain its own Git commit id without "
                "self-reference. Content freshness is enforced by the owner "
                "hashes below; agents query the checkout revision at runtime."
            ),
        },
        "public_claims": source["publication_claims"],
        "publication_non_claims": source["publication_non_claims"],
        "registered_mathematical_non_claims": claims["non_claims"],
        "remaining_open_propositions": claims["remaining_open_propositions"],
        "research_frontier": research_frontier,
        "authority_map": {
            "nodes": source["authority_nodes"],
            "edges": source["authority_edges"],
        },
        "historical_checker_example": {
            "purpose": (
                "Illustrate the boundary of explicitly recorded checks; "
                "this is not an architecture component or reliability score."
            ),
            "plain_result": (
                "One false README edit passed because its public claim had "
                "not been recorded. After the claim was recorded, the intact "
                "text passed and the same false edit failed."
            ),
            "evidence_owner": EVIDENCE_PATH,
            "summary_query": (
                "python3 scripts/query_corpus.py --publication-evidence summary"
            ),
            "current_owner_snapshot": current_snapshot,
        },
        "known_limitations": evidence["threats_to_validity"],
        "historical_evidence_residuals": active_residuals,
        "artifact_owners": {
            "publication_artifact_id": systems_artifact["id"],
            "source_path": systems_artifact["source_path"],
            "rendered_path": systems_artifact["rendered_path"],
            "publication_contract": CONTRACT_PATH,
            "publication_evidence": EVIDENCE_PATH,
            "mutation_manifest": MUTATION_MANIFEST_PATH,
            "mutation_harness": MUTATION_HARNESS_PATH,
            "entry_source": ENTRY_SOURCE_PATH,
            "entry_packet": ENTRY_PACKET_PATH,
        },
        "content_hashes": content_hashes,
        "validation_commands": commands,
        "packet_contract": {
            "max_bytes": source["packet_max_bytes"],
            "freshness_check": (
                "python3 scripts/build_publication_entry_packet.py --check"
            ),
            "agent_entry_owner": AGENT_ENTRY_PATH,
        },
    }


def validate_publication_entry_packet(
    reader: RepositoryReader,
    *,
    source_override: dict[str, Any] | None = None,
    packet_override: dict[str, Any] | None = None,
) -> list[str]:
    """Validate generation, boundedness, and actual agent-entry wiring."""
    errors: list[str] = []
    try:
        source = source_override or load_json(reader, ENTRY_SOURCE_PATH)
    except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
        return [f"{ENTRY_SOURCE_PATH}: {error}"]
    try:
        packet_bytes = (
            canonical_json_bytes(packet_override)
            if packet_override is not None
            else reader.read_bytes(ENTRY_PACKET_PATH)
        )
        packet = packet_override or json.loads(packet_bytes)
    except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
        return [f"{ENTRY_PACKET_PATH}: {error}"]

    if source.get("schema") != ENTRY_SOURCE_SCHEMA:
        errors.append(f"{ENTRY_SOURCE_PATH} must use schema {ENTRY_SOURCE_SCHEMA}")
    if source.get("packet_path") != ENTRY_PACKET_PATH:
        errors.append("publication entry source points at the wrong packet path")
    if packet.get("schema") != ENTRY_PACKET_SCHEMA:
        errors.append(f"{ENTRY_PACKET_PATH} must use schema {ENTRY_PACKET_SCHEMA}")
    if len(source.get("five_sentence_summary", [])) != 5:
        errors.append("publication entry source must contain exactly five summary sentences")
    if len(source.get("publication_claims", [])) < 4:
        errors.append("publication entry source must retain the four evidence claims")
    if not source.get("publication_non_claims"):
        errors.append("publication entry source must retain explicit non-claims")
    max_bytes = source.get("packet_max_bytes")
    if not isinstance(max_bytes, int) or max_bytes <= 0:
        errors.append("publication entry packet byte budget is invalid")
    elif len(packet_bytes) > max_bytes:
        errors.append(
            f"publication entry packet exceeds its {max_bytes}-byte budget: "
            f"{len(packet_bytes)}"
        )

    if not errors:
        expected = build_publication_entry_packet(
            RepositoryReader(
                reader.root,
                reader.git_ref,
                {
                    ENTRY_SOURCE_PATH: canonical_json_bytes(source),
                }
                if source_override is not None
                else None,
            )
        )
        if packet != expected:
            errors.append(
                "publication entry packet is stale; run "
                "python3 scripts/build_publication_entry_packet.py"
            )

    try:
        agent_entry = reader.read_text(AGENT_ENTRY_PATH)
    except (FileNotFoundError, UnicodeError) as error:
        errors.append(f"{AGENT_ENTRY_PATH}: {error}")
    else:
        for required in (
            ENTRY_PACKET_PATH,
            "python3 scripts/build_publication_entry_packet.py --check",
        ):
            if required not in agent_entry:
                errors.append(
                    f"{AGENT_ENTRY_PATH} does not load or validate the "
                    f"publication entry packet: missing {required}"
                )
    return errors


def manuscript_title(source_text: str) -> str | None:
    """The rendered title a reader sees, read from the manuscript's own ``\\title``.

    Brace-matched rather than regex-terminated, because a title may contain
    braces. Returns ``None`` when no title can be read, which is not an error
    here: an unparseable title is a weaker signal than a wrong one.
    """
    match = re.search(r"\\title\{", source_text)
    if match is None:
        return None
    depth, index = 1, match.end()
    start = index
    while index < len(source_text) and depth:
        if source_text[index] == "{":
            depth += 1
        elif source_text[index] == "}":
            depth -= 1
        index += 1
    if depth:
        return None
    return source_text[start : index - 1]


def comparable_title(text: str) -> str:
    """Reduce a title to what a reader sees, so LaTeX spelling is not a diff.

    ``\\\\`` is a line break inside a title, not a word boundary; ``$3/2$``
    renders as ``3/2``; and the two apostrophes are the same character to a
    reader. Comparing raw strings would report those as drift and train the
    next person to ignore this check.
    """
    text = re.sub(r"\\\\", " ", text).replace("$", "")
    text = text.replace("\\H{o}", "ő").replace("\\H o", "ő")
    text = re.sub(r"\\[A-Za-z]+\s*", "", text)
    text = text.replace("{", "").replace("}", "").replace("\u2019", "'")
    return re.sub(r"\s+", " ", text).strip().casefold()


def manuscript_title_errors(
    reader: RepositoryReader, artifacts: list[dict[str, Any]]
) -> list[str]:
    """Refuse a contract that titles a manuscript differently from the manuscript.

    The contract's ``title`` is what ``docs/problems.json``, the external
    verification packet, and the public site all print for a paper, so a stale
    one labels a link with one title and opens a PDF with another -- and a
    reader cannot tell which is the real paper. Earned 2026-08-14: eight of the
    thirteen registered titles had drifted from their own ``\\title`` after the
    manuscripts were retitled, and nothing here compared them.
    """
    errors: list[str] = []
    for artifact in artifacts:
        source = artifact.get("source_path")
        declared = artifact.get("title")
        if not isinstance(source, str) or not source.endswith(".tex"):
            continue
        if not isinstance(declared, str):
            continue
        try:
            source_text = reader.read_text(source)
        except (FileNotFoundError, UnicodeError):
            continue
        actual = manuscript_title(source_text)
        if actual is None:
            continue
        if comparable_title(actual) != comparable_title(declared):
            errors.append(
                f"artifact {artifact.get('id')!r} is titled {declared!r} but "
                f"{source} carries {' '.join(actual.split())!r}"
            )
    return errors


def validate_publication_contract(
    reader: RepositoryReader,
    *,
    contract_override: dict[str, Any] | None = None,
    claims_override: dict[str, Any] | None = None,
    evidence_override: dict[str, Any] | None = None,
) -> list[str]:
    errors: list[str] = []

    try:
        contract = contract_override or load_json(reader, CONTRACT_PATH)
    except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
        return [f"{CONTRACT_PATH}: {error}"]
    try:
        claims = claims_override or load_json(reader, CLAIMS_PATH)
    except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
        return [f"{CLAIMS_PATH}: {error}"]

    if contract.get("schema") != SCHEMA:
        errors.append(f"{CONTRACT_PATH} must use schema {SCHEMA}")
    if contract.get("authority_posture") != (
        "publication_metadata_and_evidence_boundary_not_Lean_proof_authority"
    ):
        errors.append("publication contract authority posture drifted")

    artifacts = contract.get("artifacts")
    if not isinstance(artifacts, list) or not artifacts:
        return [*errors, "publication contract must contain artifacts"]

    artifact_ids = [row.get("id") for row in artifacts]
    source_paths = [row.get("source_path") for row in artifacts]
    rendered_paths = [row.get("rendered_path") for row in artifacts]
    if len(artifact_ids) != len(set(artifact_ids)):
        errors.append("publication contract contains duplicate artifact ids")
    if len(source_paths) != len(set(source_paths)):
        errors.append("publication contract contains duplicate source paths")
    if len(rendered_paths) != len(set(rendered_paths)):
        errors.append("publication contract contains duplicate rendered paths")
    errors.extend(manuscript_title_errors(reader, artifacts))

    route_ids = {
        row.get("id") for row in all_entrypoints(claims, contract) if row.get("id")
    }
    for artifact in artifacts:
        artifact_id = artifact.get("id", "<unknown>")
        missing = REQUIRED_ARTIFACT_FIELDS - set(artifact)
        if missing:
            errors.append(
                f"publication artifact {artifact_id!r} lacks fields: {sorted(missing)}"
            )
            continue
        source = artifact["source_path"]
        rendered = artifact["rendered_path"]
        if not source.startswith("paper/") or not source.endswith(".tex"):
            errors.append(
                f"publication artifact {artifact_id!r} has invalid source path {source!r}"
            )
        if "/" in rendered or not rendered.endswith(".pdf"):
            errors.append(
                f"publication artifact {artifact_id!r} has invalid rendered path {rendered!r}"
            )
        for relative, digest_field in (
            (source, "source_content_digest"),
            (rendered, "rendered_content_digest"),
        ):
            if not reader.exists(relative):
                errors.append(
                    f"publication artifact {artifact_id!r} path does not exist: {relative}"
                )
                continue
            actual = sha256(reader.read_bytes(relative))
            if artifact[digest_field] != actual:
                errors.append(
                    f"publication artifact {artifact_id!r} {digest_field} drifted: "
                    f"expected {artifact[digest_field]}, actual {actual}"
                )
        try:
            source_text = reader.read_text(source)
        except (FileNotFoundError, UnicodeError):
            pass
        else:
            errors.extend(manuscript_source_license_errors(source, source_text))
        if "not_Lean_proof_authority" not in artifact["authority_posture"]:
            errors.append(
                f"publication artifact {artifact_id!r} lost its Lean proof-authority boundary"
            )
        if artifact["entry_route_id"] not in route_ids:
            errors.append(
                f"publication artifact {artifact_id!r} names unknown entry route "
                f"{artifact['entry_route_id']!r}"
            )
        if not artifact["validation"] or not all(
            isinstance(command, str) and command.startswith("python3 scripts/")
            for command in artifact["validation"]
        ):
            errors.append(
                f"publication artifact {artifact_id!r} lacks repository validation commands"
            )

    try:
        built = makefile_papers(reader.read_text(MAKEFILE_PATH))
    except (FileNotFoundError, UnicodeError) as error:
        errors.append(f"{MAKEFILE_PATH}: {error}")
        built = set()
    registered_bases = {Path(path).stem for path in source_paths if isinstance(path, str)}
    if built != registered_bases:
        errors.append(
            "publication build coverage drifted: "
            f"missing_from_contract={sorted(built - registered_bases)}, "
            f"not_built={sorted(registered_bases - built)}"
        )

    reuse: dict[str, Any] | None = None
    try:
        reuse = tomllib.loads(reader.read_text(REUSE_PATH))
        licensed_pdfs = reuse_manuscript_pdfs(reuse)
    except (FileNotFoundError, UnicodeError, tomllib.TOMLDecodeError) as error:
        errors.append(f"{REUSE_PATH}: {error}")
        licensed_pdfs = set()
    registered_pdfs = {path for path in rendered_paths if isinstance(path, str)}
    if licensed_pdfs != registered_pdfs:
        errors.append(
            "publication licence coverage drifted: "
            f"missing_from_contract={sorted(licensed_pdfs - registered_pdfs)}, "
            f"not_CC_BY_licensed={sorted(registered_pdfs - licensed_pdfs)}"
        )
    if reuse is not None:
        errors.extend(reuse_manuscript_override_errors(reuse, registered_pdfs))

    contract_routes = contract.get("entrypoints", [])
    contract_route_ids = [row.get("id") for row in contract_routes]
    if len(contract_route_ids) != len(set(contract_route_ids)):
        errors.append("publication contract contains duplicate entry route ids")
    for route in contract_routes:
        route_id = route.get("id", "<unknown>")
        for field in (
            "id",
            "title",
            "intent",
            "read",
            "query_steps",
            "authority_owners",
            "adjacent_handle_classes",
        ):
            if not route.get(field):
                errors.append(
                    f"publication entry route {route_id!r} lacks required field {field!r}"
                )
        for relative in route.get("read", []):
            if not reader.exists(relative):
                errors.append(
                    f"publication entry route {route_id!r} read path is missing: {relative}"
                )
        for command in route.get("query_steps", []):
            if not command.startswith("python3 scripts/query_corpus.py --"):
                errors.append(
                    f"publication entry route {route_id!r} has an untyped query step: "
                    f"{command}"
                )

    architecture = claims["machine_readable_paper"]["publication_assembly"][
        "publication_architecture"
    ]
    by_class: dict[str, set[str]] = {}
    for artifact in artifacts:
        by_class.setdefault(artifact["artifact_class"], set()).add(
            artifact["source_path"]
        )
    if by_class.get("mathematical_gateway", set()) != {
        architecture["canonical_gateway"]["source"]
    }:
        errors.append("publication gateway drifted from docs/claims.json")
    retained_sources = {
        row["source"] for row in architecture.get("retained_companions", [])
    }
    if by_class.get("mathematical_companion", set()) != retained_sources:
        errors.append("publication mathematical companions drifted from docs/claims.json")
    systems_sources = {
        row["source"] for row in architecture.get("architecture_guides", [])
    }
    if by_class.get("repository_architecture_guide", set()) != systems_sources:
        errors.append("publication architecture guides drifted from docs/claims.json")
    agent_navigation_sources = {
        row["source"]
        for row in architecture.get("agent_native_guides", [])
    }
    if (
        by_class.get("agent_navigation_guide", set())
        != agent_navigation_sources
    ):
        errors.append(
            "publication agent-navigation guides drifted from docs/claims.json"
        )
    # A problem note expounds the expansion library, whose declarations carry no
    # reviewed claim status.  The class is compared like the others so that a
    # note cannot be shipped without a matching registry row, and its posture is
    # required to say in words that it is not proof authority for a public claim.
    problem_note_sources = {
        row["source"] for row in architecture.get("problem_series", [])
    }
    if by_class.get(NOTE_ARTIFACT_CLASS, set()) != problem_note_sources:
        errors.append("publication problem notes drifted from docs/claims.json")
    if problem_note_sources and not architecture.get("problem_series_boundary"):
        errors.append(
            "docs/claims.json ships problem notes without a problem_series_boundary"
        )
    for artifact in artifacts:
        if artifact.get("artifact_class") != NOTE_ARTIFACT_CLASS:
            continue
        if "unregistered_expansion_module" not in artifact.get("authority_posture", ""):
            errors.append(
                f"problem note {artifact.get('id')!r} lost its unregistered-module posture"
            )

    rejected_ids = set(contract.get("rejected_artifact_ids", []))
    registered_ids = set(artifact_ids)
    overlap = rejected_ids & registered_ids
    if overlap:
        errors.append(
            f"publication artifacts are both registered and rejected: {sorted(overlap)}"
        )
    claims_rejected = {
        row.get("id") for row in architecture.get("rejected_companions", [])
    }
    if "system_or_methodology_paper" in claims_rejected and systems_sources:
        errors.append(
            "docs/claims.json still rejects a system or methodology paper while "
            "a systems case study is shipped"
        )

    systems_artifacts = [
        row
        for row in artifacts
        if row.get("artifact_class") == "repository_architecture_guide"
    ]
    for artifact in systems_artifacts:
        evidence = artifact.get("evidence_boundary")
        if not isinstance(evidence, dict):
            errors.append(
                f"systems artifact {artifact['id']!r} lacks an evidence_boundary"
            )
            continue
        checkpoint = evidence.get("evaluation_checkpoint", "")
        unavailable_detail: str | None = None
        if not isinstance(checkpoint, str) or not re.fullmatch(
            r"[0-9a-f]{40}", checkpoint
        ):
            errors.append(
                f"systems artifact {artifact['id']!r} has an invalid evaluation checkpoint"
            )
        else:
            unavailable_detail = reader.git_object_unavailable_detail(checkpoint)
        if (
            isinstance(checkpoint, str)
            and re.fullmatch(r"[0-9a-f]{40}", checkpoint)
            and unavailable_detail is not None
        ):
            errors.append(
                f"systems artifact {artifact['id']!r} evaluation checkpoint "
                f"{unavailable_detail}"
            )
        if evidence.get("release_check_count_at_evaluation") != 5207:
            errors.append(
                "systems evidence must preserve the 5,207-check evaluation baseline"
            )
        if evidence.get("authored_mutation_count") != 10:
            errors.append("systems evidence must preserve the ten-mutation study size")
        if evidence.get("rejected_mutation_count") != 9:
            errors.append("systems evidence must preserve the nine rejected mutations")
        if evidence.get("escaped_mutation_id") != "M8":
            errors.append("systems evidence must preserve M8 as the escaped mutation")
        if evidence.get("post_repair_full_mutation_rerun") is not False:
            errors.append(
                "systems evidence must not claim a complete post-repair mutation rerun"
            )
        if "ten-of-ten" not in str(evidence.get("forbidden_inference", "")):
            errors.append(
                "systems evidence must explicitly forbid a post-repair ten-of-ten claim"
            )
        try:
            source_text = reader.read_text(artifact["source_path"])
        except (FileNotFoundError, UnicodeError) as error:
            errors.append(
                f"systems artifact {artifact['id']!r} evidence source is unreadable: "
                f"{error}"
            )
        else:
            errors.extend(validate_systems_evidence_source(artifact, source_text))
        evidence_path = artifact.get("evidence_receipt_path")
        evidence_digest = artifact.get("evidence_receipt_digest")
        if evidence_path != EVIDENCE_PATH:
            errors.append(
                f"systems artifact {artifact['id']!r} must register {EVIDENCE_PATH}"
            )
            continue
        if not isinstance(evidence_digest, str):
            errors.append(
                f"systems artifact {artifact['id']!r} lacks an evidence receipt digest"
            )
            continue
        try:
            receipt_bytes = reader.read_bytes(evidence_path)
            receipt = evidence_override or json.loads(receipt_bytes)
        except (FileNotFoundError, json.JSONDecodeError, UnicodeError) as error:
            errors.append(f"{EVIDENCE_PATH}: {error}")
            continue
        actual_digest = sha256(receipt_bytes)
        if evidence_digest != actual_digest:
            errors.append(
                f"systems artifact {artifact['id']!r} evidence receipt digest drifted: "
                f"expected {evidence_digest}, actual {actual_digest}"
            )
        errors.extend(validate_mutation_evidence_receipt(receipt, artifact, reader))

    errors.extend(validate_publication_entry_packet(reader))
    return errors


def mutation_fixture_failures(reader: RepositoryReader) -> list[str]:
    """Return fixture names whose known-bad mutation was not rejected."""
    contract = load_json(reader, CONTRACT_PATH)
    failures: list[str] = []

    checkpoint = "0" * 40
    shallow_message = RepositoryReader.git_object_unavailable_message(
        checkpoint,
        shallow=True,
    )
    if (
        checkpoint not in shallow_message
        or "`git fetch --unshallow origin`" not in shallow_message
        or "shallow clone" not in shallow_message
    ):
        failures.append("shallow_checkpoint_recovery_diagnostic")
    full_history_message = RepositoryReader.git_object_unavailable_message(
        checkpoint,
        shallow=False,
    )
    if full_history_message != f"{checkpoint} is absent":
        failures.append("missing_checkpoint_full_history_diagnostic")

    missing = copy.deepcopy(contract)
    missing["artifacts"] = [
        row
        for row in missing["artifacts"]
        if row["id"] != "repository_architecture_guide"
    ]
    if not validate_publication_contract(reader, contract_override=missing):
        failures.append("unregistered_built_systems_paper")

    duplicate = copy.deepcopy(contract)
    duplicate["artifacts"].append(copy.deepcopy(duplicate["artifacts"][0]))
    duplicate["artifacts"][-1]["id"] = "duplicate_gateway"
    if not validate_publication_contract(reader, contract_override=duplicate):
        failures.append("duplicate_publication_source")

    drift = copy.deepcopy(contract)
    drift["artifacts"][0]["source_content_digest"] = "sha256:" + "0" * 64
    if not validate_publication_contract(reader, contract_override=drift):
        failures.append("publication_digest_drift")

    reuse_text = reader.read_text(REUSE_PATH)
    precedence_anchor = 'precedence = "override"'
    ambiguous_reuse = reuse_text.replace(precedence_anchor, "", 1)
    if ambiguous_reuse == reuse_text:
        failures.append("publication_license_precedence_fixture_anchor_missing")
    else:
        overlay_reader = RepositoryReader(
            reader.root,
            reader.git_ref,
            {REUSE_PATH: ambiguous_reuse.encode("utf-8")},
        )
        if not validate_publication_contract(overlay_reader):
            failures.append("publication_license_override_precedence_removed")

    source_license_drift = copy.deepcopy(contract)
    gateway = next(
        row
        for row in source_license_drift["artifacts"]
        if row["artifact_class"] == "mathematical_gateway"
    )
    source_path = gateway["source_path"]
    original_source = reader.read_text(source_path)
    mutated_source = original_source.replace(
        f"{SPDX_LICENSE_HEADER}{MANUSCRIPT_LICENSE}",
        f"{SPDX_LICENSE_HEADER}Apache-2.0",
        1,
    )
    if mutated_source == original_source:
        failures.append("manuscript_source_license_fixture_anchor_missing")
    else:
        gateway["source_content_digest"] = sha256(mutated_source.encode("utf-8"))
        overlay_reader = RepositoryReader(
            reader.root,
            reader.git_ref,
            {source_path: mutated_source.encode("utf-8")},
        )
        if not validate_publication_contract(
            overlay_reader,
            contract_override=source_license_drift,
        ):
            failures.append("manuscript_source_relicensed_as_software")

    rejected = copy.deepcopy(contract)
    rejected["rejected_artifact_ids"].append("repository_architecture_guide")
    if not validate_publication_contract(reader, contract_override=rejected):
        failures.append("registered_and_rejected_artifact")

    inflated = copy.deepcopy(contract)
    systems = next(
        row
        for row in inflated["artifacts"]
        if row["id"] == "repository_architecture_guide"
    )
    systems["evidence_boundary"]["post_repair_full_mutation_rerun"] = True
    if not validate_publication_contract(reader, contract_override=inflated):
        failures.append("post_repair_ten_of_ten_inflation")

    checkpoint_drift = copy.deepcopy(contract)
    systems = next(
        row
        for row in checkpoint_drift["artifacts"]
        if row["id"] == "repository_architecture_guide"
    )
    systems["evidence_boundary"]["evaluation_checkpoint"] = (
        "a16aa24af5236b6508a34b8a4c4b41fdcf620a98"
    )
    if not validate_publication_contract(reader, contract_override=checkpoint_drift):
        failures.append("evaluation_checkpoint_source_drift")

    source_inflation = copy.deepcopy(contract)
    systems = next(
        row
        for row in source_inflation["artifacts"]
        if row["id"] == "repository_architecture_guide"
    )
    source_path = systems["source_path"]
    original_source = reader.read_text(source_path)
    limited_sentence = (
        "The evidence marks a coverage boundary, not a reliability score."
    )
    inflated_sentence = (
        "This example establishes a general reliability score for future errors."
    )
    if limited_sentence not in original_source:
        failures.append("post_repair_source_fixture_anchor_missing")
    else:
        mutated_source = original_source.replace(
            limited_sentence,
            inflated_sentence,
            1,
        )
        systems["source_content_digest"] = sha256(mutated_source.encode("utf-8"))
        overlay_reader = RepositoryReader(
            reader.root,
            reader.git_ref,
            {source_path: mutated_source.encode("utf-8")},
        )
        if not validate_publication_contract(
            overlay_reader,
            contract_override=source_inflation,
        ):
            failures.append("source_and_digest_ten_of_ten_inflation")

    evidence = load_json(reader, EVIDENCE_PATH)

    matrix_inflation = copy.deepcopy(evidence)
    m8 = next(
        row
        for row in matrix_inflation["evaluation"]["mutations"]
        if row["id"] == "M8"
    )
    m8["outcome"] = "rejected"
    m8["first_detector"] = "boundary_language"
    matrix_inflation["evaluation"]["summary"]["rejected_mutation_count"] = 10
    matrix_inflation["evaluation"]["summary"]["escaped_mutation_ids"] = []
    matrix_inflation["evaluation"]["summary"]["observed_detection_ratio"] = "10/10"
    if not validate_publication_contract(
        reader,
        evidence_override=matrix_inflation,
    ):
        failures.append("historical_matrix_ten_of_ten_inflation")

    detector_drift = copy.deepcopy(evidence)
    m3 = next(
        row
        for row in detector_drift["evaluation"]["mutations"]
        if row["id"] == "M3"
    )
    m3["first_detector"] = "byte_budgets"
    if not validate_publication_contract(
        reader,
        evidence_override=detector_drift,
    ):
        failures.append("historical_matrix_detector_drift")

    provenance_inflation = copy.deepcopy(evidence)
    provenance_inflation["provenance"]["raw_run_logs_registered"] = True
    if not validate_publication_contract(
        reader,
        evidence_override=provenance_inflation,
    ):
        failures.append("unbacked_raw_run_log_claim")

    snapshot_inflation = copy.deepcopy(evidence)
    snapshot_inflation["evaluation"]["corpus_snapshot"]["curated_claim_count"] = 98
    snapshot_inflation["evaluation"]["corpus_snapshot"][
        "contribution_family_count"
    ] = 21
    if not validate_publication_contract(
        reader,
        evidence_override=snapshot_inflation,
    ):
        failures.append("evaluation_snapshot_current_tree_conflation")

    packet = load_json(reader, ENTRY_PACKET_PATH)

    thesis_loss = copy.deepcopy(packet)
    thesis_loss["thesis"] = "The checks passed."
    if not validate_publication_entry_packet(reader, packet_override=thesis_loss):
        failures.append("publication_entry_thesis_loss")

    checkpoint_conflation = copy.deepcopy(packet)
    checkpoint_conflation["revision_and_identity"]["evaluation_checkpoint"] = (
        checkpoint_conflation["revision_and_identity"]["formal_source"]["ref"]
    )
    if not validate_publication_entry_packet(
        reader,
        packet_override=checkpoint_conflation,
    ):
        failures.append("publication_entry_checkpoint_conflation")

    owner_hash_drift = copy.deepcopy(packet)
    owner_hash_drift["content_hashes"][EVIDENCE_PATH] = "sha256:" + "0" * 64
    if not validate_publication_entry_packet(
        reader,
        packet_override=owner_hash_drift,
    ):
        failures.append("publication_entry_owner_hash_drift")

    residual_loss = copy.deepcopy(packet)
    residual_loss["historical_evidence_residuals"] = []
    if not validate_publication_entry_packet(reader, packet_override=residual_loss):
        failures.append("publication_entry_residual_loss")

    return failures
