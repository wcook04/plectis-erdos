#!/usr/bin/env python3
"""Check the repository-local Palomar qualification product.

This checker is deliberately a qualification checker, not a Palomar
replacement.  It reads the committed Comparator configuration from HEAD so
that uncommitted sibling rows cannot silently become submission evidence.  A
truthful NOT_READY result is successful checker output when the report and its
recorded deficits agree.
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


PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)
SELECTION_AXES = {
    "mathematical_nontriviality",
    "consequence_and_endpoint_proximity",
    "mechanism_depth_and_natural_friction",
    "genuinely_distinct_content_and_independence",
    "external_review_value",
    "proof_digestion_value",
    "evidence_certainty",
    "overclaim_risk",
}
VALUE_DISPOSITIONS = {"selected", "represented", "deferred", "subordinate", "rejected", "long_tail"}
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
SOURCE_TYPES = {
    "paper",
    "book",
    "web discussion",
    "folklore",
    "original-proof",
    "other",
}
SOURCE_RELATIONSHIPS = {
    "formalizes",
    "adapts",
    "independently-proves",
    "background",
    "other",
}
PINNED_TAXONOMY_AUTHORITIES = {
    "taxonomies/arxiv-categories.json": {
        "url": "https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/e215b184d1b659e8e3e641162a7d63708678016f/taxonomies/arxiv-categories.json",
        "commit": "e215b184d1b659e8e3e641162a7d63708678016f",
        "sha256": "3b339cf140a914c50bab39b1c44df2437ce3984bd09bb2150fcb0edd60eda776",
    },
    "taxonomies/msc2020-codes.json": {
        "url": "https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/e215b184d1b659e8e3e641162a7d63708678016f/taxonomies/msc2020-codes.json",
        "commit": "e215b184d1b659e8e3e641162a7d63708678016f",
        "sha256": "b4de69f1f562da01e0f4580cecc0ab36098f5297bb7cdd669c8ec3b0d3606060",
    },
}
REPOSITORY_SIZE_LIMIT_BYTES = 500 * 1024 * 1024
CHALLENGE_SIZE_LIMIT_BYTES = 100 * 1024
CHALLENGE_LINE_LIMIT = 1000
CHALLENGE_WARNING_BYTES = 32 * 1024
CHALLENGE_WARNING_LINES = 300
FORMALIZATION_SIZE_LIMIT_BYTES = 256 * 1024
LICENSE_SIZE_LIMIT_BYTES = 1024 * 1024
COMPILED_ARTIFACT_SUFFIXES = (
    ".olean",
    ".ilean",
    ".a",
    ".bc",
    ".dll",
    ".dylib",
    ".o",
    ".obj",
    ".so",
    ".trace",
)
REQUIRED_REQUIREMENT_IDS = {
    "repository_source_envelope",
    "challenge_source_envelope",
    "lake_manifest_and_dependency_pins",
    "root_license",
    "formalization_file_envelope",
    "formalization_v04_metadata",
}


class UnsafeQualificationInput(ValueError):
    """A qualification input escaped its root or is not a regular file."""


def safe_text(path: Path, *, root: Path) -> str:
    """Read a qualification input through a no-follow regular-file descriptor."""
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(path))
    if candidate != root and root not in candidate.parents:
        raise UnsafeQualificationInput(
            f"qualification input escaped checkout: {candidate}"
        )
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeQualificationInput(
                f"symlinked qualification input: {candidate}"
            )
        if current == root:
            break
        if current.parent == current:
            raise UnsafeQualificationInput(
                f"qualification input escaped checkout: {candidate}"
            )
        current = current.parent
    if not candidate.is_file():
        raise UnsafeQualificationInput(
            f"qualification input is not a regular file: {candidate}"
        )

    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeQualificationInput(
            f"qualification input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeQualificationInput(
                f"qualification input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        try:
            return b"".join(chunks).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise UnsafeQualificationInput(
                f"qualification input is not UTF-8: {candidate}"
            ) from exc
    finally:
        os.close(descriptor)


def load_json(path: Path, *, root: Path) -> dict[str, Any]:
    value = json.loads(safe_text(path, root=root))
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def committed_bytes(root: Path, path: str) -> bytes:
    """Read a qualification input from the immutable repository HEAD."""
    result = subprocess.run(
        ["git", "-C", str(root), "show", f"HEAD:{path}"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.stdout


def committed_text(root: Path, path: str) -> str:
    """Decode a committed qualification input without consulting worktree dirt."""
    try:
        return committed_bytes(root, path).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"committed qualification input is not UTF-8: {path}") from exc


def committed_file_exists(root: Path, path: str) -> bool:
    """Report whether a regular qualification input exists in committed HEAD."""
    try:
        committed_bytes(root, path)
    except subprocess.CalledProcessError:
        return False
    return True


def committed_head(root: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


def committed_commit_is_ancestor(root: Path, commit: str) -> bool:
    """Require a recorded transport commit to be in the committed HEAD ancestry."""
    if not HEX40.fullmatch(commit):
        return False
    result = subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", commit, "HEAD"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.returncode == 0


def committed_tree_entries(root: Path) -> list[dict[str, Any]]:
    """Return the immutable HEAD tree with checkout-relevant blob sizes."""
    result = subprocess.run(
        ["git", "-C", str(root), "ls-tree", "-r", "-l", "-z", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    entries: list[dict[str, Any]] = []
    for record in result.stdout.split(b"\0"):
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, object_type, object_id, raw_size = metadata.split()
        entries.append(
            {
                "mode": mode.decode("ascii"),
                "object_type": object_type.decode("ascii"),
                "object_id": object_id.decode("ascii"),
                "size": None if raw_size == b"-" else int(raw_size),
                "path": raw_path.decode("utf-8"),
            }
        )
    return entries


def committed_lfs_pointer_paths(
    root: Path, entries: list[dict[str, Any]]
) -> list[str]:
    """Find Git LFS pointers without scanning every byte in the checkout."""
    paths_by_object: dict[str, list[str]] = {}
    for entry in entries:
        if entry["object_type"] != "blob" or int(entry["size"] or 0) > 4096:
            continue
        paths_by_object.setdefault(entry["object_id"], []).append(entry["path"])

    process = subprocess.Popen(
        ["git", "-C", str(root), "cat-file", "--batch"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert process.stdin is not None
    assert process.stdout is not None
    pointers: list[str] = []
    try:
        for object_id, paths in paths_by_object.items():
            process.stdin.write(f"{object_id}\n".encode("ascii"))
            process.stdin.flush()
            header = process.stdout.readline().decode("ascii").strip().split()
            if len(header) != 3 or header[1] != "blob":
                raise ValueError(f"unexpected git cat-file response for {object_id}")
            blob = process.stdout.read(int(header[2]))
            if process.stdout.read(1) != b"\n":
                raise ValueError(f"unterminated git cat-file response for {object_id}")
            if blob.startswith(b"version https://git-lfs.github.com/spec/v1\n"):
                pointers.extend(paths)
    finally:
        process.stdin.close()
        stderr = process.stderr.read() if process.stderr is not None else b""
        returncode = process.wait()
        if returncode != 0:
            raise subprocess.CalledProcessError(
                returncode, process.args, stderr=stderr
            )
    return sorted(pointers)


def _license_name(path: str) -> bool:
    if "/" in path:
        return False
    lowered = path.casefold()
    for base in ("license", "licence", "copying", "unlicense", "ofl"):
        if lowered == base or lowered in {
            f"{base}.md",
            f"{base}.markdown",
            f"{base}.txt",
        }:
            return True
    return False


def repository_intake_evidence(root: Path) -> dict[str, Any]:
    """Measure Palomar's official committed-source intake envelope."""
    entries = committed_tree_entries(root)
    by_path = {entry["path"]: entry for entry in entries}
    comparator = json.loads(committed_bytes(root, "verification/comparator.json"))
    challenge_path = comparator["challenge_module"].replace(".", "/") + ".lean"
    solution_path = comparator["solution_module"].replace(".", "/") + ".lean"
    challenge = committed_bytes(root, challenge_path)
    formalization = committed_bytes(root, "formalization.yaml")
    license_paths = sorted(entry["path"] for entry in entries if _license_name(entry["path"]))
    license_bytes = committed_bytes(root, license_paths[0]) if len(license_paths) == 1 else b""
    manifest = json.loads(committed_bytes(root, "lake-manifest.json"))
    git_packages = [row for row in manifest.get("packages", []) if row.get("type") == "git"]
    github_url = re.compile(r"^https://github\.com/[^/?#]+/[^/?#]+$")
    invalid_git_dependencies = sorted(
        str(row.get("name", "<unnamed>"))
        for row in git_packages
        if not github_url.fullmatch(str(row.get("url", "")))
        or not HEX40.fullmatch(str(row.get("rev", "")))
    )
    compiled_artifacts = sorted(
        entry["path"]
        for entry in entries
        if not entry["path"].startswith(".lake/")
        and entry["path"].casefold().endswith(COMPILED_ARTIFACT_SUFFIXES)
    )
    facts: dict[str, Any] = {
        "repository_size_bytes": sum(
            int(entry["size"] or 0)
            for entry in entries
            if entry["mode"] != "120000"
        ),
        "repository_size_limit_bytes": REPOSITORY_SIZE_LIMIT_BYTES,
        "git_submodules": sorted(
            entry["path"] for entry in entries if entry["mode"] == "160000"
        ),
        "git_lfs_pointers": committed_lfs_pointer_paths(root, entries),
        "compiled_artifacts": compiled_artifacts,
        "challenge_path": challenge_path,
        "challenge_regular": by_path.get(challenge_path, {}).get("mode") in {"100644", "100755"},
        "challenge_bytes": len(challenge),
        "challenge_lines": len(challenge.splitlines()),
        "challenge_size_limit_bytes": CHALLENGE_SIZE_LIMIT_BYTES,
        "challenge_line_limit": CHALLENGE_LINE_LIMIT,
        "solution_path": solution_path,
        "solution_regular": by_path.get(solution_path, {}).get("mode") in {"100644", "100755"},
        "formalization_bytes": len(formalization),
        "formalization_size_limit_bytes": FORMALIZATION_SIZE_LIMIT_BYTES,
        "formalization_utf8": True,
        "license_paths": license_paths,
        "license_regular": len(license_paths) == 1
        and by_path.get(license_paths[0], {}).get("mode") in {"100644", "100755"},
        "license_bytes": len(license_bytes),
        "license_size_limit_bytes": LICENSE_SIZE_LIMIT_BYTES,
        "license_utf8": True,
        "git_dependency_count": len(git_packages),
        "invalid_git_dependencies": invalid_git_dependencies,
    }
    try:
        formalization.decode("utf-8")
    except UnicodeDecodeError:
        facts["formalization_utf8"] = False
    try:
        license_bytes.decode("utf-8")
    except UnicodeDecodeError:
        facts["license_utf8"] = False
    facts["warnings"] = []
    if (
        facts["challenge_bytes"] > CHALLENGE_WARNING_BYTES
        or facts["challenge_lines"] > CHALLENGE_WARNING_LINES
    ):
        facts["warnings"].append(
            "Challenge exceeds Palomar's 32 KiB or 300-line auditability warning threshold"
        )
    return facts


def repository_intake_errors(facts: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if facts["repository_size_bytes"] > facts["repository_size_limit_bytes"]:
        errors.append("committed repository exceeds Palomar's 500 MiB source cap")
    if facts["git_submodules"]:
        errors.append("submitted repository contains Git submodules")
    if facts["git_lfs_pointers"]:
        errors.append("submitted repository contains Git LFS pointers")
    if facts["compiled_artifacts"]:
        errors.append("submitted repository contains forbidden compiled artifacts")
    if not facts["challenge_regular"] or not facts["solution_regular"]:
        errors.append("Challenge and Solution must resolve to regular committed Lean files")
    if facts["challenge_bytes"] > facts["challenge_size_limit_bytes"]:
        errors.append("Challenge exceeds Palomar's 100 KiB hard limit")
    if facts["challenge_lines"] > facts["challenge_line_limit"]:
        errors.append("Challenge exceeds Palomar's 1,000-line hard limit")
    if not facts["formalization_utf8"] or facts["formalization_bytes"] > facts[
        "formalization_size_limit_bytes"
    ]:
        errors.append("formalization.yaml violates Palomar's UTF-8/256 KiB envelope")
    if len(facts["license_paths"]) != 1:
        errors.append("repository must contain exactly one conventional root licence file")
    elif (
        not facts["license_regular"]
        or not facts["license_utf8"]
        or facts["license_bytes"] <= 0
        or facts["license_bytes"] > facts["license_size_limit_bytes"]
    ):
        errors.append("root licence violates Palomar's regular UTF-8/1 MiB envelope")
    if facts["invalid_git_dependencies"]:
        errors.append("lake-manifest.json contains Git dependencies without accepted URLs or full pins")
    return errors


def flatten_showcase(showcase: dict[str, Any]) -> list[str]:
    names: list[str] = []
    for row in showcase.get("frontier_by_problem", []):
        names.extend(row.get("comparator_declarations", []))
    return names


def roster_errors(
    root: Path,
    comparator: dict[str, Any],
    showcase: dict[str, Any],
    reconciliation: dict[str, Any],
) -> list[str]:
    errors: list[str] = []
    names = comparator.get("theorem_names")
    if not isinstance(names, list) or not names or not all(isinstance(n, str) for n in names):
        return ["Comparator theorem_names must be a nonempty string array"]
    if len(names) != len(set(names)):
        errors.append("Comparator theorem_names contains duplicates")
    allowed_keys = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms", "enable_nanoda"}
    unexpected = set(comparator) - allowed_keys
    if unexpected:
        errors.append(f"Comparator has unexpected keys: {sorted(unexpected)}")
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    if not required <= set(comparator):
        errors.append("Comparator is missing one or more required keys")
    if comparator.get("challenge_module") == comparator.get("solution_module"):
        errors.append("Challenge and Solution module names must be distinct")
    if comparator.get("permitted_axioms") != ["propext", "Quot.sound", "Classical.choice"]:
        errors.append("Comparator permitted_axioms does not equal Palomar's closed ceiling")

    showcase_names = showcase.get("source_authority", {}).get("comparator_roster")
    if not isinstance(showcase_names, list):
        showcase_names = flatten_showcase(showcase)
    if showcase_names != names:
        errors.append("showcase declaration order does not exactly equal committed Comparator order")
    grouped_names = flatten_showcase(showcase)
    if len(grouped_names) != len(set(grouped_names)):
        errors.append("showcase binds at least one Comparator declaration more than once")
    if set(grouped_names) != set(names):
        errors.append("problem crosswalk does not cover exactly the committed Comparator declarations")
    missing = sorted(set(names) - set(showcase_names))
    extra = sorted(set(showcase_names) - set(names))
    if missing:
        errors.append(f"showcase omits committed Comparator declarations: {missing}")
    if extra:
        errors.append(f"showcase invents declarations absent from committed Comparator: {extra}")
    problem_rows = showcase.get("frontier_by_problem", [])
    if [row.get("problem") for row in problem_rows] != list(PROBLEMS):
        errors.append("showcase must contain the eight problem programmes in canonical order")
    if set(row.get("problem") for row in problem_rows) != set(PROBLEMS):
        errors.append("showcase does not cover exactly the eight problem programmes")

    recorded = reconciliation.get("current_repository", {}).get("comparator", {})
    if recorded.get("theorem_name_count") != len(names):
        errors.append("reconciliation theorem_name_count disagrees with committed Comparator")
    expected_digest = recorded.get("committed_sha256")
    actual_digest = hashlib.sha256(committed_bytes(root, "verification/comparator.json")).hexdigest()
    if expected_digest != f"{actual_digest}":
        errors.append("reconciliation Comparator SHA-256 does not match HEAD:verification/comparator.json")
    if showcase.get("source_authority", {}).get("comparator_sha256") != actual_digest:
        errors.append("showcase Comparator SHA-256 does not match HEAD:verification/comparator.json")
    return errors


def authority_errors(reconciliation: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    authorities = reconciliation.get("official_authorities", [])
    if len(authorities) < 10:
        errors.append("official authority capture is unexpectedly incomplete")
    for row in authorities:
        if not HEX40.fullmatch(row.get("commit", "")):
            errors.append(f"authority {row.get('path')} lacks an immutable full commit")
        if not HEX64.fullmatch(row.get("sha256", "")):
            errors.append(f"authority {row.get('path')} lacks a 64-hex SHA-256 digest")
        if not str(row.get("url", "")).startswith("https://raw.githubusercontent.com/"):
            errors.append(f"authority {row.get('path')} is not bound to an immutable raw URL")
    by_path = {
        row.get("path"): row for row in authorities if isinstance(row, dict)
    }
    for path, expected in PINNED_TAXONOMY_AUTHORITIES.items():
        actual = by_path.get(path)
        if not actual:
            errors.append(f"official authority {path} is not pinned")
            continue
        for field in ("url", "commit", "sha256"):
            if actual.get(field) != expected[field]:
                errors.append(f"official authority {path} disagrees on {field}")
    head = reconciliation.get("current_repository", {}).get("observed_head_before_product", "")
    if not HEX40.fullmatch(head):
        errors.append("current repository observation lacks a full commit")
    requirement_ids = {
        row.get("id")
        for row in reconciliation.get("requirements", [])
        if isinstance(row, dict)
    }
    missing_requirements = sorted(REQUIRED_REQUIREMENT_IDS - requirement_ids)
    if missing_requirements:
        errors.append(
            f"Palomar requirement matrix omits official intake requirements: {missing_requirements}"
        )
    return errors


def candidate_selection_errors(
    comparator: dict[str, Any], showcase: dict[str, Any], root: Path | None = None
) -> list[str]:
    """Require an explicit, complete, source-backed value-selection record."""
    errors: list[str] = []
    if root is None:
        root = Path(__file__).resolve().parents[1]
    names = comparator.get("theorem_names", [])
    universe = showcase.get("candidate_universe")
    if not isinstance(universe, dict):
        return ["showcase lacks the authority-backed candidate universe"]
    universe_names = universe.get("declarations")
    if universe.get("authority") != "HEAD:docs/claims.json::external_verification_packet.review_matrix":
        errors.append("candidate universe is not bound to the committed claims review matrix")
    screen = universe.get("comparator_screen")
    if not isinstance(screen, dict):
        errors.append("candidate universe lacks its nested Comparator screen")
    else:
        if screen.get("authority") != "HEAD:verification/comparator.json":
            errors.append("nested Comparator screen is not bound to HEAD:verification/comparator.json")
        if screen.get("roster_field") != "candidate_universe.declarations":
            errors.append("nested Comparator screen does not identify its roster field")
        if screen.get("partition") != "candidate_value_dispositions.eligible_groups":
            errors.append("nested Comparator screen does not identify its exact partition")
        if screen.get("comparator_sha256") != showcase.get("source_authority", {}).get(
            "comparator_sha256"
        ):
            errors.append("nested Comparator screen digest disagrees with showcase authority")
    if not isinstance(universe_names, list) or universe_names != names:
        errors.append("nested Comparator screen roster does not exactly equal the committed Comparator roster")
    try:
        claims = json.loads(committed_bytes(root, "docs/claims.json"))
        review_matrix = claims["external_verification_packet"]["review_matrix"]
        review_rows = [
            row
            for group in review_matrix
            for row in group.get("families", [])
            if isinstance(row, dict)
        ]
    except (KeyError, TypeError, json.JSONDecodeError, subprocess.CalledProcessError):
        review_rows = []
        errors.append("candidate universe cannot read the committed claims review matrix")
    review_ids = [row.get("id") for row in review_rows]
    if universe.get("source_review_matrix_path") != "docs/claims.json::external_verification_packet.review_matrix":
        errors.append("source-landscape universe has the wrong review-matrix path")
    if universe.get("source_review_family_count") != len(review_rows):
        errors.append("source-landscape universe count disagrees with the committed review matrix")
    if universe.get("source_review_family_count_at_dispatch") != 60:
        errors.append("source-landscape universe does not preserve the 60-family dispatch baseline")
    expected_review_digest = hashlib.sha256(committed_bytes(root, "docs/claims.json")).hexdigest()
    if universe.get("source_review_matrix_sha256") != expected_review_digest:
        errors.append("source-landscape universe digest does not match the committed claims matrix")
    source_ids = universe.get("source_review_family_ids")
    if not isinstance(source_ids, list) or source_ids != review_ids:
        errors.append("source-landscape universe does not consume every committed review family in order")
    if not isinstance(universe.get("source_review_matrix_sha256"), str):
        errors.append("source-landscape universe lacks the committed review-matrix digest")
    source_contract = universe.get("source_family_disposition_contract")
    required_source_fields = {
        "disposition",
        "support_evidence",
        "contrary_evidence",
        "cheapest_probe",
        "stop_evidence",
        "hard_mechanism",
        "attribution",
        "limitations",
        "open_boundary",
    }
    expected_bindings = {
        "support_evidence": "source_review_row.summary",
        "contrary_evidence": "source_review_row.boundary",
        "cheapest_probe": "source_review_row.evidence_mode plus exact source-coordinate comparison",
        "stop_evidence": "source_review_row.boundary",
        "hard_mechanism": "source_review_row.summary",
        "attribution": "source_review_row.contribution_class",
        "limitations": "source_review_row.boundary",
        "open_boundary": "source_review_row.boundary",
    }
    if not isinstance(source_contract, dict):
        errors.append("source-landscape universe lacks its family evidence contract")
    else:
        if set(source_contract.get("required_fields", [])) != required_source_fields:
            errors.append("source-landscape family evidence contract is incomplete")
        if source_contract.get("field_bindings") != expected_bindings:
            errors.append("source-landscape family evidence bindings are not canonical")
    source_dispositions = universe.get("source_family_dispositions")
    if not isinstance(source_dispositions, dict) or set(source_dispositions) != set(review_ids):
        errors.append("source-landscape universe lacks one disposition for every review family")
    else:
        for row in review_rows:
            family_id = row.get("id")
            disposition = source_dispositions.get(family_id)
            if disposition not in VALUE_DISPOSITIONS:
                errors.append(f"source-landscape family {family_id} has an invalid disposition")
            if not row.get("summary") or not row.get("boundary"):
                errors.append(f"source-landscape family {family_id} lacks support or contrary evidence")
            if not row.get("evidence_mode") or not row.get("contribution_class"):
                errors.append(f"source-landscape family {family_id} lacks probe or attribution evidence")
        if any(not isinstance(family_id, str) for family_id in source_dispositions):
            errors.append("source-landscape family disposition IDs are invalid")

    discoveries = universe.get("targeted_theorem_forest_discoveries")
    expected_discoveries = {
        "first_harmonic_pivot",
        "actual_lcm_positive_corridor_top_edge",
        "certificate_completeness",
        "erdos1049_four_jet_pade_obstruction",
        "erdos251_integral_tail_classification",
        "erdos243_centered_state_recovery",
        "weighted_phase_carry_observer",
        "strict_prime_tail_orbit_gap",
        "erdos249_carry_anti_compression",
    }
    if not isinstance(discoveries, list) or {
        row.get("candidate_id") for row in discoveries if isinstance(row, dict)
    } != expected_discoveries:
        errors.append("targeted theorem-forest discoveries do not match the source-landscape queue")
    else:
        for row in discoveries:
            if row.get("disposition") not in VALUE_DISPOSITIONS:
                errors.append(f"targeted discovery {row.get('candidate_id')} has an invalid disposition")
            if not isinstance(row.get("source_landscape_record"), str):
                errors.append(f"targeted discovery {row.get('candidate_id')} lacks its source-landscape record")

    disposition_record = showcase.get("candidate_value_dispositions")
    if not isinstance(disposition_record, dict):
        errors.append("showcase lacks the candidate value-disposition record")
    else:
        groups = disposition_record.get("eligible_groups")
        if not isinstance(groups, list) or not groups:
            errors.append("candidate value-disposition record lacks eligible groups")
        else:
            grouped_names: list[str] = []
            for index, group in enumerate(groups, 1):
                if not isinstance(group, dict):
                    errors.append(f"candidate value-disposition group {index} is not an object")
                    continue
                disposition = group.get("disposition")
                if disposition not in VALUE_DISPOSITIONS:
                    errors.append(f"candidate value-disposition group {index} has an invalid disposition")
                declarations = group.get("declarations")
                if not isinstance(declarations, list) or not declarations:
                    errors.append(f"candidate value-disposition group {index} lacks declarations")
                else:
                    grouped_names.extend(declarations)
                    if not all(isinstance(name, str) and name.strip() for name in declarations):
                        errors.append(f"candidate value-disposition group {index} has invalid declarations")
                if not isinstance(group.get("reason"), str) or not group["reason"].strip():
                    errors.append(f"candidate value-disposition group {index} lacks reason")
            if len(grouped_names) != len(set(grouped_names)):
                errors.append("candidate value-disposition groups contain duplicate declarations")
            if set(grouped_names) != set(names):
                errors.append("candidate value-disposition groups do not partition Comparator")
            selected_groups = [group for group in groups if isinstance(group, dict) and group.get("disposition") == "selected"]
            if len(selected_groups) != 1 or selected_groups[0].get("declarations") != [
                showcase.get("candidate_selection", {}).get("declaration")
            ]:
                errors.append("candidate value-disposition selected group disagrees with candidate selection")

        landscape = disposition_record.get("source_landscape_candidates")
        if not isinstance(landscape, list) or not landscape:
            errors.append("candidate value-disposition record lacks source-landscape candidates")
        else:
            required_landscape = {
                "candidate_id",
                "family_id",
                "disposition",
                "comparator_eligibility",
                "queue_role",
                "source_declaration",
                "source_file",
                "source_anchor",
                "statement",
                "exact_hypotheses",
                "conclusion",
                "hard_mechanism",
                "attribution",
                "limitations",
                "reason",
                "reversal_evidence",
            }
            for index, row in enumerate(landscape, 1):
                if not isinstance(row, dict):
                    errors.append(f"source-landscape candidate {index} is not an object")
                    continue
                missing = sorted(field for field in required_landscape if not row.get(field))
                if missing:
                    errors.append(f"source-landscape candidate {index} lacks fields: {missing}")
                if row.get("disposition") not in VALUE_DISPOSITIONS:
                    errors.append(f"source-landscape candidate {index} has an invalid disposition")
                expected_family = {
                    "first_harmonic_pivot": "first_harmonic_pivot_decomposition",
                    "actual_lcm_positive_corridor_top_edge": "actual_lcm_orbit_separation",
                    "erdos257_boolean_mobius_exact_row_dynamics": "boolean_mobius_exact_row_dynamics",
                    "erdos257_half_membership_seam_classification": "half_membership_seam_classification",
                    "erdos249_fixed_precision_transport_no_go": "fixed_precision_transport_no_go",
                    "erdos251_coefficient_only_no_go": "coefficient_only_no_go",
                    "erdos243_negative_mass_recovery": "negative_mass_recovery",
                }.get(row.get("candidate_id"))
                if expected_family and row.get("family_id") != expected_family:
                    errors.append(
                        f"source-landscape candidate {index} merges or misnames its canonical family"
                    )
                eligibility = row.get("comparator_eligibility")
                if eligibility == "committed_source_faithful_transport":
                    if row.get("queue_role") != "source_landscape_review_with_committed_comparator_evidence":
                        errors.append(
                            f"source-landscape candidate {index} mislabels committed Comparator evidence"
                        )
                    if row.get("comparator_declaration") not in names:
                        errors.append(
                            f"source-landscape candidate {index} names a non-Comparator declaration"
                        )
                    supporting = row.get("supporting_comparator_declarations", [])
                    if not isinstance(supporting, list) or not all(
                        isinstance(declaration, str) and declaration in names
                        for declaration in supporting
                    ):
                        errors.append(
                            f"source-landscape candidate {index} names a non-Comparator supporting declaration"
                        )
                elif eligibility == "committed_source_transport_pending_comparator_registration":
                    if row.get("queue_role") != "source_landscape_review_not_comparator_evidence":
                        errors.append(
                            f"source-landscape candidate {index} mislabels pending Comparator admission"
                        )
                    if row.get("comparator_declaration"):
                        errors.append(
                            f"source-landscape candidate {index} pending transport must not name Comparator evidence"
                        )
                    transport_commit = row.get("source_transport_commit")
                    if not isinstance(transport_commit, str) or not committed_commit_is_ancestor(
                        root, transport_commit
                    ):
                        errors.append(
                            f"source-landscape candidate {index} lacks an ancestor source transport commit"
                        )
                    transport_files = row.get("source_transport_files")
                    if not isinstance(transport_files, list) or not transport_files or not all(
                        isinstance(path, str) and path.startswith("ExternalVerification/")
                        for path in transport_files
                    ):
                        errors.append(
                            f"source-landscape candidate {index} lacks transported ExternalVerification files"
                        )
                    transport_declarations = row.get("transport_declarations")
                    if not isinstance(transport_declarations, list) or not transport_declarations or not all(
                        isinstance(declaration, str) and declaration.startswith("Erdos249257.ExternalVerification.")
                        for declaration in transport_declarations
                    ):
                        errors.append(
                            f"source-landscape candidate {index} lacks exact transported declarations"
                        )
                    if not isinstance(row.get("transport_admission_boundary"), str) or not all(
                        token in row["transport_admission_boundary"]
                        for token in ("verification/comparator.json", "review matrix")
                    ):
                        errors.append(
                            f"source-landscape candidate {index} lacks the pending-admission boundary"
                        )
                elif eligibility == "source_landed_but_not_comparator_configured":
                    if row.get("queue_role") != "source_landscape_review_not_comparator_evidence":
                        errors.append(
                            f"source-landscape candidate {index} mislabels source-landscape-only review"
                        )
                    if row.get("comparator_declaration"):
                        errors.append(
                            f"source-landscape candidate {index} source-landscape row must not name Comparator evidence"
                        )
                else:
                    errors.append(f"source-landscape candidate {index} has invalid Comparator eligibility")

            candidate_ids = [
                row.get("candidate_id")
                for row in landscape
                if isinstance(row, dict)
            ]
            if len(candidate_ids) != len(set(candidate_ids)):
                errors.append("source-landscape candidates contain duplicate candidate IDs")
            expected_landscape_ids = {
                "actual_lcm_orbit_separation",
                "actual_foreign_residue_projection",
                "first_harmonic_pivot",
                "actual_lcm_positive_corridor_top_edge",
                "certificate_completeness",
                "erdos1049_four_jet_pade_obstruction",
                "erdos251_integral_tail_classification",
                "erdos243_centered_state_recovery",
                "weighted_phase_carry_observer",
                "strict_prime_tail_orbit_gap",
                "erdos257_boolean_mobius_carry",
                "erdos257_boolean_mobius_exact_row_dynamics",
                "erdos257_half_membership_seam_classification",
                "erdos249_carry_anti_compression",
                "erdos249_fixed_precision_transport_no_go",
                "erdos251_coefficient_only_no_go",
                "erdos251_small_mismatch_criterion",
                "erdos269_conditional_carry_escape",
                "erdos243_negative_mass_recovery",
            }
            if set(candidate_ids) != expected_landscape_ids:
                errors.append("source-landscape queue does not cover the admitted and targeted candidates")

    contract = showcase.get("selection_contract")
    if not isinstance(contract, dict):
        errors.append("showcase lacks the value-selection contract")
    else:
        axes = {
            row.get("axis")
            for row in contract.get("ranking_axes", [])
            if isinstance(row, dict)
        }
        missing_axes = sorted(SELECTION_AXES - axes)
        if missing_axes:
            errors.append(f"selection contract omits ranking axes: {missing_axes}")
        for field in (
            "authority_basis",
            "anti_underclaim_boundary",
            "anti_hype_boundary",
            "reversal_evidence",
        ):
            if not isinstance(contract.get(field), str) or not contract[field].strip():
                errors.append(f"selection contract lacks {field}")

    selected_record = showcase.get("candidate_selection")
    if not isinstance(selected_record, dict):
        errors.append("showcase lacks the selected candidate record")
    else:
        for field in (
            "declaration",
            "source_declaration",
            "source_file",
            "source_anchor",
            "statement",
            "conclusion",
            "open_boundary",
            "hard_mechanism",
            "why_this_is_the_showcase",
            "attribution",
        ):
            if not isinstance(selected_record.get(field), str) or not selected_record[field].strip():
                errors.append(f"selected candidate lacks exact {field}")
        for field in ("exact_hypotheses", "limitations"):
            values = selected_record.get(field)
            if (
                not isinstance(values, list)
                or not values
                or not all(isinstance(value, str) and value.strip() for value in values)
            ):
                errors.append(f"selected candidate lacks exact {field}")

    comparison = showcase.get("selection_comparison")
    if not isinstance(comparison, list) or not comparison:
        errors.append("showcase lacks nearest-alternative selection dispositions")
    else:
        for index, row in enumerate(comparison, 1):
            if not isinstance(row, dict):
                errors.append(f"selection comparison row {index} is not an object")
                continue
            for field in ("declaration", "family_id", "disposition", "reason"):
                if not isinstance(row.get(field), str) or not row[field].strip():
                    errors.append(f"selection comparison row {index} lacks {field}")
            if row.get("declaration") not in names:
                errors.append(
                    f"selection comparison row {index} names a declaration absent from Comparator"
                )

    ranking = showcase.get("candidate_ranking")
    if not isinstance(ranking, list) or not ranking:
        errors.append("showcase lacks a ranked candidate spine")
    else:
        ranks = [row.get("rank") for row in ranking if isinstance(row, dict)]
        if ranks != list(range(1, len(ranking) + 1)):
            errors.append("candidate ranking ranks are not consecutive from one")
        ranked_names = [row.get("declaration") for row in ranking if isinstance(row, dict)]
        if len(ranked_names) != len(set(ranked_names)):
            errors.append("candidate ranking contains duplicate declarations")
        if any(name not in names for name in ranked_names):
            errors.append("candidate ranking contains a declaration absent from Comparator")
        if isinstance(source_ids, list):
            ranked_family_ids = {
                row.get("family_id")
                for row in ranking
                if isinstance(row, dict) and isinstance(row.get("family_id"), str)
            }
            unknown_family_ids = sorted(ranked_family_ids - set(source_ids))
            if unknown_family_ids:
                errors.append(
                    "candidate ranking contains family IDs absent from the committed review matrix: "
                    + ", ".join(unknown_family_ids)
                )
        required_prose = {
            "mathematical_nontriviality",
            "consequence_and_endpoint_proximity",
            "mechanism_depth_and_natural_friction",
            "genuinely_distinct_content_and_independence",
            "external_review_value",
            "proof_digestion_value",
            "evidence_certainty",
            "overclaim_risk",
        }
        for index, row in enumerate(ranking, 1):
            if not isinstance(row, dict):
                errors.append(f"candidate ranking row {index} is not an object")
                continue
            missing = sorted(
                field
                for field in required_prose
                if not isinstance(row.get(field), str) or not row[field].strip()
            )
            if missing:
                errors.append(
                    f"candidate ranking row {index} lacks required prose: {missing}"
                )
            reason_field = "why_ranked_first" if index == 1 else "why_not_ranked_first"
            if not isinstance(row.get(reason_field), str) or not row[reason_field].strip():
                errors.append(f"candidate ranking row {index} lacks {reason_field}")
        selected_name = showcase.get("candidate_selection", {}).get("declaration")
        if ranking[0].get("declaration") != selected_name:
            errors.append("candidate selection does not match ranked candidate one")
        if ranking[0].get("selection_status") != "selected":
            errors.append("ranked candidate one is not marked selected")

    screening = showcase.get("candidate_screening")
    if not isinstance(screening, list) or not screening:
        errors.append("showcase lacks dispositions for non-headline Comparator rows")
    else:
        screening_names = []
        for index, row in enumerate(screening, 1):
            if not isinstance(row, dict):
                errors.append(f"candidate screening row {index} is not an object")
                continue
            screening_names.append(row.get("declaration"))
            for field in ("declaration", "family_id", "disposition", "reason"):
                if not isinstance(row.get(field), str) or not row[field].strip():
                    errors.append(f"candidate screening row {index} lacks {field}")
            if row.get("declaration") not in names:
                errors.append(
                    f"candidate screening row {index} names a declaration absent from Comparator"
                )
            expected_screening_family = {
                "Erdos249257.ExternalVerification.scaleFullTarget_miss_of_projected_separation":
                    "actual_foreign_residue_projection",
            }.get(row.get("declaration"))
            if expected_screening_family and row.get("family_id") != expected_screening_family:
                errors.append(
                    f"candidate screening row {index} misbinds its canonical family"
                )
        ranked_names = [row.get("declaration") for row in ranking or [] if isinstance(row, dict)]
        if len(screening_names) != len(set(screening_names)):
            errors.append("candidate screening contains duplicate declarations")
        if set(ranked_names) & set(screening_names):
            errors.append("candidate ranking and screening overlap")
        if set(ranked_names) | set(screening_names) != set(names):
            errors.append("candidate ranking and screening do not partition Comparator")
    return errors


def formalization_metadata_deficits(formalization: str) -> list[str]:
    """Apply the pinned PalomarSubmission v0.4 metadata/profile boundary."""
    deficits: list[str] = []
    version = re.search(r"^version:\s*[\"']?([^\"'\s]+)", formalization, re.MULTILINE)
    if not version or version.group(1) != "v0.4":
        deficits.append("formalization_v04_metadata")

    project_region = formalization.split("sources:", 1)[0]
    description = re.search(r"^  description:\s*(.*)$", project_region, re.MULTILINE)
    if not description or not description.group(1).strip() or len(description.group(1).strip()) > 10_000:
        deficits.append("project_description")
    if not re.search(
        r"^  authors:\s*$.*?^    -\s*\S.*?^  license:",
        project_region,
        re.MULTILINE | re.DOTALL,
    ):
        deficits.append("project_authors")
    if not re.search(
        r"^  responsible_maintainers:\s*$.*?^    -\s*\S",
        project_region,
        re.MULTILINE | re.DOTALL,
    ):
        deficits.append("responsible_maintainers")

    classification = re.search(
        r"^classification:\s*$((?:\n^  .*?$)*)",
        formalization,
        re.MULTILINE,
    )
    if not classification:
        deficits.append("classification_metadata")
    else:
        classification_region = classification.group(1)

        def list_values(field: str) -> list[str] | None:
            match = re.search(rf"^  {field}:\s*(.*)$", classification_region, re.MULTILINE)
            if not match:
                return None
            inline = match.group(1).strip()
            if inline.startswith("[") and inline.endswith("]"):
                return [value.strip().strip("\"'") for value in inline[1:-1].split(",") if value.strip()]
            tail = classification_region[match.end() :]
            return [
                value.strip().strip("\"'")
                for value in re.findall(r"^    -\s*(.*)$", tail, re.MULTILINE)
                if value.strip()
            ]

        arxiv = list_values("arxiv")
        msc2020 = list_values("msc2020")
        if (
            arxiv is None
            or not 1 <= len(arxiv) <= 8
            or len(arxiv) != len(set(arxiv))
            or msc2020 is None
            or len(msc2020) > 8
            or len(msc2020) != len(set(msc2020))
        ):
            deficits.append("classification_metadata")

    if not re.search(
        r"^automation:\s*$.*?^  methods:\s*$.*?^    - method:\s*\S",
        formalization,
        re.MULTILINE | re.DOTALL,
    ):
        deficits.append("automation_metadata")
    if not re.search(
        r"^review:\s*$.*?^  status:\s*\S",
        formalization,
        re.MULTILINE | re.DOTALL,
    ):
        deficits.append("review_metadata")

    source_region = formalization.split("sources:", 1)[-1].split("status:", 1)[0]
    source_entries: list[dict[str, str]] = []
    current: dict[str, str] | None = None
    for line in source_region.splitlines():
        if line.startswith("  - title:"):
            current = {"title": line.split(":", 1)[1].strip().strip("\"'")}
            source_entries.append(current)
        elif current is not None and line.startswith("    type:"):
            current["type"] = line.split(":", 1)[1].strip().strip("\"'")
        elif current is not None and line.startswith("    relationship:"):
            current["relationship"] = line.split(":", 1)[1].strip().strip("\"'")

    if not source_entries or any(
        not entry.get("title") or not entry.get("relationship") for entry in source_entries
    ):
        deficits.append("source_relationship_metadata")

    source_types = [entry.get("type", "") for entry in source_entries]
    relationship_values = [entry.get("relationship", "") for entry in source_entries]
    bad_types = sorted(set(source_type for source_type in source_types if source_type) - SOURCE_TYPES)
    bad_relationships = sorted(
        set(relationship for relationship in relationship_values if relationship)
        - SOURCE_RELATIONSHIPS
    )
    if bad_types or bad_relationships:
        deficits.append("v04_source_relationship_vocabulary")

    if source_entries and all(relationship_values):
        if any(source_type == "original-proof" for source_type in source_types):
            origin_ok = all(
                entry.get("relationship") == "other"
                for entry in source_entries
                if entry.get("type") == "original-proof"
            ) and all(
                entry.get("relationship") in {"background", "other"}
                for entry in source_entries
            )
        else:
            origin_ok = any(
                relationship in {"formalizes", "adapts", "independently-proves"}
                for relationship in relationship_values
            )
        if not origin_ok:
            deficits.append("source_origin_consistency")
    else:
        deficits.append("source_origin_consistency")
    return sorted(set(deficits))


def static_requirement_errors(root: Path, reconciliation: dict[str, Any], showcase: dict[str, Any]) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    deficits: list[str] = []
    # formalization.yaml is generated from the sibling-owned claims projection.
    # Qualification must never consume an uncommitted generated projection as
    # evidence; the owning source can land it, after which HEAD becomes the
    # qualification input.
    formalization = committed_text(root, "formalization.yaml")
    toolchain = committed_text(root, "lean-toolchain").strip()
    project_license = re.search(r'^  license:\s*["\']?([^"\'\s]+)', formalization, re.MULTILINE)
    tool_version = re.search(r"lean4:v([0-9]+)\.([0-9]+)\.([0-9]+)", toolchain)
    if not project_license or project_license.group(1) != "Apache-2.0":
        errors.append("formalization.yaml project.license is not Apache-2.0")
    if not committed_file_exists(root, "LICENSE"):
        errors.append("root LICENSE is missing")
    if not committed_file_exists(root, "lakefile.toml") or not committed_file_exists(
        root, "lake-manifest.json"
    ):
        errors.append("lakefile.toml and lake-manifest.json must both be present")
    if not committed_file_exists(root, "ExternalVerification/Challenge.lean"):
        errors.append("ExternalVerification/Challenge.lean is missing")
    if not committed_file_exists(root, "ExternalVerification/Solution.lean"):
        errors.append("ExternalVerification/Solution.lean is missing")
    if not tool_version or tuple(map(int, tool_version.groups())) < (4, 28, 0):
        errors.append("lean-toolchain is below Palomar's v4.28.0 minimum")

    intake = repository_intake_evidence(root)
    errors.extend(repository_intake_errors(intake))

    deficits.extend(formalization_metadata_deficits(formalization))

    selected = showcase.get("candidate_selection", {})
    selected_name = selected.get("declaration", "")
    roster = set(flatten_showcase(showcase))
    if selected_name not in roster:
        errors.append("selected showcase candidate is absent from the committed Comparator roster")
    source_path = selected.get("source_file", "")
    source_file = root / source_path
    short_name = selected_name.rsplit(".", 1)[-1]
    try:
        source_text = committed_text(root, source_path)
    except (OSError, ValueError, subprocess.CalledProcessError):
        source_text = ""
    source_short_name = selected.get("source_declaration", "").rsplit(".", 1)[-1]
    if not source_path or not source_text or not re.search(
        rf"\btheorem\s+{re.escape(short_name)}\b", source_text
    ):
        errors.append("selected candidate does not resolve to its declared current Lean source")
    if not source_short_name or not re.search(
        rf"\btheorem\s+{re.escape(source_short_name)}\b", source_text
    ):
        errors.append("selected candidate source_declaration does not resolve to its source theorem")
    for problem in PROBLEMS:
        row = next((r for r in showcase.get("frontier_by_problem", []) if r.get("problem") == problem), None)
        if not row or not row.get("frontier_summary") or not row.get("open_boundary"):
            errors.append(f"problem {problem} lacks a frontier and open-boundary account")
    return errors, deficits


def evaluate(root: Path) -> dict[str, Any]:
    recon = load_json(root / "docs/PALOMAR_POLICY_RECONCILIATION.json", root=root)
    showcase = load_json(root / "docs/PALOMAR_RESULT_SHOWCASE.json", root=root)
    comparator = json.loads(committed_bytes(root, "verification/comparator.json"))
    errors = authority_errors(recon)
    errors.extend(roster_errors(root, comparator, showcase, recon))
    errors.extend(candidate_selection_errors(comparator, showcase, root))
    selected = showcase.get("candidate_selection", {})
    recon_selection = recon.get("candidate_value_selection", {})
    if not isinstance(recon_selection, dict):
        errors.append("reconciliation lacks the Palomar candidate value-selection record")
    else:
        for field, expected in (
            ("showcase_path", "docs/PALOMAR_RESULT_SHOWCASE.json"),
            ("authority", "HEAD:verification/comparator.json"),
            ("selected_declaration", selected.get("declaration")),
            ("selected_source_declaration", selected.get("source_declaration")),
            ("selected_family_id", selected.get("family_id")),
        ):
            if recon_selection.get(field) != expected:
                errors.append(f"reconciliation candidate selection disagrees on {field}")
    static_errors, deficits = static_requirement_errors(root, recon, showcase)
    errors.extend(static_errors)
    repository_intake = repository_intake_evidence(root)
    decision = recon.get("qualification_decision", {}).get("decision")
    if deficits and decision != "NOT_READY":
        errors.append("qualification must remain NOT_READY while recorded structural deficits exist")
    if decision not in {"READY", "NOT_READY"}:
        errors.append("qualification decision must be READY or NOT_READY")
    return {
        "schema": "plectis-palomar-qualification-report/1",
        "decision": decision,
        "source_head": committed_head(root),
        "comparator_theorem_count": len(comparator.get("theorem_names", [])),
        "selected_candidate": showcase.get("candidate_selection", {}).get("declaration"),
        "structural_deficits": sorted(set(deficits)),
        "structural_warnings": repository_intake["warnings"],
        "repository_intake": repository_intake,
        "withheld_terminal_gates": ["mechanical_report", "independent_nanoda_replay", "editorial_review"],
        "operator_only_gates": ["submission_consent", "registration", "publication"],
        "errors": errors,
        "ok": not errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--json", action="store_true", help="emit the structured qualification report")
    args = parser.parse_args()
    try:
        report = evaluate(args.root.resolve())
    except (OSError, ValueError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
        report = {"schema": "plectis-palomar-qualification-report/1", "ok": False, "errors": [str(exc)]}
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"Palomar qualification: {report.get('decision', 'ERROR')}")
        print(f"Comparator declarations: {report.get('comparator_theorem_count', 0)}")
        if report.get("structural_deficits"):
            print("Structural deficits: " + ", ".join(report["structural_deficits"]))
        if report.get("errors"):
            for error in report["errors"]:
                print(f"ERROR: {error}")
    return 0 if report.get("ok") else 1


if __name__ == "__main__":
    sys.exit(main())
