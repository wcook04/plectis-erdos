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
    result = subprocess.run(
        ["git", "-C", str(root), "show", f"HEAD:{path}"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.stdout


def committed_head(root: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


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
    head = reconciliation.get("current_repository", {}).get("observed_head_before_product", "")
    if not HEX40.fullmatch(head):
        errors.append("current repository observation lacks a full commit")
    return errors


def static_requirement_errors(root: Path, reconciliation: dict[str, Any], showcase: dict[str, Any]) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    deficits: list[str] = []
    formalization = safe_text(root / "formalization.yaml", root=root)
    toolchain = safe_text(root / "lean-toolchain", root=root).strip()
    project_license = re.search(r'^  license:\s*["\']?([^"\'\s]+)', formalization, re.MULTILINE)
    version = re.search(r'^version:\s*["\']?([^"\'\s]+)', formalization, re.MULTILINE)
    tool_version = re.search(r"lean4:v([0-9]+)\.([0-9]+)\.([0-9]+)", toolchain)
    if not project_license or project_license.group(1) != "Apache-2.0":
        errors.append("formalization.yaml project.license is not Apache-2.0")
    if not (root / "LICENSE").is_file():
        errors.append("root LICENSE is missing")
    if not (root / "lakefile.toml").is_file() or not (root / "lake-manifest.json").is_file():
        errors.append("lakefile.toml and lake-manifest.json must both be present")
    if not (root / "ExternalVerification" / "Challenge.lean").is_file():
        errors.append("ExternalVerification/Challenge.lean is missing")
    if not (root / "ExternalVerification" / "Solution.lean").is_file():
        errors.append("ExternalVerification/Solution.lean is missing")
    if not tool_version or tuple(map(int, tool_version.groups())) < (4, 28, 0):
        errors.append("lean-toolchain is below Palomar's v4.28.0 minimum")

    if not version or version.group(1) != "v0.4":
        deficits.append("formalization_v04_metadata")
    if not re.search(r"^  responsible_maintainers:\s*$", formalization, re.MULTILINE):
        deficits.append("responsible_maintainers")
    if not re.search(r"^classification:\s*$", formalization, re.MULTILINE):
        deficits.append("classification_metadata")
    source_region = formalization.split("status:", 1)[0]
    bad_types = sorted(set(re.findall(r'^    type:\s*["\']([^"\']+)["\']', source_region, re.MULTILINE)) - SOURCE_TYPES)
    if bad_types:
        deficits.append("v04_source_relationship_vocabulary")

    selected = showcase.get("candidate_selection", {})
    selected_name = selected.get("declaration", "")
    roster = set(flatten_showcase(showcase))
    if selected_name not in roster:
        errors.append("selected showcase candidate is absent from the committed Comparator roster")
    source_file = root / selected.get("source_file", "")
    short_name = selected_name.rsplit(".", 1)[-1]
    if not source_file.is_file() or not re.search(
        rf"\btheorem\s+{re.escape(short_name)}\b",
        safe_text(source_file, root=root) if source_file.is_file() else "",
    ):
        errors.append("selected candidate does not resolve to its declared current Lean source")
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
    static_errors, deficits = static_requirement_errors(root, recon, showcase)
    errors.extend(static_errors)
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
