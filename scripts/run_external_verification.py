#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Write and enforce the commit-bound external-verification runtime receipt."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_MISMATCH = (
    "Challenge and solution theorem statement do not match: "
    "'Erdos249257.ExternalVerification.finrank_totientKernelThroughLevelFamily_eq'"
)


def digest(path: Path | None) -> str | None:
    if path is None or not path.is_file():
        return None
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def is_expected_negative_rejection(exit_code: int, log_text: str) -> bool:
    return exit_code != 0 and EXPECTED_MISMATCH in log_text


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", default="final")
    parser.add_argument("--positive-exit", type=int, default=-999)
    parser.add_argument("--negative-exit", type=int, default=-999)
    parser.add_argument("--positive-log", type=Path)
    parser.add_argument("--negative-log", type=Path)
    parser.add_argument("--comparator-rev")
    parser.add_argument("--lean4export-rev")
    parser.add_argument("--landrun-rev")
    parser.add_argument("--comparator-bin", type=Path)
    parser.add_argument("--lean4export-bin", type=Path)
    parser.add_argument("--landrun-bin", type=Path)
    parser.add_argument("--comparator-lean-toolchain")
    parser.add_argument("--sandbox-mode")
    parser.add_argument(
        "--output", type=Path, default=ROOT / "artifacts/external-verification-receipt.json"
    )
    args = parser.parse_args()

    projection_check = subprocess.run(
        ["python3", "scripts/build_external_verification.py", "--check"], cwd=ROOT
    ).returncode
    claims = json.loads((ROOT / "docs/claims.json").read_text(encoding="utf-8"))
    owner = claims["external_verification_packet"]
    packet = json.loads(
        (ROOT / "docs/external_verification_packet.json").read_text(encoding="utf-8")
    )
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    observed_revisions = {
        "comparator": args.comparator_rev,
        "lean4export": args.lean4export_rev,
        "landrun": args.landrun_rev,
    }
    binary_digests = {
        "comparator": digest(args.comparator_bin),
        "lean4export": digest(args.lean4export_bin),
        "landrun": digest(args.landrun_bin),
    }
    pins_match = observed_revisions == owner["comparator"]["pins"]
    negative_text = (
        args.negative_log.read_text(encoding="utf-8", errors="replace")
        if args.negative_log is not None and args.negative_log.is_file()
        else ""
    )
    negative_semantic_rejection = is_expected_negative_rejection(
        args.negative_exit, negative_text
    )
    all_statuses_open = all(
        row["status"] == "open" for row in packet["problem_index"]["problems"]
    )
    passed = (
        projection_check == 0
        and args.positive_exit == 0
        and negative_semantic_rejection
        and pins_match
        and all(binary_digests.values())
        and args.sandbox_mode in {"user-manager", "system-manager-nonprivileged-unit", "local-fake-landrun-smoke"}
        and all_statuses_open
    )
    receipt = {
        "schema": "erdos-external-verification-runtime-receipt/1",
        "result": "pass" if passed else "fail",
        "phase": args.phase,
        "repository_commit": git("rev-parse", "HEAD"),
        "repository_tree": git("rev-parse", "HEAD^{tree}"),
        "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "ci": {
            "repository": os.environ.get("GITHUB_REPOSITORY"),
            "run_id": os.environ.get("GITHUB_RUN_ID"),
            "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
            "workflow": os.environ.get("GITHUB_WORKFLOW"),
            "sandbox_mode": args.sandbox_mode,
        },
        "proof_environment": {
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "mathlib_revision": mathlib["rev"],
        },
        "comparator_toolchain": {
            "expected_revisions": owner["comparator"]["pins"],
            "observed_revisions": observed_revisions,
            "revisions_match": pins_match,
            "comparator_lean_toolchain": args.comparator_lean_toolchain,
            "binary_digests": binary_digests,
        },
        "whole_programme_disclosure": {
            "scope": owner["scope"],
            "problem_index": packet["problem_index"]["projection"],
            "problem_index_digest": packet["problem_index"]["projection_digest"],
            "problem_count": packet["problem_index"]["problem_count"],
            "problem_ids": owner["problem_ids"],
            "all_statuses_open": all_statuses_open,
        },
        "statement_contract": {
            "config": owner["comparator"]["config"],
            "config_digest": packet["config_digest"],
            "challenge_import_closure": packet["challenge_import_closure"],
            "trusted_build_inputs": packet["trusted_build_inputs"],
            "theorem_names": [row["wrapper_declaration"] for row in owner["main_results"]],
            "permitted_axioms": owner["comparator"]["permitted_axioms"],
        },
        "checks": {
            "projection_and_isolation_check_exit": projection_check,
            "positive_comparator_exit": args.positive_exit,
            "positive_log_digest": digest(args.positive_log),
            "negative_mismatch_comparator_exit": args.negative_exit,
            "negative_log_digest": digest(args.negative_log),
            "negative_fixture_rejected": negative_semantic_rejection,
            "negative_expected_diagnostic": EXPECTED_MISMATCH,
        },
    }
    output = args.output if args.output.is_absolute() else ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(output)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
