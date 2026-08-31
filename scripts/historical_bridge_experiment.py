#!/usr/bin/env python3
"""Run one leakage-resistant historical bridge evaluation.

The experiment checks out the parent of the bridge-introduction commit in a
disposable local clone, builds only the pre-existing dependency target, asks
the proof-state compiler for the exact obstruction, and checks an anonymised
bridge candidate with that historical Lean environment.  Current-history
reuse is measured only after the blind proof run and is never imported into
the historical checkout.

This is a historical shadow evaluator, not a claim of autonomous lemma
invention.  The candidate proof is an authored reconstruction whose utility
and admissibility are tested under a real pre-introduction environment.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any

import proof_state_compiler as compiler
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "erdos249257-historical-bridge-experiment/1"
ENVIRONMENT_CONTRACT = "clean_reproduction_subprocess_environment_v1"
INTRODUCTION_COMMIT = "11078b7791c429b99b057218bdce49597f0ce14c"
EXPECTED_PARENT = "8906a4c7978b69ed197b54e981f1873720c8a7be"
FUTURE_MODULE = "Erdos249257/RewindHalfDivisorAdapter.lean"
FUTURE_NAME = "supportCoeff_eq_of_restriction_at_halfDivisor"
HISTORICAL_BUILD_TARGET = "Erdos249257.HalfDivisorUnitDrop"


def _sha256_text(value: str) -> str:
    return "sha256:" + hashlib.sha256(value.encode("utf-8")).hexdigest()


def _run(
    command: list[str],
    *,
    cwd: Path,
    timeout_seconds: float,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        env=singleflight.command_environment(),
        timeout=timeout_seconds,
    )


def historical_request() -> dict[str, Any]:
    return {
        "schema_version": compiler.REQUEST_SCHEMA,
        "goal_id": "historical_half_divisor_coefficient_bridge",
        "imports": ["Erdos249257.HalfDivisorUnitDrop"],
        "opens": [
            "Erdos249257",
            "Erdos249257.HalfCarryReachability",
            "Erdos249257.HalfCarrySelectedWindow",
            "Erdos249257.HalfDivisorUnitDrop",
        ],
        "context": [
            {
                "name": "K",
                "binder": "{K : ℕ}",
                "role": "term",
            },
            {
                "name": "M",
                "binder": "{M : ℕ}",
                "role": "term",
            },
            {
                "name": "hKM",
                "binder": "(hKM : K + 1 ≤ M)",
                "role": "assumption",
            },
            {
                "name": "hMlt",
                "binder": "(hMlt : M < 2 * (K + 1))",
                "role": "assumption",
            },
            {
                "name": "w",
                "binder": "(w : HalfWord M)",
                "role": "term",
            },
            {
                "name": "b",
                "binder": "(b : HalfWord (K + 1))",
                "role": "term",
            },
            {
                "name": "hrestrict",
                "binder": "(hrestrict : restrictWord hKM w = b)",
                "role": "assumption",
            },
        ],
        "target": (
            "supportCoeff (wordSupport w) (2 * (K + 1)) =\n"
            "supportCoeff (wordSupport b) (2 * (K + 1))"
        ),
        "candidates": [
            {
                "candidate_id": "divisor_membership_extensionality",
                "declaration": (
                    "Erdos249257.HalfCarrySelectedWindow."
                    "supportCoeff_eq_of_divisorAgreement"
                ),
                "arguments": [],
                "discharge_tactics": [],
                "proposal_receipt": (
                    "pre-introduction extensionality theorem selected from "
                    "the authorised parent environment"
                ),
            }
        ],
    }


def anonymised_candidate_source() -> str:
    """Return the candidate statement/proof without future identifiers."""
    return """import Erdos249257.HalfDivisorUnitDrop

namespace HistoricalShadow

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.HalfDivisorUnitDrop

theorem historicalBridgeCandidate
    {K M : ℕ} (hKM : K + 1 ≤ M) (hMlt : M < 2 * (K + 1))
    (w : HalfWord M) (b : HalfWord (K + 1))
    (hrestrict : restrictWord hKM w = b) :
    supportCoeff (wordSupport w) (2 * (K + 1)) =
      supportCoeff (wordSupport b) (2 * (K + 1)) := by
  apply supportCoeff_eq_of_divisorAgreement
  intro e hediv
  by_cases heK : e ≤ K + 1
  · have hset := congrArg wordSupport hrestrict
    rw [wordSupport_restrictWord] at hset
    have hmem :
        e ∈ wordSupport w ∩ Set.Iic (K + 1) ↔ e ∈ wordSupport b := by
      rw [hset]
    simpa [heK] using hmem
  · have hwAbsent : e ∉ wordSupport w := by
      intro hew
      rcases hew with ⟨helt, -⟩
      have heM : e ≤ M := Nat.le_of_lt_succ helt
      have hdvd : e ∣ 2 * (K + 1) := Nat.dvd_of_mem_divisors hediv
      obtain ⟨q, hq⟩ := hdvd
      have hq0 : q ≠ 0 := by
        intro hzero
        subst q
        simp at hq
      have hq1 : q ≠ 1 := by
        intro hone
        subst q
        simp at hq
        omega
      have hq2 : 2 ≤ q := by omega
      have hmul : e * 2 ≤ 2 * (K + 1) := by
        rw [hq]
        exact Nat.mul_le_mul_left e hq2
      exact heK (by omega)
    have hbAbsent : e ∉ wordSupport b := by
      intro heb
      rcases heb with ⟨helt, -⟩
      exact heK (by omega)
    simp [hwAbsent, hbAbsent]

#print axioms historicalBridgeCandidate

end HistoricalShadow
"""


def _parent_of_introduction() -> str:
    completed = _run(
        ["git", "rev-parse", f"{INTRODUCTION_COMMIT}^"],
        cwd=ROOT,
        timeout_seconds=30.0,
    )
    if completed.returncode != 0:
        raise RuntimeError(completed.stdout)
    return completed.stdout.strip()


def _future_name_in_ref(ref: str) -> list[str]:
    completed = _run(
        [
            "git",
            "grep",
            "-n",
            FUTURE_NAME,
            ref,
            "--",
            "*.lean",
            "*.json",
            "*.md",
        ],
        cwd=ROOT,
        timeout_seconds=30.0,
    )
    if completed.returncode not in {0, 1}:
        raise RuntimeError(completed.stdout)
    return [
        line for line in completed.stdout.splitlines() if line.strip()
    ]


def _current_reuse_sites() -> list[str]:
    sites = []
    for path in sorted((ROOT / "Erdos249257").glob("*.lean")):
        if path.name == Path(FUTURE_MODULE).name:
            continue
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(),
            start=1,
        ):
            if FUTURE_NAME in line:
                sites.append(f"{path.relative_to(ROOT)}:{line_number}")
    return sites


def _prepare_historical_clone(clone_root: Path) -> dict[str, Any]:
    clone = _run(
        [
            "git",
            "clone",
            "--quiet",
            "--shared",
            "--no-checkout",
            str(ROOT),
            str(clone_root),
        ],
        cwd=ROOT,
        timeout_seconds=120.0,
    )
    if clone.returncode != 0:
        raise RuntimeError(clone.stdout)
    checkout = _run(
        ["git", "checkout", "--quiet", EXPECTED_PARENT],
        cwd=clone_root,
        timeout_seconds=60.0,
    )
    if checkout.returncode != 0:
        raise RuntimeError(checkout.stdout)

    packages = ROOT / ".lake/packages"
    if not packages.is_dir():
        raise RuntimeError(
            "current .lake/packages is required for an offline historical run"
        )
    historical_lake = clone_root / ".lake"
    historical_lake.mkdir(exist_ok=True)
    os.symlink(
        packages,
        historical_lake / "packages",
        target_is_directory=True,
    )

    started = time.monotonic()
    build = _run(
        ["lake", "build", HISTORICAL_BUILD_TARGET],
        cwd=clone_root,
        timeout_seconds=900.0,
    )
    elapsed = time.monotonic() - started
    if build.returncode != 0:
        raise RuntimeError(
            "historical dependency build failed:\n"
            + build.stdout[-8000:]
        )
    return {
        "target": HISTORICAL_BUILD_TARGET,
        "return_code": build.returncode,
        "elapsed_seconds": round(elapsed, 3),
        "output_digest": _sha256_text(build.stdout),
        "output_line_count": len(build.stdout.splitlines()),
        "dependency_packages": (
            "shared_pinned_packages_from_current_manifest"
        ),
        "project_oleans": "rebuilt_inside_disposable_parent_clone",
    }


def run_experiment() -> dict[str, Any]:
    parent = _parent_of_introduction()
    if parent != EXPECTED_PARENT:
        raise RuntimeError(
            f"introduction parent changed: {parent} != {EXPECTED_PARENT}"
        )
    parent_hits = _future_name_in_ref(EXPECTED_PARENT)
    source = anonymised_candidate_source()
    if FUTURE_NAME in source or "RewindHalfDivisorAdapter" in source:
        raise RuntimeError("future identifier leaked into historical source")
    if "sorry" in source or "admit" in source:
        raise RuntimeError("untrusted proof placeholder in candidate source")

    with tempfile.TemporaryDirectory(
        prefix="erdos249257-historical-bridge-"
    ) as temp_dir:
        clone_root = Path(temp_dir) / "repo"
        build_receipt = _prepare_historical_clone(clone_root)
        if (clone_root / FUTURE_MODULE).exists():
            raise RuntimeError("future module exists in the parent checkout")

        transition_packet = compiler.compile_request(
            historical_request(),
            repo_root=clone_root,
            timeout_seconds=120.0,
        )
        transition = transition_packet["lean_tested_transitions"][0]
        blocker_targets = [
            row["target"] for row in transition["open_obligations"]
        ]

        candidate = _run(
            ["lake", "env", "lean", "--stdin", "--json"],
            cwd=clone_root,
            input_text=source,
            timeout_seconds=180.0,
        )
        candidate_messages, non_json = compiler._parse_lean_messages(
            candidate.stdout
        )
        sorry_axiom = any(
            "sorryAx" in str(message.get("data", ""))
            for message in candidate_messages
        )
        candidate_receipt = {
            "candidate_name": "HistoricalShadow.historicalBridgeCandidate",
            "return_code": candidate.returncode,
            "kernel_checked": candidate.returncode == 0 and not sorry_axiom,
            "source_digest": _sha256_text(source),
            "message_digest": _sha256_text(candidate.stdout),
            "message_count": len(candidate_messages),
            "non_json_output": non_json[:8],
            "sorry_axiom_detected": sorry_axiom,
            "future_identifier_absent": True,
        }

    reuse_sites = _current_reuse_sites()
    verdict = {
        "parent_identity_verified": parent == EXPECTED_PARENT,
        "future_name_absent_from_parent": not parent_hits,
        "future_module_absent_from_parent": True,
        "minimal_blocker_is_divisor_membership_agreement": (
            len(blocker_targets) == 1
            and "∀ d ∈ (2 * (K + 1)).divisors" in blocker_targets[0]
        ),
        "anonymised_candidate_kernel_checked": candidate_receipt[
            "kernel_checked"
        ],
        "later_independent_reuse_count": len(reuse_sites),
        "later_reused": len(reuse_sites) >= 2,
    }
    return {
        "schema_version": SCHEMA,
        "kind": "historical_bridge_experiment",
        "experiment_class": (
            "blinded_historical_shadow_evaluator_not_autonomous_discovery"
        ),
        "history_identity": {
            "introduction_commit": INTRODUCTION_COMMIT,
            "parent_commit": parent,
            "future_module": FUTURE_MODULE,
            "future_declaration": FUTURE_NAME,
        },
        "leakage_controls": {
            "parent_future_name_hits": parent_hits,
            "candidate_source_uses_fresh_name": True,
            "candidate_source_excludes_future_module_and_name": True,
            "future_projections_imported": False,
            "proof_run_completed_before_current_reuse_scan": True,
        },
        "historical_build_receipt": build_receipt,
        "obstruction_packet": transition_packet,
        "blocker_targets": blocker_targets,
        "candidate_proof_receipt": candidate_receipt,
        "current_history_reuse_evidence": {
            "sites": reuse_sites,
            "site_count": len(reuse_sites),
            "authority_posture": (
                "post-experiment utility evidence only; never proof input"
            ),
        },
        "verdict": verdict,
        "claim_ceiling": (
            "The evaluator recovers an exact pre-introduction blocker and "
            "kernel-checks an anonymised authored bridge candidate in the "
            "real parent environment; it does not claim autonomous synthesis."
        ),
        "promotion_reentry": (
            "replace the authored candidate with a cut-conditioned generator "
            "and repeat on a second corpus or prospective unseen bridge"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="run the blinded historical bridge shadow experiment"
    )
    parser.add_argument("--compact", action="store_true")
    parser.add_argument("--singleflight-worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    packet = run_experiment()
    print(
        json.dumps(
            packet,
            indent=None if args.compact else 2,
            sort_keys=True,
        )
    )
    verdict = packet["verdict"]
    success = all(
        value is True
        for key, value in verdict.items()
        if key != "later_independent_reuse_count"
    ) and verdict["later_independent_reuse_count"] >= 2
    return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
