#!/usr/bin/env python3
"""Run one historical bridge evaluation and state exactly what it can answer.

Two questions must be kept apart, because a checkout of a past revision
answers only the first.

Q1, interpretation.  Do the semantic layers present at a revision let a reader
find the relevant mathematics and interpret it correctly?  The obstruction
packet compiled inside the parent checkout is evidence about Q1: it shows
which exact obligation the layers at that revision expose for a stated target.

Q2, acceleration.  Do the derived layers as they stood in the past shorten the
work of producing a later result?  This module does not answer Q2 and must not
be reported as if it did.  A past checkout does not isolate acceleration,
because several channels can carry the later answer into the run.  The channel
table below names each channel and says whether this module controls it.  The
uncontrolled channels are limitations of every number this module prints.

Controlled here:
  parent_identity        the parent commit is recomputed from the introduction
                         commit and compared with the pinned value;
  future_declaration     the future declaration name is absent from the parent
    _name                ref across .lean, .json and .md, by ``git grep``;
  future_module_file     the future module path does not exist in the parent
                         checkout;
  candidate_naming       the candidate source contains neither the future
                         declaration name nor the future module name;
  candidate_placeholder  the candidate source contains no ``sorry`` or
                         ``admit``, and a ``sorryAx`` axiom in the kernel
                         report fails the run;
  build_scope            only the pre-existing dependency target is built
                         inside the disposable parent clone;
  obstruction_scope      the proof-state compiler runs against the parent
                         checkout root, not the current tree;
  measurement_order      later reuse in current history is scanned only after
                         the proof run has finished.

Not controlled here, and therefore reported as limitations:
  shared_object_store    the disposable clone is created with ``git clone
                         --shared``, so every later commit, tree and blob of
                         the current repository stays reachable by object id
                         from inside the historical checkout;
  dependency_pin         ``.lake/packages`` is symlinked from the current tree,
                         so the run uses the current dependency pin rather than
                         the one the parent revision declared;
  derived_layer_content  only the future declaration *name* is screened.  A
                         paraphrase, a semantic node, a receipt, a dossier or a
                         prose statement at the parent revision that describes
                         the same bridge is not detected;
  supplied_context       the request supplied to the compiler already names the
                         target statement and the exact candidate declaration,
                         so obstruction recovery is conditioned on an answer
                         key rather than searched for;
  authored_candidate     the candidate proof is an authored reconstruction
                         written with knowledge of the later proof;
  no_agent_in_the_loop   no model runs here, so nothing in this module measures
                         what a model would find without the layers;
  model_familiarity      a model asked to reproduce this bridge may have seen
                         the public mathematics during training;
  network_and_filesystem the child processes are environment-sanitised, and
                         they are not sandboxed against network or filesystem
                         access;
  no_control_arm         there is no ordinary source-and-documentation arm, so
                         no comparison between routes is available.

Reading of the verdict.  A pass says that the runtime recovers an exact
pre-introduction obligation for a supplied target and that an authored,
name-free candidate is accepted by the kernel in the parent environment.  It
does not say that the system invented the lemma, that the derived layers
caused anything, or that a later result was produced faster.
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

# Design constants.
# These describe the experiment.  They are declarative and must stay in step
# with the module docstring and with docs/methodology.json.

QUESTIONS = {
    "Q1_interpretation": (
        "Do the semantic layers present at a revision let a reader find the "
        "relevant mathematics and interpret it correctly?"
    ),
    "Q2_acceleration": (
        "Do the derived layers as they stood in the past shorten the work of "
        "producing a later result?"
    ),
}
QUESTION_ANSWERED_BY_THIS_MODULE = "Q1_interpretation"
QUESTION_NOT_ANSWERED_BY_THIS_MODULE = "Q2_acceleration"

CONTROLLED_LEAKAGE_CHANNELS = {
    "parent_identity": "parent commit recomputed and compared with the pin",
    "future_declaration_name": (
        "git grep for the future declaration name at the parent ref across "
        ".lean, .json and .md returns no hits"
    ),
    "future_module_file": "future module path absent from the parent checkout",
    "candidate_naming": (
        "candidate source excludes the future declaration name and module name"
    ),
    "candidate_placeholder": (
        "candidate source excludes sorry and admit; a sorryAx axiom fails the run"
    ),
    "build_scope": "only the pre-existing dependency target is built",
    "obstruction_scope": "the compiler reads the parent checkout root",
    "measurement_order": "current-history reuse is scanned after the proof run",
}
UNCONTROLLED_LEAKAGE_CHANNELS = {
    "shared_object_store": (
        "git clone --shared keeps every later object reachable by id from the "
        "historical checkout"
    ),
    "dependency_pin": (
        ".lake/packages is symlinked from the current tree, so the historical "
        "run uses the current dependency pin"
    ),
    "derived_layer_content": (
        "only the declaration name is screened; a paraphrase, semantic node, "
        "receipt, dossier or prose statement describing the same bridge is not"
    ),
    "supplied_context": (
        "the compiler request names the target statement and the exact "
        "candidate declaration"
    ),
    "authored_candidate": (
        "the candidate proof was authored with knowledge of the later proof"
    ),
    "no_agent_in_the_loop": "no model runs, so no search behaviour is observed",
    "model_familiarity": (
        "a model reproducing this bridge may have seen the public mathematics "
        "during training"
    ),
    "network_and_filesystem": (
        "child processes are environment-sanitised and are not sandboxed"
    ),
    "no_control_arm": (
        "no ordinary source-and-documentation arm is run, so no route "
        "comparison is available"
    ),
}

# The comparison a Q2 result would require.  Target, access permissions and
# work budget are held fixed; only the route varies.
CONTROL_ARM = "ordinary_source_and_documentation_route"
TREATMENT_ARM = "derived_semantic_and_obstruction_layers"
HELD_CONSTANT_ACROSS_ARMS = (
    "target_declaration",
    "access_permissions",
    "work_budget",
)
MEASURED_OUTCOMES = (
    "correct_reconstruction",
    "false_strengthening",
    "missed_hypotheses",
    "correct_identification_of_the_open_remainder",
    "successful_replay",
    "usable_returned_contribution",
)

# Fixture separation.  The bridge below is the development fixture: its
# obstruction and candidate were inspected while this harness was written, so
# it can be used to debug the harness and must never be reported as an
# evaluation result.  Evaluation cases are held out and unseen.
DEVELOPMENT_FIXTURE_ID = "half_divisor_coefficient_bridge"
FIXTURE_ROLE = "development_fixture_not_an_evaluation_case"
HELD_OUT_VARIANT_CLASSES = (
    "ordinary_proof_presented_as_lean_checked",
    "attractive_claim_absent_from_a_selector",
    "same_file_export_loss",
    "stale_rendered_artifact",
    "apparently_closed_route_whose_obstruction_is_unproved",
)


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
        "experiment_design": {
            "questions": QUESTIONS,
            "question_answered": QUESTION_ANSWERED_BY_THIS_MODULE,
            "question_not_answered": QUESTION_NOT_ANSWERED_BY_THIS_MODULE,
            "controlled_leakage_channels": CONTROLLED_LEAKAGE_CHANNELS,
            "uncontrolled_leakage_channels": UNCONTROLLED_LEAKAGE_CHANNELS,
            "control_arm": CONTROL_ARM,
            "treatment_arm": TREATMENT_ARM,
            "held_constant_across_arms": list(HELD_CONSTANT_ACROSS_ARMS),
            "measured_outcomes": list(MEASURED_OUTCOMES),
            "arms_run_here": [TREATMENT_ARM],
            "fixture_id": DEVELOPMENT_FIXTURE_ID,
            "fixture_role": FIXTURE_ROLE,
            "held_out_variant_classes": list(HELD_OUT_VARIANT_CLASSES),
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
            "The evaluator recovers an exact pre-introduction obligation for a "
            "supplied target and kernel-checks an authored, name-free bridge "
            "candidate in the parent environment. This is Q1 evidence on a "
            "development fixture. It does not claim autonomous synthesis, it "
            "does not measure acceleration, and it does not control the "
            "channels listed under uncontrolled_leakage_channels."
        ),
        "promotion_reentry": (
            "to answer Q2, add the ordinary source-and-documentation control "
            "arm with target, access permissions and work budget held fixed, "
            "close the shared object store and dependency pin, screen the "
            "derived layers for paraphrases of the target rather than only for "
            "its declaration name, stop supplying the candidate declaration in "
            "the request, and run the held-out variant classes on a corpus "
            "whose bridge was never inspected while writing this harness"
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
