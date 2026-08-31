#!/usr/bin/env python3
"""Focused contract and live-Lean tests for ``proof_state_compiler.py``."""

from __future__ import annotations

import copy
import json
import os
import tempfile
from pathlib import Path
from unittest import mock

import proof_state_compiler as compiler
import validation_singleflight as singleflight


def check_goal_parser() -> None:
    state = """case left
x : Nat
⊢ x = x

case right
y : Nat
⊢ y ≤ y"""
    goals = compiler.split_goal_state(state)
    assert [goal["case"] for goal in goals] == ["left", "right"]
    assert [goal["target"] for goal in goals] == ["⊢ x = x", "⊢ y ≤ y"]


def check_minimal_cuts() -> None:
    residuals = [{"a", "b"}, {"b", "c"}]
    cuts = compiler.minimal_hitting_sets(residuals)
    assert cuts == [["b"], ["a", "c"]]
    interventions = compiler.minimal_missing_interventions(residuals)
    assert interventions == [["a", "b"], ["b", "c"]]
    # Category boundary: adding cut {b} closes neither plan, while each
    # intervention row completes exactly one plan.
    assert interventions != cuts
    single = [{"a", "b"}]
    assert compiler.minimal_hitting_sets(single) == [["a"], ["b"]]
    assert compiler.minimal_missing_interventions(single) == [["a", "b"]]
    absorbed = compiler.minimal_missing_interventions(
        [{"a", "b"}, {"a", "b", "c"}]
    )
    assert absorbed == [["a", "b"]]


def check_subprocess_environment() -> None:
    completed = compiler.subprocess.CompletedProcess([], 0, "fixture\n", "")
    hostile = {
        "GIT_DIR": "/foreign/repository",
        "GIT_NAMESPACE": "foreign-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/foreign/",
        "PYTHONPATH": "/foreign/modules",
        "LANG": "fr_FR",
    }
    with mock.patch.dict(os.environ, hostile, clear=False), mock.patch.object(
        compiler.subprocess, "run", return_value=completed
    ) as run:
        observed = compiler._command_output(
            ["git", "rev-parse", "HEAD"], cwd=Path("/tmp"), timeout_seconds=7
        )

    if observed != "fixture":
        raise AssertionError(f"unexpected mocked command output: {observed!r}")
    call = run.call_args
    expected_environment = dict(singleflight.command_environment())
    expected_environment["PATH"] = os.pathsep.join(
        (str(compiler.TOOLCHAIN_BIN), expected_environment["PATH"])
    )
    if call.kwargs["env"] != expected_environment:
        raise AssertionError(
            "proof-state subprocess drifted from the canonical elan-visible "
            "environment"
        )
    if call.kwargs["timeout"] != 7:
        raise AssertionError("proof-state subprocess lost its explicit timeout")


def check_toolchain_absence_is_a_clean_skip_signal() -> None:
    """A missing `lake` must raise ToolchainUnavailable, never a bare crash.

    This is the inverse of ``check_subprocess_environment``: it proves the
    skip path is wired to genuine absence (``FileNotFoundError`` from the
    OS trying to exec ``lake``) and not to "the check failed for some other
    reason".  A non-zero exit or a real Lean rejection must still surface
    as a different, louder failure -- see ``check_typed_rejection``, which
    exercises exactly that path with a live Lean rejection when the
    toolchain is actually present.
    """
    real_run = compiler.subprocess.run
    real_require = compiler._require_lean_dependencies

    def missing_lake_only(command, *args, **kwargs):
        if command and command[0] == "lake":
            raise FileNotFoundError(2, "No such file or directory", "lake")
        return real_run(command, *args, **kwargs)

    compiler.subprocess.run = missing_lake_only
    # Stand the dependency probe down. It runs first and raises a subclass of
    # the same exception, so leaving it live would let this check pass in an
    # unbuilt clone without ever reaching the `lake` exec it exists to test.
    compiler._require_lean_dependencies = lambda _repo_root: None
    try:
        try:
            compiler.environment_fingerprint(compiler.ROOT, timeout_seconds=1)
        except compiler.LeanDependenciesUnavailable as error:
            raise AssertionError(
                "the missing-`lake` probe was answered by the dependency "
                f"signal instead of the exec failure: {error}"
            ) from error
        except compiler.ToolchainUnavailable:
            pass
        else:
            raise AssertionError(
                "environment_fingerprint did not raise ToolchainUnavailable "
                "when `lake` was absent"
            )
    finally:
        compiler.subprocess.run = real_run
        compiler._require_lean_dependencies = real_require


def check_unfetched_dependencies_are_a_clean_skip_signal() -> None:
    """An unbuilt clone must say so, and a built one must not get the excuse.

    A fresh clone has `lake` but no `.lake/packages`, and the raw failure is a
    git error about checking out a mathlib revision, which reads like the
    repository is broken. Both halves matter: absent packages must produce the
    named signal, and present packages must not, or a genuine `lake` failure
    would be skipped as an environment problem.
    """
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        (root / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": "mathlib"}, {"name": "batteries"}]}),
            encoding="utf-8",
        )
        packages = root / ".lake" / "packages"

        def refuses(stage: str) -> None:
            try:
                compiler._require_lean_dependencies(root)
            except compiler.LeanDependenciesUnavailable:
                return
            raise AssertionError(
                f"an incomplete checkout ({stage}) did not raise "
                "LeanDependenciesUnavailable"
            )

        refuses("nothing fetched")
        # A `lake` run that dies mid-resolution leaves the package it was
        # working on behind. That is still incomplete, and the earlier shallow
        # probe stopped firing at exactly this point.
        (packages / "mathlib").mkdir(parents=True)
        refuses("resolution stopped partway")

        (packages / "batteries").mkdir(parents=True)
        # Complete tree: the probe must stand aside so that a genuine `lake`
        # failure still reaches the caller as a failure.
        compiler._require_lean_dependencies(root)


def check_live_pilot() -> dict:
    packet = compiler.compile_pilot_suite()
    assert packet["schema_version"] == compiler.PILOT_SCHEMA
    assert packet["packet_bytes"] < compiler.MAX_PACKET_BYTES
    expected_verdict = {
        "blocked_control_is_precise": True,
        "counterfactual_closes": True,
        "independent_ready_control_closes": True,
    }
    if packet["pilot_verdict"] != expected_verdict:
        first_failure = next(
            (
                failure
                for case in packet["cases"].values()
                for transition in case["lean_tested_transitions"]
                for failure in transition["typed_failures"]
            ),
            None,
        )
        raise AssertionError(
            "live Lean pilot verdict mismatch: Lean genuinely ran (this is "
            "not a missing-toolchain skip) but its verdict does not match "
            f"the expected controls. expected={expected_verdict!r} "
            f"observed={packet['pilot_verdict']!r}. A common cause in a "
            "checkout that has not run `lake build` is an unresolved local "
            "import (e.g. \"unknown module prefix 'Erdos249257'\"); first "
            f"typed failure: {first_failure!r}"
        )
    causal = packet["causal_obstruction_receipt"]
    assert causal["same_target"]
    assert causal["same_candidate_action"]
    assert causal["added_assumptions"] == ["hdvd"]
    assert causal["effect"] == (
        "exact_obligation_is_causally_sufficient_for_this_transition"
    )

    blocked = packet["cases"]["integer_tail_without_divisibility"]
    transition = blocked["lean_tested_transitions"][0]
    assert transition["status"] == "lean_accepted_open_obligations"
    assert transition["lean_run_receipt"][
        "expected_unsolved_goal_error_ignored"
    ]
    assert transition["declaration_receipt"]["source_ref"] == (
        "Erdos249257/TotientTailPeriodKiller.lean:327"
    )
    assert blocked["minimal_blocker_cuts"][0]["targets"] == [
        "⊢ r.den ∣ 2 ^ N * (2 ^ h - 1)"
    ]
    assert blocked["minimal_missing_interventions"][0]["targets"] == [
        "⊢ r.den ∣ 2 ^ N * (2 ^ h - 1)"
    ]
    assert "minimal_blocker_cuts" in blocked["blocker_algebra_semantics"]

    ready = packet["cases"]["integer_tail_with_divisibility"]
    assert ready["closed_proof_receipts"]
    assert ready["lean_tested_transitions"][0]["proof_closed"]

    curvature = packet["cases"]["curvature_supply_control"]
    curvature_transition = curvature["lean_tested_transitions"][0]
    assert curvature_transition["proof_closed"]
    assert curvature_transition["open_obligations"][0]["target"] == (
        "⊢ SharpCurvatureSupply"
    )
    return packet


def check_typed_rejection() -> None:
    request = copy.deepcopy(compiler.pilot_requests()[0])
    request["goal_id"] = "deliberately_incompatible_candidate"
    request["candidates"][0] = {
        "candidate_id": "wrong_shape",
        "declaration": (
            "Erdos249257.TotientTailPeriodKiller."
            "irrational_totientSeries_of_sharpCurvatureSupply"
        ),
        "arguments": [],
        "discharge_tactics": [],
    }
    packet = compiler.compile_request(request)
    transition = packet["lean_tested_transitions"][0]
    assert transition["status"] == "lean_rejected"
    assert not transition["application_accepted"]
    assert transition["typed_failures"]
    assert packet["abstention_receipt"]["status"] == (
        "all_candidates_rejected_by_Lean"
    )


def main() -> int:
    check_goal_parser()
    check_minimal_cuts()
    check_subprocess_environment()
    check_toolchain_absence_is_a_clean_skip_signal()
    check_unfetched_dependencies_are_a_clean_skip_signal()
    try:
        packet = check_live_pilot()
        check_typed_rejection()
    except compiler.ToolchainUnavailable as error:
        print(
            "SKIPPED test_proof_state_compiler: the live-Lean checks "
            "(check_live_pilot, check_typed_rejection) need a working pinned "
            "Lean environment, which this checkout does not have. "
            f"{error} These checks would have compiled the pilot's three "
            "causal controls and one typed-rejection probe through real "
            "Lean elaboration -- see lean-toolchain and "
            "docs/PROOF_STATE_COMPILER.md for the setup route. The static "
            "checks that do not need Lean (goal parser, minimal cuts, "
            "subprocess environment isolation, toolchain-absence signal) "
            "still ran and passed."
        )
        return 0
    print(
        json.dumps(
            {
                "schema": "proof-state-compiler-test-receipt/1",
                "passed": True,
                "checks": 6,
                "pilot_packet_bytes": packet["packet_bytes"],
                "environment_fingerprint": packet[
                    "environment_fingerprint"
                ]["fingerprint"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
