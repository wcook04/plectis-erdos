#!/usr/bin/env python3
"""Focused offline tests for ``proof_workbench.py`` ledger mechanics.

Live Lean is not required here: the probe runner is stubbed so the tests
exercise the notary contract itself — append-only ledger, the claim gate
that refuses non-kernel-accepted citations, the conjecture falsifier
warning, and byte-exact replay bookkeeping.
"""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

import proof_workbench as workbench


def _run(sessions_root: Path, argv: list[str]) -> dict:
    parser = workbench.build_parser(workbench.repo_root())
    args = parser.parse_args(
        ["--sessions-root", str(sessions_root), *argv]
    )
    return args.func(args, workbench.repo_root())


def check_session_lifecycle(sessions_root: Path) -> None:
    opened = _run(
        sessions_root,
        [
            "open",
            "--session",
            "t_lifecycle",
            "--intent",
            "exercise the notary",
            "--actor",
            "test_agent",
        ],
    )
    assert opened["kind"] == "session_opened"
    assert opened["environment_fingerprint"]["git_head"]
    note = _run(
        sessions_root,
        [
            "note",
            "--session",
            "t_lifecycle",
            "--kind",
            "conjecture",
            "--text",
            "the pivot exists",
        ],
    )
    assert note["warning"] == "conjecture_without_declared_falsifier"
    grounded = _run(
        sessions_root,
        [
            "note",
            "--session",
            "t_lifecycle",
            "--kind",
            "conjecture",
            "--text",
            "the pivot exists",
            "--falsifier",
            "a numeral-adjacent pair with no flip rank",
        ],
    )
    assert "warning" not in grounded
    closed = _run(
        sessions_root,
        [
            "close",
            "--session",
            "t_lifecycle",
            "--outcome",
            "open",
            "--summary",
            "lifecycle only",
        ],
    )
    assert closed["move_counts"]["note"] == 2
    assert closed["kernel_accepted_probes"] == 0


def check_claim_gate(sessions_root: Path, tmp: Path) -> None:
    real_runner = workbench.run_lean_probe
    calls: list[str] = []

    def fake_runner(root: Path, source: str) -> dict:
        calls.append(source)
        verdict = (
            "kernel_accepted"
            if "good" in source
            else "kernel_rejected"
        )
        return {
            "verdict": verdict,
            "detail": None,
            "exit_code": 0 if verdict == "kernel_accepted" else 1,
            "error_count": 0 if verdict == "kernel_accepted" else 1,
            "sorry_count": 0,
            "duration_seconds": 0.01,
            "output_tail": "",
        }

    workbench.run_lean_probe = fake_runner
    try:
        _run(
            sessions_root,
            [
                "open",
                "--session",
                "t_claims",
                "--intent",
                "claim gate",
            ],
        )
        good = tmp / "good.lean"
        good.write_text("-- good probe\n", encoding="utf-8")
        bad = tmp / "bad.lean"
        bad.write_text("-- failing probe\n", encoding="utf-8")
        accepted = _run(
            sessions_root,
            [
                "probe",
                "--session",
                "t_claims",
                "--file",
                str(good),
                "--label",
                "accepted",
            ],
        )
        assert accepted["kernel_receipt"]["verdict"] == (
            "kernel_accepted"
        )
        rejected = _run(
            sessions_root,
            [
                "probe",
                "--session",
                "t_claims",
                "--file",
                str(bad),
            ],
        )
        assert rejected["kernel_receipt"]["verdict"] == (
            "kernel_rejected"
        )
        claim = _run(
            sessions_root,
            [
                "claim",
                "--session",
                "t_claims",
                "--text",
                "the good probe establishes the lemma",
                "--probe",
                accepted["move_id"],
            ],
        )
        assert claim["authority"] == "kernel_accepted_probe_receipt"
        refused = False
        try:
            _run(
                sessions_root,
                [
                    "claim",
                    "--session",
                    "t_claims",
                    "--text",
                    "this must be refused",
                    "--probe",
                    rejected["move_id"],
                ],
            )
        except SystemExit:
            refused = True
        assert refused, "claim citing a rejected probe must be refused"
        replay = _run(
            sessions_root,
            ["replay", "--session", "t_claims"],
        )
        assert replay["probes_replayed"] == 2
        assert replay["all_match"]
    finally:
        workbench.run_lean_probe = real_runner


def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        sessions_root = tmp / "sessions"
        check_session_lifecycle(sessions_root)
        check_claim_gate(sessions_root, tmp)
    print(
        json.dumps(
            {
                "schema": "proof-workbench-test-receipt/1",
                "passed": True,
                "checks": 2,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
