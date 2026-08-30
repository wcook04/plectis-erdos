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


def check_session_path_boundaries(tmp: Path) -> None:
    real = tmp / "real-sessions"
    real.mkdir()
    linked = tmp / "linked-sessions"
    linked.symlink_to(real, target_is_directory=True)
    try:
        _run(
            linked,
            [
                "open",
                "--session",
                "redirected",
                "--intent",
                "symlink root",
            ],
        )
    except SystemExit as error:
        if "symbolic links" not in str(error):
            raise AssertionError(f"symlink root rejection had no bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench followed a symlinked sessions root")
    if (real / "redirected" / "ledger.jsonl").exists():
        raise AssertionError("symlinked sessions root received a redirected ledger")

    try:
        _run(
            real,
            [
                "open",
                "--session",
                "../escaped",
                "--intent",
                "session traversal",
            ],
        )
    except SystemExit as error:
        if "session must match" not in str(error):
            raise AssertionError(f"session traversal rejection had no bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted a path-traversing session slug")
    if (tmp / "escaped" / "ledger.jsonl").exists():
        raise AssertionError("traversing session slug received an escaped ledger")


def check_replay_path_boundary(tmp: Path) -> None:
    sessions_root = tmp / "replay-sessions"
    parser = workbench.build_parser(workbench.repo_root())
    _run(
        sessions_root,
        ["open", "--session", "replay", "--intent", "replay path boundary"],
    )
    source = "-- redirected replay bytes\n"
    outside = tmp / "replay-outside.lean"
    outside.write_text(source, encoding="utf-8")
    receipt = {
        "verdict": "kernel_accepted",
        "detail": None,
        "exit_code": 0,
        "error_count": 0,
        "sorry_count": 0,
        "duration_seconds": 0.0,
        "output_tail": "",
    }
    session = workbench.Session(sessions_root, "replay")
    session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "at": "2026-08-30T00:00:00+00:00",
            "kind": "probe",
            "input_path": "../../replay-outside.lean",
            "input_sha256": workbench._sha256_text(source),
            "label": "redirected",
            "kernel_receipt": receipt,
        }
    )
    linked = sessions_root / "replay" / "probes" / "m003.lean"
    linked.symlink_to(outside)
    session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m003",
            "at": "2026-08-30T00:00:00+00:00",
            "kind": "probe",
            "input_path": "probes/m003.lean",
            "input_sha256": workbench._sha256_text(source),
            "label": "linked",
            "kernel_receipt": receipt,
        }
    )
    calls: list[str] = []
    real_runner = workbench.run_lean_probe
    workbench.run_lean_probe = lambda _root, text: calls.append(text) or receipt
    try:
        replay_args = parser.parse_args(
            ["--sessions-root", str(sessions_root), "replay", "--session", "replay"]
        )
        result = replay_args.func(replay_args, workbench.repo_root())
    finally:
        workbench.run_lean_probe = real_runner
    if result["all_match"]:
        raise AssertionError("replay treated rejected probe paths as matches")
    if [row["replay"] for row in result["results"]] != [
        "input_path_rejected",
        "input_path_rejected",
    ]:
        raise AssertionError(f"replay path rejection drifted: {result}")
    if calls:
        raise AssertionError("replay executed a path rejected by the session boundary")


def check_malformed_ledger_boundary(tmp: Path) -> None:
    """Every workbench command must receive a bounded ledger-read failure."""
    sessions_root = tmp / "malformed-ledger-sessions"
    session = workbench.Session(sessions_root, "malformed")
    session.directory.mkdir(parents=True)
    session.ledger_path.write_bytes(b"{\xff\n")
    try:
        session.moves()
    except SystemExit as error:
        if "utf-8" not in str(error).lower():
            raise AssertionError(f"malformed ledger lacked a decode diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted a malformed UTF-8 ledger")

    session.ledger_path.write_text("not-json\n", encoding="utf-8")
    try:
        session.moves()
    except SystemExit as error:
        if "line 1" not in str(error):
            raise AssertionError(f"malformed ledger lacked a line diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted malformed ledger JSON")

    receipt_session = workbench.Session(sessions_root, "malformed-receipt")
    receipt_session.directory.mkdir(parents=True)
    rows = [
        {"schema": workbench.SESSION_SCHEMA, "move_id": "m001", "kind": "session_opened"},
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/m002.lean",
            "input_sha256": "x",
            "kernel_receipt": "corrupt",
        },
    ]
    separator = chr(10)
    receipt_session.ledger_path.write_text(
        separator.join(json.dumps(row) for row in rows) + separator,
        encoding="utf-8",
    )
    commands = (
        (
            "show",
            lambda: workbench.cmd_show(
                type("Args", (), {"sessions_root": sessions_root, "session": "malformed-receipt"})(),
                workbench.repo_root(),
            ),
        ),
        (
            "close",
            lambda: workbench.cmd_close(
                type(
                    "Args",
                    (),
                    {
                        "sessions_root": sessions_root,
                        "session": "malformed-receipt",
                        "outcome": "open",
                        "summary": "malformed receipt",
                    },
                )(),
                workbench.repo_root(),
            ),
        ),
        (
            "claim",
            lambda: workbench.cmd_claim(
                type(
                    "Args",
                    (),
                    {
                        "sessions_root": sessions_root,
                        "session": "malformed-receipt",
                        "probe": "m002",
                        "text": "must refuse",
                    },
                )(),
                workbench.repo_root(),
            ),
        ),
    )
    for action, command in commands:
        try:
            command()
        except SystemExit as error:
            if "invalid kernel receipt" not in str(error):
                raise AssertionError(f"{action} lacked a bounded receipt diagnostic: {error}")
        else:
            raise AssertionError(f"{action} accepted a malformed kernel receipt")


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
        linked = tmp / "linked.lean"
        linked.symlink_to(good)
        refused_symlink = False
        try:
            _run(
                sessions_root,
                [
                    "probe",
                    "--session",
                    "t_claims",
                    "--file",
                    str(linked),
                ],
            )
        except SystemExit as error:
            refused_symlink = "symbolic links" in str(error)
        assert refused_symlink, "probe followed a symlinked source path"
        assert not (sessions_root / "t_claims" / "probes" / "m004.lean").exists()
        invalid = tmp / "invalid-utf8.lean"
        invalid.write_bytes(b"\xff\xfe\n")
        refused_invalid_utf8 = False
        try:
            _run(
                sessions_root,
                [
                    "probe",
                    "--session",
                    "t_claims",
                    "--file",
                    str(invalid),
                ],
            )
        except SystemExit as error:
            refused_invalid_utf8 = "not readable UTF-8" in str(error)
        assert refused_invalid_utf8, "probe accepted invalid UTF-8 source"
        assert not (sessions_root / "t_claims" / "probes" / "m004.lean").exists()
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
        check_session_path_boundaries(tmp)
        check_replay_path_boundary(tmp)
        check_malformed_ledger_boundary(tmp)
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
