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
    (sessions_root / "replay" / "probes" / "other.lean").write_text(
        source, encoding="utf-8"
    )
    session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m004",
            "at": "2026-08-30T00:00:00+00:00",
            "kind": "probe",
            "input_path": "probes/other.lean",
            "input_sha256": workbench._sha256_text(source),
            "label": "noncanonical",
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
        "input_path_rejected",
    ]:
        raise AssertionError(f"replay path rejection drifted: {result}")
    if calls:
        raise AssertionError("replay executed a path rejected by the session boundary")


def check_replay_receipt_boundary(tmp: Path) -> None:
    """Replay must not compare a fresh run against forged receipt provenance."""
    sessions_root = tmp / "replay-receipt-sessions"
    workbench.cmd_open(
        type(
            "Args",
            (),
            {
                "sessions_root": sessions_root,
                "session": "empty-replay",
                "actor": "outsider",
                "intent": "empty evidence",
            },
        )(),
        workbench.repo_root(),
    )
    empty_result = workbench.cmd_replay(
        type(
            "Args",
            (),
            {"sessions_root": sessions_root, "session": "empty-replay"},
        )(),
        workbench.repo_root(),
    )
    assert empty_result["probes_replayed"] == 0
    assert not empty_result["all_match"]

    cases = (
        (
            "unknown-verdict",
            {
                "verdict": "made_up_verdict",
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            },
        ),
        (
            "contradictory-verdict",
            {
                "verdict": "kernel_accepted",
                "exit_code": 1,
                "error_count": 1,
                "sorry_count": 0,
            },
        ),
    )
    for session_name, receipt in cases:
        session = workbench.Session(sessions_root, session_name)
        session.probes_dir.mkdir(parents=True)
        source = f"exact {session_name}\n"
        (session.probes_dir / "m002.lean").write_text(source, encoding="utf-8")
        session.append(
            {
                "schema": workbench.SESSION_SCHEMA,
                "move_id": "m001",
                "kind": "session_opened",
            }
        )
        session.append(
            {
                "schema": workbench.MOVE_SCHEMA,
                "move_id": "m002",
                "kind": "probe",
                "input_path": "probes/m002.lean",
                "input_sha256": workbench._sha256_text(source),
                "kernel_receipt": receipt,
            }
        )
        calls: list[str] = []
        real_runner = workbench.run_lean_probe
        workbench.run_lean_probe = (
            lambda _root, text: calls.append(text)
            or {
                "verdict": "kernel_accepted",
                "detail": None,
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            }
        )
        try:
            result = workbench.cmd_replay(
                type(
                    "Args",
                    (),
                    {"sessions_root": sessions_root, "session": session_name},
                )(),
                workbench.repo_root(),
            )
        finally:
            workbench.run_lean_probe = real_runner
        assert result["probes_replayed"] == 1
        assert not result["all_match"]
        assert result["results"][0]["replay"] == "kernel_receipt_invalid"
        assert not calls, "replay ran Lean against an invalid receipt"


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

    unknown_kind_session = workbench.Session(sessions_root, "unknown-kind")
    unknown_kind_session.directory.mkdir(parents=True)
    unknown_kind_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    unknown_kind_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "untrusted-move",
        }
    )
    try:
        unknown_kind_session.moves()
    except SystemExit as error:
        if "unsupported move kind" not in str(error):
            raise AssertionError(f"unknown move kind lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted an unknown move kind")

    schema_sessions = (
        (
            "wrong-open-schema",
            [
                {
                    "schema": workbench.MOVE_SCHEMA,
                    "move_id": "m001",
                    "kind": "session_opened",
                }
            ],
        ),
        (
            "wrong-move-schema",
            [
                {
                    "schema": workbench.SESSION_SCHEMA,
                    "move_id": "m001",
                    "kind": "session_opened",
                },
                {
                    "schema": workbench.SESSION_SCHEMA,
                    "move_id": "m002",
                    "kind": "note",
                    "note_kind": "observation",
                    "text": "forged schema",
                },
            ],
        ),
    )
    for session_name, schema_rows in schema_sessions:
        schema_session = workbench.Session(sessions_root, session_name)
        schema_session.directory.mkdir(parents=True)
        for row in schema_rows:
            schema_session.append(row)
        try:
            schema_session.moves()
        except SystemExit as error:
            if "requires schema" not in str(error):
                raise AssertionError(f"schema confusion lacked a bounded diagnostic: {error}")
        else:
            raise AssertionError(f"workbench accepted schema confusion in {session_name}")

    duplicate_id_session = workbench.Session(sessions_root, "duplicate-ids")
    duplicate_id_session.directory.mkdir(parents=True)
    duplicate_id_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    duplicate_id_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "note",
            "note_kind": "observation",
            "text": "first",
        }
    )
    duplicate_id_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "note",
            "note_kind": "observation",
            "text": "second",
        }
    )
    try:
        duplicate_id_session.moves()
    except SystemExit as error:
        if "duplicate move id" not in str(error):
            raise AssertionError(f"duplicate move id lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted duplicate move ids")

    move_id_sessions = (
        (
            "noncanonical-move-id",
            [
                {
                    "schema": workbench.SESSION_SCHEMA,
                    "move_id": "m001",
                    "kind": "session_opened",
                },
                {
                    "schema": workbench.MOVE_SCHEMA,
                    "move_id": "move-two",
                    "kind": "note",
                    "note_kind": "observation",
                    "text": "bad id",
                },
            ],
        ),
        (
            "gapped-move-id",
            [
                {
                    "schema": workbench.SESSION_SCHEMA,
                    "move_id": "m001",
                    "kind": "session_opened",
                },
                {
                    "schema": workbench.MOVE_SCHEMA,
                    "move_id": "m003",
                    "kind": "note",
                    "note_kind": "observation",
                    "text": "skipped m002",
                },
            ],
        ),
        (
            "zero-move-id",
            [
                {
                    "schema": workbench.SESSION_SCHEMA,
                    "move_id": "m000",
                    "kind": "session_opened",
                }
            ],
        ),
    )
    for session_name, move_id_rows in move_id_sessions:
        move_id_session = workbench.Session(sessions_root, session_name)
        move_id_session.directory.mkdir(parents=True)
        for row in move_id_rows:
            move_id_session.append(row)
        try:
            move_id_session.moves()
        except SystemExit as error:
            if "expected move id" not in str(error):
                raise AssertionError(f"move-id confusion lacked a bounded diagnostic: {error}")
        else:
            raise AssertionError(f"workbench accepted malformed move ids in {session_name}")

    invalid_lifecycle_session = workbench.Session(sessions_root, "invalid-lifecycle")
    invalid_lifecycle_session.directory.mkdir(parents=True)
    lifecycle_rows = [
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        },
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "session_closed",
        },
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m003",
            "kind": "note",
            "note_kind": "observation",
            "text": "after close",
        },
    ]
    for row in lifecycle_rows:
        invalid_lifecycle_session.append(row)
    try:
        invalid_lifecycle_session.moves()
    except SystemExit as error:
        if "final move" not in str(error):
            raise AssertionError(f"terminal lifecycle lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted a move after session_closed")

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

    missing_hash_session = workbench.Session(sessions_root, "missing-hash")
    missing_hash_session.directory.mkdir(parents=True)
    missing_hash_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    missing_hash_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/m002.lean",
            "kernel_receipt": {
                "verdict": "kernel_accepted",
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            },
        }
    )
    try:
        workbench.cmd_claim(
            type(
                "Args",
                (),
                {
                    "sessions_root": sessions_root,
                    "session": "missing-hash",
                    "probe": "m002",
                    "text": "must retain an exact input hash",
                },
            )(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "invalid input hash" not in str(error):
            raise AssertionError(f"missing input hash lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("claim accepted a probe without an input hash")

    invalid_hash_session = workbench.Session(sessions_root, "invalid-hash")
    invalid_hash_session.directory.mkdir(parents=True)
    invalid_hash_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    invalid_hash_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/m002.lean",
            "input_sha256": "not-a-sha256",
            "kernel_receipt": {
                "verdict": "kernel_accepted",
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            },
        }
    )
    try:
        workbench.cmd_claim(
            type(
                "Args",
                (),
                {
                    "sessions_root": sessions_root,
                    "session": "invalid-hash",
                    "probe": "m002",
                    "text": "must retain a canonical hash",
                },
            )(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "invalid input hash" not in str(error):
            raise AssertionError(f"invalid input hash lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("claim accepted a non-canonical input hash")

    contradictory_receipt_session = workbench.Session(sessions_root, "contradictory-receipt")
    contradictory_receipt_session.probes_dir.mkdir(parents=True)
    (contradictory_receipt_session.probes_dir / "m002.lean").write_text(
        "exact artifact\n", encoding="utf-8"
    )
    contradictory_receipt_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    contradictory_receipt_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/m002.lean",
            "input_sha256": workbench._sha256_text("exact artifact\n"),
            "kernel_receipt": {
                "verdict": "kernel_accepted",
                "exit_code": 1,
                "error_count": 1,
                "sorry_count": 0,
            },
        }
    )
    try:
        workbench.cmd_claim(
            type(
                "Args",
                (),
                {
                    "sessions_root": sessions_root,
                    "session": "contradictory-receipt",
                    "probe": "m002",
                    "text": "must reject contradictory receipts",
                },
            )(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "invalid kernel receipt" not in str(error):
            raise AssertionError(f"contradictory receipt lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("claim accepted a contradictory kernel receipt")

    missing_artifact_session = workbench.Session(sessions_root, "missing-artifact")
    missing_artifact_session.directory.mkdir(parents=True)
    missing_artifact_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    missing_artifact_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/m002.lean",
            "input_sha256": "0" * 64,
            "kernel_receipt": {
                "verdict": "kernel_accepted",
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            },
        }
    )
    try:
        workbench.cmd_claim(
            type(
                "Args",
                (),
                {
                    "sessions_root": sessions_root,
                    "session": "missing-artifact",
                    "probe": "m002",
                    "text": "must cite a stored artifact",
                },
            )(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "stored artifact" not in str(error):
            raise AssertionError(f"missing stored artifact lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("claim accepted a receipt without its stored artifact")

    mismatched_artifact_session = workbench.Session(sessions_root, "mismatched-artifact")
    mismatched_artifact_session.probes_dir.mkdir(parents=True)
    (mismatched_artifact_session.probes_dir / "m002.lean").write_text(
        "different bytes\n", encoding="utf-8"
    )
    mismatched_artifact_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    mismatched_artifact_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/m002.lean",
            "input_sha256": workbench._sha256_text("expected bytes\n"),
            "kernel_receipt": {
                "verdict": "kernel_accepted",
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            },
        }
    )
    try:
        workbench.cmd_claim(
            type(
                "Args",
                (),
                {
                    "sessions_root": sessions_root,
                    "session": "mismatched-artifact",
                    "probe": "m002",
                    "text": "must cite unchanged bytes",
                },
            )(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "does not match input hash" not in str(error):
            raise AssertionError(f"mismatched stored artifact lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("claim accepted a stored artifact with a mismatched hash")

    noncanonical_path_session = workbench.Session(sessions_root, "noncanonical-path")
    noncanonical_path_session.probes_dir.mkdir(parents=True)
    (noncanonical_path_session.probes_dir / "other.lean").write_text(
        "exact artifact\n", encoding="utf-8"
    )
    noncanonical_path_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    noncanonical_path_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/other.lean",
            "input_sha256": workbench._sha256_text("exact artifact\n"),
            "kernel_receipt": {
                "verdict": "kernel_accepted",
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            },
        }
    )
    try:
        workbench.cmd_claim(
            type(
                "Args",
                (),
                {
                    "sessions_root": sessions_root,
                    "session": "noncanonical-path",
                    "probe": "m002",
                    "text": "must use the move-owned path",
                },
            )(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "canonical input path" not in str(error):
            raise AssertionError(f"noncanonical input path lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("claim accepted a probe with a noncanonical artifact path")

    forged_claim_session = workbench.Session(sessions_root, "forged-claim")
    forged_claim_session.probes_dir.mkdir(parents=True)
    forged_source = "exact artifact\n"
    (forged_claim_session.probes_dir / "m002.lean").write_text(
        forged_source, encoding="utf-8"
    )
    forged_claim_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    forged_claim_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/m002.lean",
            "input_sha256": workbench._sha256_text(forged_source),
            "kernel_receipt": {
                "verdict": "kernel_accepted",
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            },
        }
    )
    forged_claim_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m003",
            "kind": "claim",
            "text": "forged claim",
            "cited_probe": "m002",
            "cited_input_sha256": "0" * 64,
            "authority": "manual_assertion",
        }
    )
    try:
        workbench.cmd_show(
            type("Args", (), {"sessions_root": sessions_root, "session": "forged-claim"})(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "invalid authority" not in str(error):
            raise AssertionError(f"forged claim lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("show accepted a forged claim record")

    stale_claim_session = workbench.Session(sessions_root, "stale-claim")
    stale_claim_session.probes_dir.mkdir(parents=True)
    stale_source = "exact artifact\n"
    stale_artifact = stale_claim_session.probes_dir / "m002.lean"
    stale_artifact.write_text(stale_source, encoding="utf-8")
    stale_claim_session.append(
        {
            "schema": workbench.SESSION_SCHEMA,
            "move_id": "m001",
            "kind": "session_opened",
        }
    )
    stale_claim_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m002",
            "kind": "probe",
            "input_path": "probes/m002.lean",
            "input_sha256": workbench._sha256_text(stale_source),
            "kernel_receipt": {
                "verdict": "kernel_accepted",
                "exit_code": 0,
                "error_count": 0,
                "sorry_count": 0,
            },
        }
    )
    stale_claim_session.append(
        {
            "schema": workbench.MOVE_SCHEMA,
            "move_id": "m003",
            "kind": "claim",
            "text": "valid then stale",
            "cited_probe": "m002",
            "cited_input_sha256": workbench._sha256_text(stale_source),
            "authority": "kernel_accepted_probe_receipt",
        }
    )
    stale_artifact.write_text("changed artifact\n", encoding="utf-8")
    try:
        workbench.cmd_show(
            type("Args", (), {"sessions_root": sessions_root, "session": "stale-claim"})(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "does not match input hash" not in str(error):
            raise AssertionError(f"stale claim lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("show exposed a claim after its probe artifact changed")

    incomplete_rows = (
        (
            "missing-note-text",
            {"schema": workbench.MOVE_SCHEMA, "move_id": "m002", "kind": "note", "note_kind": "observation"},
            "text",
        ),
        (
            "missing-claim-probe",
            {"schema": workbench.MOVE_SCHEMA, "move_id": "m002", "kind": "claim", "text": "claim"},
            "cited_probe",
        ),
        (
            "blank-claim-text",
            {"schema": workbench.MOVE_SCHEMA, "move_id": "m002", "kind": "claim", "text": ""},
            "claim text",
        ),
    )
    for session_name, row, field in incomplete_rows:
        reader_session = workbench.Session(sessions_root, session_name)
        reader_session.directory.mkdir(parents=True)
        reader_session.append(
            {
                "schema": workbench.SESSION_SCHEMA,
                "move_id": "m001",
                "kind": "session_opened",
            }
        )
        reader_session.append(row)
        try:
            workbench.cmd_show(
                type("Args", (), {"sessions_root": sessions_root, "session": session_name})(),
                workbench.repo_root(),
            )
        except SystemExit as error:
            if f"invalid {field}" not in str(error):
                raise AssertionError(
                    f"incomplete {session_name} lacked a bounded {field} diagnostic: {error}"
                )
        else:
            raise AssertionError(f"show accepted incomplete {session_name} row")


def check_session_lifecycle(sessions_root: Path) -> None:
    try:
        _run(
            sessions_root,
            [
                "open",
                "--session",
                "blank-actor",
                "--actor",
                " ",
                "--intent",
                "identity boundary",
            ],
        )
    except SystemExit as error:
        if "actor" not in str(error):
            raise AssertionError(f"blank actor lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted whitespace-only actor identity")
    _run(
        sessions_root,
        ["open", "--session", "blank-note", "--intent", "advisory note"],
    )
    try:
        _run(
            sessions_root,
            [
                "note",
                "--session",
                "blank-note",
                "--kind",
                "observation",
                "--text",
                " ",
            ],
        )
    except SystemExit as error:
        if "note text" not in str(error):
            raise AssertionError(f"blank note lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted whitespace-only note text")
    try:
        _run(
            sessions_root,
            [
                "open",
                "--session",
                "blank-intent",
                "--intent",
                " ",
            ],
        )
    except SystemExit as error:
        if "intent" not in str(error):
            raise AssertionError(f"blank session intent lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted whitespace-only session intent")
    _run(
        sessions_root,
        ["open", "--session", "blank-summary", "--intent", "closure summary"],
    )
    try:
        _run(
            sessions_root,
            [
                "close",
                "--session",
                "blank-summary",
                "--outcome",
                "open",
                "--summary",
                " ",
            ],
        )
    except SystemExit as error:
        if "summary" not in str(error):
            raise AssertionError(f"blank closure summary lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench accepted whitespace-only closure summary")
    _run(
        sessions_root,
        [
            "open",
            "--session",
            "unverified-established",
            "--intent",
            "establishment evidence",
        ],
    )
    try:
        _run(
            sessions_root,
            [
                "close",
                "--session",
                "unverified-established",
                "--outcome",
                "established",
                "--summary",
                "no evidence",
            ],
        )
    except SystemExit as error:
        if "kernel_accepted probe" not in str(error):
            raise AssertionError(f"unverified establishment lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("workbench established a session without accepted evidence")

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
    for command in (
        [
            "note",
            "--session",
            "t_lifecycle",
            "--kind",
            "observation",
            "--text",
            "after close",
        ],
        [
            "close",
            "--session",
            "t_lifecycle",
            "--outcome",
            "open",
            "--summary",
            "closed twice",
        ],
    ):
        try:
            _run(sessions_root, command)
        except SystemExit as error:
            if "already closed" not in str(error):
                raise AssertionError(f"closed-session mutation lacked a bounded diagnostic: {error}")
        else:
            raise AssertionError(f"workbench accepted {command[0]} after session closure")
    assert [row["kind"] for row in workbench.Session(sessions_root, "t_lifecycle").moves()] == [
        "session_opened",
        "note",
        "note",
        "session_closed",
    ]


def check_probe_runner_failures() -> None:
    real_run = workbench.subprocess.run
    failures = (
        (FileNotFoundError(2, "lake"), "lean_probe_unavailable"),
        (
            UnicodeDecodeError("utf-8", b"\xff", 0, 1, "invalid output"),
            "lean_probe_output_unreadable",
        ),
    )
    for failure, detail in failures:
        def raise_failure(*args, **kwargs):
            raise failure

        workbench.subprocess.run = raise_failure
        try:
            receipt = workbench.run_lean_probe(
                workbench.repo_root(), "example : True := by trivial\n"
            )
        finally:
            workbench.subprocess.run = real_run
        assert receipt["verdict"] == "probe_error"
        assert receipt["detail"] == detail
        assert receipt["exit_code"] is None


def check_environment_fingerprint_failures(tmp: Path) -> None:
    real_run = workbench.subprocess.run

    def unavailable(*args, **kwargs):
        raise FileNotFoundError(2, "git")

    workbench.subprocess.run = unavailable
    try:
        fingerprint = workbench.environment_fingerprint(workbench.repo_root())
        assert fingerprint["git_head"] == "git_head_unavailable"
        assert fingerprint["dirty_path_count"] == 0
        opened = workbench.cmd_open(
            type(
                "Args",
                (),
                {
                    "sessions_root": tmp / "fingerprint-sessions",
                    "session": "degraded-fingerprint",
                    "actor": "outsider",
                    "intent": "fingerprint boundary",
                },
            )(),
            workbench.repo_root(),
        )
    finally:
        workbench.subprocess.run = real_run
    assert opened["environment_fingerprint"]["git_head"] == "git_head_unavailable"


def check_session_storage_failures(tmp: Path) -> None:
    blocked_root = tmp / "sessions-root-file"
    blocked_root.write_text("not a directory\n", encoding="utf-8")
    try:
        workbench.cmd_open(
            type(
                "Args",
                (),
                {
                    "sessions_root": blocked_root,
                    "session": "blocked-root",
                    "actor": "outsider",
                    "intent": "storage boundary",
                },
            )(),
            workbench.repo_root(),
        )
    except SystemExit as error:
        if "cannot create workbench session" not in str(error):
            raise AssertionError(f"blocked session root lacked a bounded diagnostic: {error}")
    else:
        raise AssertionError("session creation leaked a filesystem failure")

    sessions_root = tmp / "append-failure-sessions"
    session = workbench.Session(sessions_root, "append-failure")
    session.directory.mkdir(parents=True)
    session.ledger_path.touch()
    real_open = workbench.Path.open

    def fail_ledger_open(path: Path, *args, **kwargs):
        if path == session.ledger_path:
            raise PermissionError(13, "ledger storage denied")
        return real_open(path, *args, **kwargs)

    workbench.Path.open = fail_ledger_open
    try:
        try:
            session.append({"schema": workbench.MOVE_SCHEMA, "move_id": "m001", "kind": "note"})
        except SystemExit as error:
            if "cannot append workbench ledger" not in str(error):
                raise AssertionError(f"ledger append lacked a bounded diagnostic: {error}")
        else:
            raise AssertionError("ledger append leaked a filesystem failure")
    finally:
        workbench.Path.open = real_open


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
                "--actor",
                "human:alice",
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
        try:
            _run(
                sessions_root,
                [
                    "claim",
                    "--session",
                    "t_claims",
                    "--text",
                    " ",
                    "--probe",
                    accepted["move_id"],
                ],
            )
        except SystemExit as error:
            if "claim text" not in str(error):
                raise AssertionError(f"blank claim lacked a bounded diagnostic: {error}")
        else:
            raise AssertionError("claim accepted whitespace-only credit")
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
        destination = sessions_root / "t_claims" / "probes" / "m004.lean"
        outside = tmp / "probe-destination-outside.lean"
        outside.write_text("outside sentinel\n", encoding="utf-8")
        destination.symlink_to(outside)
        calls_before_destination = len(calls)
        refused_destination_link = False
        try:
            _run(
                sessions_root,
                [
                    "probe",
                    "--session",
                    "t_claims",
                    "--file",
                    str(good),
                ],
            )
        except SystemExit as error:
            refused_destination_link = "symbolic links" in str(error)
        assert refused_destination_link, "probe followed a symlinked destination"
        assert len(calls) == calls_before_destination
        assert outside.read_text(encoding="utf-8") == "outside sentinel\n"

        destination.unlink()
        destination.write_text("existing sentinel\n", encoding="utf-8")
        refused_existing_destination = False
        try:
            _run(
                sessions_root,
                [
                    "probe",
                    "--session",
                    "t_claims",
                    "--file",
                    str(good),
                ],
            )
        except SystemExit as error:
            refused_existing_destination = "already exists" in str(error)
        assert refused_existing_destination, "probe overwrote an existing destination"
        assert destination.read_text(encoding="utf-8") == "existing sentinel\n"

        destination.unlink()
        real_copy = workbench.shutil.copyfile
        workbench.shutil.copyfile = lambda *args, **kwargs: (_ for _ in ()).throw(
            PermissionError(13, "session storage denied")
        )
        refused_copy_failure = False
        try:
            _run(
                sessions_root,
                [
                    "probe",
                    "--session",
                    "t_claims",
                    "--file",
                    str(good),
                ],
            )
        except SystemExit as error:
            refused_copy_failure = "could not be stored" in str(error)
        finally:
            workbench.shutil.copyfile = real_copy
        assert refused_copy_failure, "probe leaked a storage copy failure"
        assert len(calls) == calls_before_destination
        assert not destination.exists()
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
        shown = _run(sessions_root, ["show", "--session", "t_claims"])
        shown_open = shown["moves"][0]
        assert shown_open["actor"] == "human:alice"
        assert shown_open["intent"] == "claim gate"
        shown_probe = shown["moves"][1]
        assert shown_probe["input_path"] == "probes/m002.lean"
        assert shown_probe["input_sha256"] == accepted["input_sha256"]
        assert shown_probe["kernel_receipt"]["verdict"] == "kernel_accepted"
        shown_claim = shown["moves"][3]
        assert shown_claim["cited_probe"] == accepted["move_id"]
        assert shown_claim["cited_input_sha256"] == accepted["input_sha256"]
        assert shown_claim["authority"] == "kernel_accepted_probe_receipt"
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
        established = _run(
            sessions_root,
            [
                "close",
                "--session",
                "t_claims",
                "--outcome",
                "established",
                "--summary",
                "accepted claim",
            ],
        )
        assert established["kernel_accepted_probes"] == 1
    finally:
        workbench.run_lean_probe = real_runner


def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        check_session_path_boundaries(tmp)
        check_replay_path_boundary(tmp)
        check_replay_receipt_boundary(tmp)
        check_malformed_ledger_boundary(tmp)
        check_probe_runner_failures()
        check_environment_fingerprint_failures(tmp)
        check_session_storage_failures(tmp)
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
