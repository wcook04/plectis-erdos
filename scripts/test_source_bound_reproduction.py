#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused tests for the source-bound reproduction receipt."""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import patch

import run_source_bound_reproduction as subject


def require(condition: bool, message: str) -> None:
    """Keep reproduction assurance failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def expect_failure(action, fragment: str) -> None:
    try:
        action()
    except subject.ReproductionError as error:
        require(
            fragment in str(error),
            f"expected error containing {fragment!r}, got {error!s}",
        )
    else:
        raise AssertionError(f"expected ReproductionError containing {fragment!r}")


def tiny_plan() -> list[dict]:
    return [
        subject.command(
            "quiet",
            [sys.executable, "-c", "pass"],
            expect_empty_stdout=True,
            expect_empty_stderr=True,
        ),
        subject.command(
            "isolated_write",
            [
                sys.executable,
                "-c",
                (
                    "from pathlib import Path; "
                    "Path('.lake').mkdir(exist_ok=True); "
                    "Path('.lake/only-in-copy').write_text('ok')"
                ),
            ],
            expect_empty_stdout=True,
            expect_empty_stderr=True,
        ),
    ]


def make_source(root: Path) -> None:
    (root / "included").mkdir()
    (root / "included" / "a.txt").write_text("alpha\n")
    (root / ".git").mkdir()
    (root / ".git" / "state").write_text("ignored\n")
    (root / ".lake").mkdir()
    (root / ".lake" / "cache").write_text("ignored\n")
    (root / "__pycache__").mkdir()
    (root / "__pycache__" / "x.pyc").write_bytes(b"ignored")
    (root / ".DS_Store").write_bytes(b"ignored")


def test_hashing_and_exclusions(source: Path) -> None:
    first = subject.source_identity(source)
    (source / ".git" / "state").write_text("changed but excluded\n")
    (source / ".lake" / "cache").write_text("changed but excluded\n")
    require(
        subject.source_identity(source) == first,
        "excluded checkout state changed the source identity",
    )
    (source / "included" / "a.txt").write_text("beta\n")
    require(
        subject.source_identity(source)["source_digest"] != first["source_digest"],
        "included source mutation did not change the source digest",
    )
    (source / "included" / "a.txt").write_text("alpha\n")
    require(
        subject.source_identity(source) == first,
        "restored source did not recover its original identity",
    )


def test_isolation_success_and_validation(source: Path, plan: list[dict]) -> dict:
    receipt = subject.execute(source, plan)
    require(
        not (source / ".lake" / "only-in-copy").exists(),
        "isolated execution leaked a write into the source checkout",
    )
    subject.validate_receipt(receipt, source, plan)
    return receipt


def test_environment_isolation(source: Path) -> None:
    plan = [
        subject.command(
            "environment",
            [
                sys.executable,
                "-c",
                (
                    "import os; "
                    "assert os.environ.get('GIT_DIR') is None; "
                    "assert os.environ.get('GIT_NAMESPACE') is None; "
                    "assert os.environ.get('GIT_REPLACE_REF_BASE') is None; "
                    "assert os.environ.get('PYTHONPATH') != 'hostile-pythonpath'; "
                    "assert os.environ.get('LC_ALL') == 'C.UTF-8'; "
                    "assert os.environ.get('LANG') == 'C.UTF-8'"
                ),
            ],
            expect_empty_stdout=True,
            expect_empty_stderr=True,
        )
    ]
    hostile = {
        "GIT_DIR": str(source / "not-a-git-directory"),
        "GIT_NAMESPACE": "hostile-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/hostile/",
        "PYTHONPATH": "hostile-pythonpath",
        "LC_ALL": "C",
        "LANG": "C",
    }
    with patch.dict(os.environ, hostile, clear=False):
        receipt = subject.execute(source, plan)
    subject.validate_receipt(receipt, source, plan)
    require(
        receipt["environment_contract"] == subject.ENVIRONMENT_CONTRACT,
        "reproduction receipt lost its environment contract",
    )


def test_command_timeout() -> None:
    spec = subject.command("bounded", [sys.executable, "-c", "pass"])
    completed = subprocess.CompletedProcess(
        spec["argv"], returncode=0, stdout=b"", stderr=b""
    )
    with patch.object(subject.subprocess, "run", return_value=completed) as runner:
        result = subject.run_command(spec, Path("/isolated-source"))
    require(result["exit_code"] == 0, "bounded source command did not complete")
    require(runner.call_args is not None, "bounded source command was not invoked")
    require(
        runner.call_args.kwargs["timeout"] == subject.COMMAND_TIMEOUT_SECONDS,
        "source-bound command lost its worker timeout",
    )


def test_toolchain_path_is_not_ambient() -> None:
    hostile = {
        "PATH": "/private/host-toolchain/bin",
        "GIT_DIR": "/private/host.git",
        "GIT_NAMESPACE": "hostile-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replace/hostile/",
    }
    with patch.dict(os.environ, hostile, clear=False):
        with patch.object(
            subject.shutil,
            "which",
            side_effect=AssertionError("ambient executable lookup was used"),
        ):
            environment = subject.execution_environment(["lake", "build"])
    require(
        environment["PATH"]
        == os.pathsep.join((str(subject.TOOLCHAIN_BIN), os.defpath)),
        "source-bound Lean commands did not use the pinned toolchain path",
    )
    for key in ("GIT_DIR", "GIT_NAMESPACE", "GIT_REPLACE_REF_BASE"):
        require(key not in environment, f"source-bound environment retained {key}")


def test_rejections(source: Path, plan: list[dict], receipt: dict) -> None:
    changed_source = source.parent / "changed"
    subject.copy_source(source, changed_source)
    (changed_source / "included" / "a.txt").write_text("different\n")
    expect_failure(
        lambda: subject.validate_receipt(receipt, changed_source, plan),
        "source identity mismatch",
    )

    missing = copy.deepcopy(receipt)
    missing["command_results"].pop()
    expect_failure(
        lambda: subject.validate_receipt(missing, source, plan),
        "missing required command result",
    )

    nonzero = copy.deepcopy(receipt)
    nonzero["command_results"][0]["exit_code"] = 9
    expect_failure(
        lambda: subject.validate_receipt(nonzero, source, plan),
        "exited nonzero",
    )

    noisy = copy.deepcopy(receipt)
    noisy["command_results"][0]["stdout_bytes"] = 1
    expect_failure(
        lambda: subject.validate_receipt(noisy, source, plan),
        "empty-stdout expectation",
    )

    malformed = copy.deepcopy(receipt)
    malformed["command_results"][0]["stdout_sha256"] = "g" * 64
    expect_failure(
        lambda: subject.validate_receipt(malformed, source, plan),
        "SHA-256",
    )

    stale = copy.deepcopy(receipt)
    old = datetime.now(timezone.utc) - timedelta(days=2)
    stale["started_at"] = old.isoformat()
    stale["completed_at"] = (old + timedelta(seconds=1)).isoformat()
    expect_failure(
        lambda: subject.validate_receipt(
            stale,
            source,
            plan,
            max_age_seconds=60,
        ),
        "stale",
    )


def test_timestamp_and_tail_rejections(
    source: Path, plan: list[dict], receipt: dict
) -> None:
    reversed_time = copy.deepcopy(receipt)
    row = reversed_time["command_results"][0]
    row["started_at"], row["completed_at"] = row["completed_at"], row["started_at"]
    expect_failure(
        lambda: subject.validate_receipt(reversed_time, source, plan),
        "completion precedes",
    )

    tail_mismatch = copy.deepcopy(receipt)
    tail_mismatch["command_results"][0]["stdout_tail_base64"] = "YQ=="
    expect_failure(
        lambda: subject.validate_receipt(tail_mismatch, source, plan),
        "tail length mismatch",
    )


def test_git_capability_refusal(source: Path) -> None:
    git_plan = [
        subject.command(
            "never_run",
            [
                sys.executable,
                "-c",
                (
                    "from pathlib import Path; "
                    "assert Path('.git/state').read_text()"
                ),
            ],
            requires_git=True,
        )
    ]
    expect_failure(
        lambda: subject.execute(source, git_plan),
        "requires_git",
    )
    receipt = subject.execute(source, git_plan, allow_git=True)
    subject.validate_receipt(receipt, source, git_plan)


def test_canonical_receipt_round_trip(
    source: Path, plan: list[dict], receipt: dict
) -> None:
    identity_before = subject.source_identity(source)
    receipt_path = source / subject.CANONICAL_RECEIPT_PATH
    subject.write_receipt(receipt_path, receipt, overwrite=False)
    require(
        subject.source_identity(source) == identity_before,
        "writing the canonical receipt changed source identity",
    )
    loaded = json.loads(receipt_path.read_text())
    subject.validate_receipt(loaded, source, plan)


def test_overwrite_guard(root: Path) -> None:
    receipt_path = root / "receipt.json"
    receipt_path.write_text("{}\n")
    expect_failure(
        lambda: subject.write_receipt(receipt_path, {"ok": True}, overwrite=False),
        "already exists",
    )
    subject.write_receipt(receipt_path, {"ok": True}, overwrite=True)
    require(
        json.loads(receipt_path.read_text()) == {"ok": True},
        "overwrite guard did not write the requested receipt",
    )


def test_file_boundaries(root: Path) -> None:
    plan_path = root / "plan.json"
    plan_path.write_text(json.dumps(tiny_plan()), encoding="utf-8")
    plan_link = root / "plan-link.json"
    plan_link.symlink_to(plan_path)
    expect_failure(
        lambda: subject.load_plan(plan_link),
        "command plan path contains a symlink",
    )
    plan_fifo = root / "plan.fifo"
    os.mkfifo(plan_fifo)
    expect_failure(
        lambda: subject.load_plan(plan_fifo),
        "command plan path is not a regular file",
    )

    sentinel = root / "receipt-sentinel.json"
    sentinel.write_text("sentinel\n", encoding="utf-8")
    receipt_link = root / "receipt-link.json"
    receipt_link.symlink_to(sentinel)
    expect_failure(
        lambda: subject.write_receipt(receipt_link, {"ok": True}, overwrite=True),
        "receipt destination contains a symlink",
    )
    require(
        sentinel.read_text(encoding="utf-8") == "sentinel\n",
        "symlinked receipt destination modified its target",
    )
    receipt_fifo = root / "receipt.fifo"
    os.mkfifo(receipt_fifo)
    expect_failure(
        lambda: subject.write_receipt(receipt_fifo, {"ok": True}, overwrite=True),
        "receipt destination is not a regular file",
    )


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="source-bound-repro-test-") as temp:
        root = Path(temp)
        source = root / "source"
        source.mkdir()
        make_source(source)
        plan = tiny_plan()
        test_hashing_and_exclusions(source)
        receipt = test_isolation_success_and_validation(source, plan)
        test_environment_isolation(source)
        test_command_timeout()
        test_toolchain_path_is_not_ambient()
        test_rejections(source, plan, receipt)
        test_timestamp_and_tail_rejections(source, plan, receipt)
        test_git_capability_refusal(source)
        test_canonical_receipt_round_trip(source, plan, receipt)
        test_overwrite_guard(root)
        test_file_boundaries(root)
    print(
        "source-bound reproduction tests passed: hashing, exclusions, isolation, "
        "validation, rejection classes, Git gate, canonical receipt, overwrite guard"
        ", and file boundaries"
    )


if __name__ == "__main__":
    main()
