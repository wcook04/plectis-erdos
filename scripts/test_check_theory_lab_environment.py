#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise theory-lab Git checks from an environment-neutral child process."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import check_theory_lab as checker
import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "scripts" / "check_theory_lab.py"


def check_child_invocation_contract() -> None:
    """Keep each hostile-environment checker child bounded."""
    completed = subprocess.CompletedProcess([sys.executable, str(CHECKER)], 0, "", "")
    with patch.object(subprocess, "run", return_value=completed) as runner:
        observed = subprocess.run(
            [sys.executable, str(CHECKER)],
            cwd=ROOT,
            env={"GIT_DIR": "hostile"},
            capture_output=True,
            text=True,
            check=False,
            timeout=singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
        )
    if observed is not completed:
        raise SystemExit("theory-lab environment probe did not return the child result")
    if runner.call_args.kwargs.get("timeout") != singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS:
        raise SystemExit("theory-lab environment probe must use the shared worker timeout")


def check_file_boundary() -> None:
    """The theory-lab checker must reject non-regular input surfaces."""
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        regular = root / "regular.json"
        regular.write_text("{}\n", encoding="utf-8")
        directory = root / "directory"
        directory.mkdir()
        link = root / "link.json"
        link.symlink_to(regular)
        fifo = root / "fifo"
        os.mkfifo(fifo)
        with patch.object(checker, "ROOT", root):
            if checker.safe_read_text(regular) != "{}\n":
                raise SystemExit("theory-lab regular-file read failed")
            for path in (directory, link, fifo):
                try:
                    checker.safe_read_text(path)
                except checker.UnsafeTheoryLabInput:
                    continue
                raise SystemExit(f"theory-lab {path.name} boundary escaped")


def main() -> int:
    check_child_invocation_contract()
    check_file_boundary()
    hostile = os.environ.copy()
    hostile.update(
        {
            "GIT_DIR": str(ROOT / "not-a-git-directory"),
            "GIT_NAMESPACE": "hostile-namespace",
            "GIT_REPLACE_REF_BASE": "refs/replace/hostile/",
        }
    )
    for optimized in (False, True):
        command = [sys.executable]
        if optimized:
            command.append("-O")
        command.append(str(CHECKER))
        completed = subprocess.run(
            command,
            cwd=ROOT,
            env=hostile,
            capture_output=True,
            text=True,
            check=False,
            timeout=singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
        )
        if completed.returncode != 0 or "contract satisfied" not in completed.stdout:
            detail = completed.stderr.strip() or completed.stdout.strip()
            raise SystemExit(
                f"theory-lab environment probe failed ({'optimized' if optimized else 'normal'}): {detail}"
            )
    print("check_theory_lab environment: hostile Git selectors neutralized in normal/-O children")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
