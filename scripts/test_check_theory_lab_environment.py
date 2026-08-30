#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise theory-lab Git checks from an environment-neutral child process."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "scripts" / "check_theory_lab.py"


def main() -> int:
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
