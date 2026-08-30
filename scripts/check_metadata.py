#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Validate release citation metadata with the CI-pinned command."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parent.parent
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"


def execution_environment(executable: str) -> dict[str, str]:
    """Keep the pinned validator discoverable without inheriting ambient state."""
    environment = singleflight.command_environment()
    executable_directory = str(Path(executable).resolve().parent)
    environment["PATH"] = os.pathsep.join(
        (executable_directory, environment["PATH"])
    )
    return environment


def main() -> int:
    cffconvert = shutil.which("cffconvert")
    if cffconvert is None:
        print(
            "cffconvert is required; install it with: python3 -m pip install cffconvert",
            file=sys.stderr,
        )
        return 2
    return subprocess.run(
        [cffconvert, "--validate"],
        cwd=ROOT,
        env=execution_environment(cffconvert),
        check=False,
        timeout=singleflight.GIT_COMMAND_TIMEOUT_SECONDS,
    ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
