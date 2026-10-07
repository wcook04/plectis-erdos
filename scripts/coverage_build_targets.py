#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Print the coverage build's Lean targets, one per line.

`.github/workflows/lean-coverage-build.yml` owns the list (its
`coverage-build` step, pinned by `scripts/test_lean_fast_build.py`). The
argument-graph export imports these targets with the default roots, so that
the declarations the paper-to-Lean ledger cites from coverage-only modules
are in its environment. With ``--imports`` the lines are Lean `import`
commands. Standard library only: the export job runs it before any package
installation.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "lean-coverage-build.yml"
TARGET = re.compile(r"^\s+((?:ErdosProblems|Erdos249257)(?:\.[A-Za-z0-9_']+)*)\s*$")


def targets(workflow: Path = WORKFLOW) -> list[str]:
    lines = workflow.read_text(encoding="utf-8").splitlines()
    try:
        start = next(i for i, line in enumerate(lines) if line.strip() == "id: coverage-build")
    except StopIteration:
        raise SystemExit(f"{workflow}: no step with id coverage-build") from None
    out: list[str] = []
    seen_flag = False
    for line in lines[start:]:
        if not seen_flag:
            seen_flag = "--lake-staleness" in line
            continue
        match = TARGET.match(line)
        if not match:
            break
        out.append(match.group(1))
    if not out:
        raise SystemExit(f"{workflow}: the coverage-build step lists no targets")
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--imports", action="store_true", help="print Lean import commands")
    args = parser.parse_args(argv)
    for target in targets():
        print(f"import {target}" if args.imports else target)
    return 0


if __name__ == "__main__":
    sys.exit(main())
