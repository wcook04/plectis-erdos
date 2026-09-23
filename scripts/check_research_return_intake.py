#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Validate a pull-request return with the sidecar required by its track."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

import validate_research_return as return_validator


ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = ROOT / "scripts" / "validate_research_return.py"


def validation_arguments(return_path: Path, route_path: Path) -> list[str] | None:
    """Select the public validator without granting one track another's evidence."""
    if return_path.is_symlink() or route_path.is_symlink():
        raise ValueError("intake artifacts must be regular files, not symbolic links")
    if not return_path.exists():
        if route_path.exists():
            raise ValueError("route-memory.json requires its return.json intake artifact")
        return None
    try:
        returned = json.loads(return_validator.read_regular_text(return_path, label="return.json"))
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read return.json: {exc}") from exc
    frontier = returned.get("frontier") if isinstance(returned, dict) else None
    track = frontier.get("track", "mathematics") if isinstance(frontier, dict) else None
    if track not in {"mathematics", "architecture"}:
        raise ValueError("return.json frontier.track must be mathematics or architecture")
    command = [
        sys.executable,
        str(VALIDATOR),
        str(return_path),
        "--require-submitted",
        "--check-git",
    ]
    if track == "mathematics":
        if not route_path.is_file():
            raise ValueError("mathematics return.json requires route-memory.json")
        command.extend(["--require-route-memory-receipt", "--route-memory-receipt", str(route_path)])
    elif route_path.exists():
        raise ValueError("architecture return.json must omit route-memory.json")
    return command


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--return-json", type=Path, default=Path("return.json"))
    parser.add_argument("--route-memory-receipt", type=Path, default=Path("route-memory.json"))
    args = parser.parse_args()
    try:
        command = validation_arguments(args.return_json, args.route_memory_receipt)
    except ValueError as exc:
        print(f"research return intake: {exc}", file=sys.stderr)
        return 1
    if command is None:
        return 0
    return subprocess.run(command, cwd=ROOT, check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
