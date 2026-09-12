#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the finite computations cited by the Erdős 251 reasoning paper."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
CASES = {
    "continued-fraction": (
        "certified_continued_fraction.py",
        ["--problem", "erdos_251", "--scale-bits", "80000"],
        "certified-cf.json",
    ),
    "adjacent-mismatch": (
        "erdos251_adjacent_mismatch_density.py",
        ["--limit", "120000000", "--max-h", "16", "--bands", "8", "--json"],
        "adjacent-mismatch.json",
    ),
    "free-pair": (
        "erdos251_free_pair_and_state_compression.py",
        ["--limit", "20000000", "--max-t", "20", "--late-frac", "0.90",
         "--witness-slack", "200", "--precision-bits", "4096", "--json"],
        "free-pair.json",
    ),
}


def differences(expected: object, actual: object, path: str = "result") -> list[str]:
    """Compare integers exactly and diagnostic floats within stated tolerances."""
    if isinstance(expected, float) and isinstance(actual, (float, int)):
        if math.isfinite(actual) and math.isclose(expected, actual, rel_tol=1e-12, abs_tol=1e-12):
            return []
        return [path]
    if type(expected) is not type(actual):
        return [path]
    if isinstance(expected, dict):
        if expected.keys() != actual.keys():
            return [path + ".keys"]
        return [p for key, value in expected.items()
                for p in differences(value, actual[key], f"{path}.{key}")]
    if isinstance(expected, list):
        if len(expected) != len(actual):
            return [path + ".length"]
        return [p for index, (left, right) in enumerate(zip(expected, actual))
                for p in differences(left, right, f"{path}[{index}]")]
    return [] if expected == actual else [path]


def recorded_case(name: str) -> dict:
    program, args, receipt = CASES[name]
    record = json.loads((ROOT / "receipts" / receipt).read_text(encoding="utf-8"))
    if record.get("schema") != "erdos251-public-computation/1":
        raise ValueError(f"{name}: unknown receipt schema")
    if record.get("program") != program or record.get("arguments") != args:
        raise ValueError(f"{name}: receipt does not match the replay command")
    digest = hashlib.sha256((ROOT / program).read_bytes()).hexdigest()
    if record.get("program_sha256") != digest:
        raise ValueError(f"{name}: program changed; the saved run does not cover these bytes")
    if record.get("verification_scope") != "finite_computation_only" or not isinstance(record.get("result"), dict):
        raise ValueError(f"{name}: missing finite-computation boundary or result")
    return record


def replay(name: str, timeout: int) -> dict:
    record = recorded_case(name)
    program, args, _ = CASES[name]
    env = dict(os.environ)
    for key in ("PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP", "PYTHONINSPECT"):
        env.pop(key, None)
    started = time.monotonic()
    result = subprocess.run(
        [sys.executable, str(ROOT / program), *args], cwd=ROOT,
        capture_output=True, text=True, env=env, timeout=timeout, check=False,
    )
    if result.returncode:
        raise ValueError(f"{name}: computation exited {result.returncode}: {result.stderr.strip() or result.stdout[-1000:]}")
    actual = json.loads(result.stdout)
    changed = differences(record["result"], actual)
    if changed:
        raise ValueError(f"{name}: recorded result differs at {', '.join(changed[:8])}")
    return {"case": name, "matched_recorded_result": True,
            "elapsed_seconds": round(time.monotonic() - started, 2),
            "verification_scope": "finite_computation_only",
            "lean_kernel_run": False,
            "comparison": "integers exact; diagnostic floats rel_tol=abs_tol=1e-12"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=[*CASES, "all"], default="continued-fraction")
    parser.add_argument("--check", action="store_true", help="check saved program identities without rerunning scans")
    parser.add_argument("--timeout", type=int, default=300, help="seconds allowed per computation")
    args = parser.parse_args()
    if args.timeout < 1:
        parser.error("--timeout must be positive")
    try:
        if args.check:
            for name in CASES:
                recorded_case(name)
            print("Three finite-computation records match their programs; scans were not rerun.")
        else:
            for name in CASES if args.case == "all" else [args.case]:
                print(json.dumps(replay(name, args.timeout), indent=2))
            print("These finite calculations do not prove irrationality or cofinality. No Lean kernel ran.")
    except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
