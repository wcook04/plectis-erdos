#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the finite computations cited by the long Erdos 1049 paper.

Each case reruns one program in this directory and compares its output with
the saved receipt under receipts/.  Every recorded value is an integer, a
string or a boolean, so the comparison is exact.  The programs use only the
Python standard library.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
SCHEMA = "erdos1049-public-computation/1"
CASES = {
    "threshold-digits": ("threshold_digits.py", [], "threshold-digits.json"),
    "rational-base-examples": ("rational_base_examples.py", [], "rational-base-examples.json"),
    "parameter-box": ("parameter_box.py", [], "parameter-box.json"),
    "source-polynomials": ("source_polynomials.py", [], "source-polynomials.json"),
    "cyclotomic-content": ("cyclotomic_content.py", [], "cyclotomic-content.json"),
    "main-term-31-4": ("main_term_31_4.py", [], "main-term-31-4.json"),
    "hankel-qorder": ("hankel_qorder.py", [], "hankel-qorder.json"),
}


def first_difference(expected: object, actual: object, path: str = "result") -> str | None:
    if type(expected) is not type(actual):
        return path
    if isinstance(expected, dict):
        if expected.keys() != actual.keys():
            return path + ".keys"
        for key in expected:
            found = first_difference(expected[key], actual[key], f"{path}.{key}")
            if found:
                return found
        return None
    if isinstance(expected, list):
        if len(expected) != len(actual):
            return path + ".length"
        for index, (left, right) in enumerate(zip(expected, actual)):
            found = first_difference(left, right, f"{path}[{index}]")
            if found:
                return found
        return None
    return None if expected == actual else path


def recorded_case(name: str) -> dict:
    program, args, receipt = CASES[name]
    record = json.loads((ROOT / "receipts" / receipt).read_text(encoding="utf-8"))
    if record.get("schema") != SCHEMA:
        raise ValueError(f"{name}: unknown receipt schema")
    if record.get("program") != program or record.get("arguments") != args:
        raise ValueError(f"{name}: receipt does not match the replay command")
    digest = hashlib.sha256((ROOT / program).read_bytes()).hexdigest()
    if record.get("program_sha256") != digest:
        raise ValueError(f"{name}: program changed; the saved run does not cover these bytes")
    result = record.get("result")
    if record.get("verification_scope") != "finite_computation_only" or not isinstance(result, dict):
        raise ValueError(f"{name}: missing finite-computation boundary or result")
    if result.get("all_printed_claims_verified") is not True:
        raise ValueError(f"{name}: the saved run does not verify the printed claims")
    return record


def replay(name: str, timeout: int) -> dict:
    record = recorded_case(name)
    program, args, _ = CASES[name]
    env = dict(os.environ)
    for key in ("PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP", "PYTHONINSPECT"):
        env.pop(key, None)
    started = time.monotonic()
    try:
        completed = subprocess.run(
            [sys.executable, str(ROOT / program), *args], cwd=ROOT,
            capture_output=True, text=True, env=env, timeout=timeout, check=False,
        )
    except subprocess.TimeoutExpired:
        raise ValueError(f"{name}: timed out after {timeout} seconds; raise --timeout") from None
    if completed.returncode:
        raise ValueError(f"{name}: program exited {completed.returncode}: "
                         f"{completed.stderr.strip()[-1000:] or completed.stdout[-1000:]}")
    actual = json.loads(completed.stdout)
    changed = first_difference(record["result"], actual)
    if changed:
        raise ValueError(f"{name}: recorded result differs at {changed}")
    return {"case": name, "matched_recorded_result": True,
            "elapsed_seconds": round(time.monotonic() - started, 1),
            "verification_scope": "finite_computation_only",
            "lean_kernel_run": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--case", choices=[*CASES, "all"], default="all")
    parser.add_argument("--check", action="store_true",
                        help="check saved program hashes and receipt shape without rerunning")
    parser.add_argument("--timeout", type=int, default=900, help="seconds allowed per case")
    args = parser.parse_args()
    if args.timeout < 1:
        parser.error("--timeout must be positive")
    names = list(CASES) if args.case == "all" else [args.case]
    try:
        if args.check:
            for name in names:
                recorded_case(name)
            print(f"{len(names)} saved receipts match their programs; nothing was rerun.")
        else:
            for name in names:
                print(json.dumps(replay(name, args.timeout), indent=2), flush=True)
            print("These finite calculations prove only the stated finite comparisons. No Lean kernel ran.")
    except (OSError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
