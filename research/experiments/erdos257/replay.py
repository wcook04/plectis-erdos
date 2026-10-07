#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the finite computations cited by the Erdős #257 long paper."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
SCHEMA = "erdos257-public-computation/1"
LADDER_STDLIB = [str(j) for j in range(3, 17)]
LADDER_NUMPY = [str(j) for j in range(17, 23)]
MACRO_OUTPUTS = (
    "/tmp/coefficient_selected_423377.csv",
    "/tmp/coefficient_support_423377.bin",
    "/tmp/coefficient_selected_final.csv",
    "/tmp/coefficient_support_final.bin",
)

# name: (program, arguments, receipt, kind, needs)
CASES = {
    "truncation-ladder": ("check_truncation_rung_ladder.py", ["ladder", *LADDER_STDLIB],
                          "truncation-ladder-3-16.json", "jsonl", "stdlib"),
    "truncation-ladder-numpy": ("check_truncation_rung_ladder.py", ["ladder", *LADDER_NUMPY],
                                "truncation-ladder-17-22.json", "jsonl", "numpy"),
    "quotient-identity": ("check_master_identity.py", [], "quotient-identity-200.json",
                          "json", "stdlib"),
    "seam-2500": ("check_seam_reset_crossing.py", ["2500", "{out}"], "seam-reset-crossing-2500.json",
                  "seam", "stdlib"),
    "tail-margins-3000": ("check_half_greedy_margins.py", ["3000", "600", "{out}"],
                          "tail-margins-3000.json", "margins", "stdlib"),
    "seam-200000": ("seam_orbit_replay.py", [], "seam-orbit-200000.json", "json", "stdlib"),
    "greedy-prefix-200000": ("certify_greedy_interval.py",
                             ["--horizon", "200000", "--no-compare", "--check", "--stdout"],
                             "greedy-prefix-200000.json", "json", "stdlib"),
    "greedy-prefix-100000": ("certify_greedy_interval.py",
                             ["--horizon", "100000", "--check", "--stdout"],
                             "greedy-prefix-100000.json", "json", "stdlib"),
    "coefficient-macro": ("half_prefix_coefficient_macro_verify.cpp", [],
                          "coefficient-macro-13548057.json", "cpp", "c++ and GMP"),
}
QUICK = ["truncation-ladder", "quotient-identity", "tail-margins-3000"]
# Default time limits in seconds; --timeout overrides them for every case.
TIMEOUTS = {"truncation-ladder-numpy": 1200, "seam-200000": 1800,
            "greedy-prefix-200000": 900, "greedy-prefix-100000": 600}
# Timing and path fields differ from run to run; they are not part of the result.
IGNORED = {"elapsed", "wall_time_seconds", "jsonl_path", "script_path", "notes"}


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


def strip(value: object) -> object:
    if isinstance(value, dict):
        return {k: strip(v) for k, v in value.items() if k not in IGNORED}
    if isinstance(value, list):
        return [strip(v) for v in value]
    return value


def seam_ledger_statistics(jsonl: Path) -> dict:
    """Exact counts and margin statistics derived from the seam ledger."""
    rows = [json.loads(line) for line in jsonl.read_text(encoding="utf-8").splitlines()]
    resets = [r for r in rows if r["kind"] == "reset"]
    in_scope = [r["margin"] for r in resets if r["row"] >= 14]
    return {
        "resets": len(resets),
        "upper_resets": sum(r["type"] == "U" for r in resets),
        "middle_resets": sum(r["type"] == "M" for r in resets),
        "nonpositive_margin_resets": [
            {"row": r["row"], "type": r["type"], "dev": r["dev"]}
            for r in resets if r["margin"] <= 0
        ],
        "in_scope_resets_rows_14_up": len(in_scope),
        "in_scope_margin_min": min(in_scope),
        "in_scope_margin_max": max(in_scope),
        "in_scope_margin_mean": sum(in_scope) / len(in_scope),
        "crossing_cells": [
            {"s": r["s"], "d": r["d"], "branch": r["branch_at_s"], "in_window": r["in_window"]}
            for r in rows if r["kind"] == "crossing"
        ],
    }


def clean_env() -> dict:
    env = dict(os.environ)
    for key in ("PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP", "PYTHONINSPECT"):
        env.pop(key, None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


def run_checked(command: list[str], cwd: Path, timeout: int, name: str) -> str:
    try:
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                                env=clean_env(), timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        raise ValueError(f"{name}: timed out after {timeout} seconds; "
                         "increase --timeout for a slower machine") from None
    if result.returncode:
        raise ValueError(f"{name}: exited {result.returncode}: "
                         f"{result.stderr.strip()[-800:] or result.stdout[-800:]}")
    return result.stdout


def compute(name: str, timeout: int) -> object:
    """Run one case and return the comparable result."""
    program, args, _, kind, _ = CASES[name]
    with tempfile.TemporaryDirectory(prefix="erdos257-replay-") as tmp:
        out = Path(tmp)
        if kind == "cpp":
            compiler = shutil.which("clang++") or shutil.which("g++")
            if not compiler:
                raise ValueError(f"{name}: needs clang++ or g++ and GMP")
            binary = out / "macro_verify"
            flags = ["-O3", "-std=c++20", str(ROOT / program), "-o", str(binary), "-lgmpxx", "-lgmp"]
            if Path("/opt/homebrew/include").is_dir():
                flags[2:2] = ["-I/opt/homebrew/include", "-L/opt/homebrew/lib"]
            run_checked([compiler, *flags], ROOT, timeout, name)
            stdout = run_checked([str(binary)], out, timeout, name)
            lines = [line.split(" seconds=")[0] for line in stdout.splitlines()]
            hashes = {Path(p).name: hashlib.sha256(Path(p).read_bytes()).hexdigest()
                      for p in MACRO_OUTPUTS}
            return {"stdout_without_timings": lines, "output_sha256": hashes}
        command = [sys.executable, str(ROOT / program), *[a.replace("{out}", tmp) for a in args]]
        stdout = run_checked(command, ROOT, timeout, name)
        if kind == "json":
            return strip(json.loads(stdout))
        if kind == "jsonl":
            return [strip(json.loads(line)) for line in stdout.splitlines() if line.strip()]
        if kind == "seam":
            summary = json.loads((out / "seam_run_summary.json").read_text(encoding="utf-8"))
            return {"summary": strip(summary),
                    "ledger_statistics": seam_ledger_statistics(out / "seam_run.jsonl")}
        if kind == "margins":
            return strip(json.loads((out / "half_greedy_margins_result.json").read_text(encoding="utf-8")))
    raise ValueError(f"{name}: unknown case kind {kind}")


def recorded_case(name: str) -> dict:
    program, args, receipt, _, _ = CASES[name]
    record = json.loads((ROOT / "receipts" / receipt).read_text(encoding="utf-8"))
    if record.get("schema") != SCHEMA:
        raise ValueError(f"{name}: unknown receipt schema")
    if record.get("program") != program or record.get("arguments") != args:
        raise ValueError(f"{name}: receipt does not match the replay command")
    digest = hashlib.sha256((ROOT / program).read_bytes()).hexdigest()
    if record.get("program_sha256") != digest:
        raise ValueError(f"{name}: program changed; the saved run does not cover these bytes")
    if record.get("verification_scope") != "finite_computation_only" or "result" not in record:
        raise ValueError(f"{name}: missing finite-computation boundary or result")
    return record


def replay(name: str, timeout: int) -> dict:
    record = recorded_case(name)
    started = time.monotonic()
    actual = compute(name, timeout)
    changed = differences(record["result"], actual)
    if changed:
        raise ValueError(f"{name}: recorded result differs at {', '.join(changed[:8])}")
    return {"case": name, "matched_recorded_result": True,
            "elapsed_seconds": round(time.monotonic() - started, 2),
            "verification_scope": "finite_computation_only",
            "lean_kernel_run": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=[*CASES, "quick", "all"], default="quick",
                        help="one case, 'quick' (default: three short stdlib cases) or 'all'")
    parser.add_argument("--check", action="store_true",
                        help="check saved program identities without rerunning")
    parser.add_argument("--timeout", type=int,
                        help="seconds allowed per computation (default 300, longer for the large cases)")
    args = parser.parse_args()
    if args.timeout is not None and args.timeout < 1:
        parser.error("--timeout must be positive")
    names = {"quick": QUICK, "all": list(CASES)}.get(args.case, [args.case])
    try:
        if args.check:
            for name in CASES:
                recorded_case(name)
            print(f"{len(CASES)} finite-computation records match their programs; nothing was rerun.")
        else:
            for name in names:
                limit = args.timeout or TIMEOUTS.get(name, 300)
                print(json.dumps(replay(name, limit), indent=2), flush=True)
            print("These finite calculations do not decide Erdős #257. No Lean kernel ran.")
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
