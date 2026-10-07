#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay the larger Erdős #269 scan and the two large denominator exclusions."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]
DATA = ROOT / "regenerated"
SCHEMA = "erdos269-public-computation/1"
SCAN = "scripts/check_erdos269_dyadic_windows.py"

# name: (program, base directory, arguments, receipt, kind)
CASES = {
    "scan-small": (SCAN, REPO, ["--max-denominator", "1000", "--start-min", "100",
                                "--start-max", "500", "--max-length", "24", "--assert-packet"],
                   "scan-1000-100-500.json", "json"),
    "scan-large": (SCAN, REPO, ["--max-denominator", "5000", "--start-min", "100",
                                "--start-max", "3000", "--max-length", "24", "--assert-packet"],
                   "scan-5000-100-3000.json", "json"),
    "verify-certificates": ("verify_recovered.py", ROOT, ["--data", "{data}"],
                            "verify-certificates.json", "json"),
    "regenerate-tail": ("regenerate_269.py", ROOT, ["--max-a", "15500", "--out", "{out}"],
                        "regenerate-tail.json", "regenerate"),
    "cf-statistics": ("erdos269_continued_fraction.py", ROOT, ["--start", "1", "--depth", "15000"],
                      "cf-statistics.json", "json"),
    "lattice-search": ("regenerate_block_certificate.py", ROOT,
                       ["--data", "{data}/dyadic_blocks.json", "--out", "{out}/block_certificate.json"],
                       "lattice-search.json", "lattice"),
}
QUICK = ["scan-small", "verify-certificates", "regenerate-tail"]
# Default time limits in seconds; --timeout overrides them for every case.
TIMEOUTS = {"scan-large": 900, "lattice-search": 1800}
# Fields of the published block certificate that the lattice search itself reproduces.
LATTICE_FIELDS = ["starts", "P", "m0", "forcing", "g", "index", "determinant", "weights",
                  "basis", "budgets", "max_budget", "Bmax", "published_Bmax",
                  "covers_published_Bmax", "checks", "lll_steps"]
IGNORED = {"seconds", "generator_seconds", "total_seconds", "inverse_seconds", "elapsed"}


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


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compute(name: str, timeout: int) -> object:
    program, base, args, _, kind = CASES[name]
    env = dict(os.environ)
    for key in ("PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP", "PYTHONINSPECT"):
        env.pop(key, None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    with tempfile.TemporaryDirectory(prefix="erdos269-replay-") as tmp:
        command = [sys.executable, str(base / program),
                   *[a.replace("{out}", tmp).replace("{data}", str(DATA)) for a in args]]
        try:
            result = subprocess.run(command, cwd=tmp, capture_output=True, text=True,
                                    env=env, timeout=timeout, check=False)
        except subprocess.TimeoutExpired:
            raise ValueError(f"{name}: timed out after {timeout} seconds; "
                             "increase --timeout for a slower machine") from None
        if result.returncode:
            raise ValueError(f"{name}: exited {result.returncode}: "
                             f"{result.stderr.strip()[-800:] or result.stdout[-800:]}")
        out = Path(tmp)
        if kind == "lattice":
            new = json.loads((out / "block_certificate.json").read_text(encoding="utf-8"))
            published = json.loads((DATA / "block_certificate.json").read_text(encoding="utf-8"))
            return {"Bmax": new["Bmax"], "max_budget": new["max_budget"],
                    "lll_steps": new["lll_steps"],
                    "fields_equal_to_published": {k: new[k] == published[k] for k in LATTICE_FIELDS}}
        printed = strip(json.loads(result.stdout))
        if kind == "json":
            return printed
        tail = strip(json.loads((out / "tail_certificate.json").read_text(encoding="utf-8")))
        stored_tail = strip(json.loads((DATA / "tail_certificate.json").read_text(encoding="utf-8")))
        return {
            "printed_summary": printed,
            "regenerated_equals_published": {
                "dyadic_blocks.json": sha256(out / "dyadic_blocks.json") == sha256(DATA / "dyadic_blocks.json"),
                "cf_common_prefix.json": sha256(out / "cf_common_prefix.json") == sha256(DATA / "cf_common_prefix.json"),
                "tail_certificate.json_without_timings": tail == stored_tail,
            },
        }


def recorded_case(name: str) -> dict:
    program, base, args, receipt, _ = CASES[name]
    record = json.loads((ROOT / "receipts" / receipt).read_text(encoding="utf-8"))
    if record.get("schema") != SCHEMA:
        raise ValueError(f"{name}: unknown receipt schema")
    if record.get("program") != program or record.get("arguments") != args:
        raise ValueError(f"{name}: receipt does not match the replay command")
    if record.get("program_sha256") != sha256(base / program):
        raise ValueError(f"{name}: program changed; the saved run does not cover these bytes")
    for data_name, digest in record.get("data_sha256", {}).items():
        if sha256(DATA / data_name) != digest:
            raise ValueError(f"{name}: {data_name} changed since the saved run")
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
                        help="one case, 'quick' (default: three short cases) or 'all'")
    parser.add_argument("--check", action="store_true",
                        help="check saved program and data identities without rerunning")
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
            print(f"{len(CASES)} finite-computation records match their programs and data; nothing was rerun.")
        else:
            for name in names:
                limit = args.timeout or TIMEOUTS.get(name, 300)
                print(json.dumps(replay(name, limit), indent=2), flush=True)
            print("These finite calculations do not prove irrationality or cofinal escape. No Lean kernel ran.")
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
