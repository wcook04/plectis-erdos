#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run scratch Lean probes against the built corpus and record the verdicts.

Each `research/probes/*.lean` file is checked with `lake env lean` in the
repository root, so it may import any module of the two corpus libraries. For
each probe the runner writes `<out>/<stem>.json` with the exit status, the
elapsed time, the error and warning messages (file, line, text), and whether
any declaration uses `sorry`; `<out>/summary.json` lists them all.

A probe is accepted when Lean exits 0, reports no error, and no declaration
uses `sorry`. That verdict covers the probe file at the checked commit; a
result that matters is moved into `lean/` through the ordinary landing path,
where the release checks apply.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROBES = ROOT / "research" / "probes"
MESSAGE = re.compile(r"^(?P<file>[^:\n]+\.lean):(?P<line>\d+):(?P<col>\d+): (?P<kind>error|warning)(?:\([^)]*\))?: (?P<text>.*)$")


def parse_messages(output: str) -> list[dict]:
    messages: list[dict] = []
    current: dict | None = None
    for line in output.splitlines():
        match = MESSAGE.match(line)
        if match:
            current = {"line": int(match["line"]), "column": int(match["col"]),
                       "kind": match["kind"], "text": match["text"]}
            messages.append(current)
        elif current is not None and line.strip():
            current["text"] += "\n" + line
    return messages


def run_probe(path: Path, timeout: int) -> dict:
    started = time.monotonic()
    try:
        completed = subprocess.run(["lake", "env", "lean", str(path.relative_to(ROOT))], cwd=ROOT,
                                   text=True, capture_output=True, timeout=timeout)
        exit_code, output = completed.returncode, completed.stdout + completed.stderr
    except subprocess.TimeoutExpired as expired:
        exit_code = None
        output = (expired.stdout or "") + (expired.stderr or "") if isinstance(expired.stdout, str) else ""
    messages = parse_messages(output)
    errors = [m for m in messages if m["kind"] == "error"]
    uses_sorry = any("declaration uses 'sorry'" in m["text"] for m in messages)
    return {
        "probe": str(path.relative_to(ROOT)),
        "exit_code": exit_code,
        "timed_out": exit_code is None,
        "elapsed_seconds": round(time.monotonic() - started, 1),
        "errors": errors,
        "warnings": [m for m in messages if m["kind"] == "warning"][:50],
        "uses_sorry": uses_sorry,
        "accepted": exit_code == 0 and not errors and not uses_sorry,
        "output_tail": output[-4000:],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=1800, help="seconds per probe")
    args = parser.parse_args(argv)
    args.out.mkdir(parents=True, exist_ok=True)
    probes = sorted(PROBES.glob("*.lean")) if PROBES.is_dir() else []
    results = []
    for path in probes:
        result = run_probe(path, args.timeout)
        (args.out / f"{path.stem}.json").write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
        results.append({k: result[k] for k in ("probe", "accepted", "exit_code", "timed_out",
                                                "elapsed_seconds", "uses_sorry")}
                       | {"error_count": len(result["errors"])})
        print(f"{'ACCEPTED' if result['accepted'] else 'REJECTED'} {result['probe']} "
              f"({len(result['errors'])} errors, {result['elapsed_seconds']} s)")
    (args.out / "summary.json").write_text(json.dumps({"probes": results}, indent=1) + "\n", encoding="utf-8")
    if not probes:
        print("no probes under research/probes/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
