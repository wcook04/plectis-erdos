#!/usr/bin/env python3
"""Serialized compile pass over the round-7 Type B modules, one problem at a time.

WHY
---
The host allows one Lean build at a time and `lake env lean` emits no object
files, so a fleet cannot compile the r7 returns in parallel and dependents of a
new module cannot be checked at all until something produces its `.olean`.  The
governed engine that does both is `lean_fast_build.py`.  This driver runs it per
problem (so one problem's failing leaf does not block another problem's waves),
captures the full Lake/Lean diagnostics, and writes a per-module receipt the
repair lane can act on without re-running anything.

`lean_fast_build.py` builds stale modules in topological waves and stops after
the first wave that contains a failure, so modules downstream of a failing
module are reported as `not_reached`; rerun the pass after repairs.

USAGE
-----
    ./repo-python formal_math/erdos257_period_noncollapse/scripts/r7_compile_pass.py \
        --modules <file with one module per line> --out-dir <dir> [--problems 68,243,...] [--pass-id p1]

Writes <out-dir>/compile_<pass-id>_<problem>.json and .log per problem, plus a
summary <out-dir>/compile_<pass-id>_summary.json.  Exit 0 when every requested
module compiled, 1 otherwise (75 if the host build slot was held by another job).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve()
PROJECT = HERE.parents[1]
REPO = PROJECT.parents[1]
FAST_BUILD = HERE.with_name("lean_fast_build.py")
RESULT_RE = re.compile(r"^lean-fast-build: (\S+) -> (\d+) \(([\d.]+)s\)$", re.M)
ERROR_RE = re.compile(r"^(\S+\.lean):(\d+):(\d+): error: (.*)$", re.M)
# Lake-level failures (bad import, missing file) carry no line/col.
FILE_ERROR_RE = re.compile(r"^error: (\S+\.lean): (.*)$", re.M)
PROBLEM_RE = re.compile(r"^ErdosProblems\.Erdos(\d+)\.")


def problem_of(module: str) -> str:
    m = PROBLEM_RE.match(module)
    return m.group(1) if m else "shared"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--modules", type=Path, required=True)
    ap.add_argument("--out-dir", type=Path, required=True)
    ap.add_argument("--problems", default="")
    ap.add_argument("--pass-id", default=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()))
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--wait-seconds", type=float, default=7200, help="how long to wait for the host build slot per problem")
    ap.add_argument("--retry-seconds", type=float, default=20)
    ap.add_argument("--whole-problem", action="store_true", help="one lean_fast_build per problem (stops at first failing wave)")
    args = ap.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    modules = [m.strip() for m in args.modules.read_text().splitlines() if m.strip() and not m.startswith("#")]
    by_problem: dict[str, list[str]] = {}
    for m in modules:
        by_problem.setdefault(problem_of(m), []).append(m)
    wanted = {p.strip() for p in args.problems.split(",") if p.strip()}
    summary: dict[str, dict] = {}
    overall_rc = 0
    for problem in sorted(by_problem, key=lambda p: (p == "shared", int(p) if p.isdigit() else 0)):
        if wanted and problem not in wanted:
            continue
        targets = by_problem[problem]
        log_path = args.out_dir / f"compile_{args.pass_id}_{problem}.log"
        started = time.monotonic()
        # lean_fast_build stops after the first wave containing a failure, so one bad
        # leaf hides every sibling.  Build each target on its own invocation (Lake
        # still builds its dependencies) unless --whole-problem is given.
        groups = [[t] for t in targets] if not args.whole_problem else [targets]
        text_parts: list[str] = []
        rc_max = 0
        for group in groups:
            # The host build slot is a non-blocking mutex; exit 75 means "held by another
            # job", not failure.  Wait for it (this pass IS the caller's own build).
            deadline = time.monotonic() + args.wait_seconds
            while True:
                proc = subprocess.run(
                    [str(REPO / "repo-python"), str(FAST_BUILD), "--jobs", str(args.jobs), "--lake-staleness",
                     "--no-final-build", "--project-root", str(PROJECT), *group],
                    cwd=str(REPO), capture_output=True, text=True,
                )
                if proc.returncode != 75 or time.monotonic() >= deadline:
                    break
                time.sleep(args.retry_seconds)
            text_parts.append(f"\n### target group {group} rc={proc.returncode}\n" + (proc.stdout or "") + "\n" + (proc.stderr or ""))
            if proc.returncode == 75:
                rc_max = 75
                break
            rc_max = max(rc_max, proc.returncode)
            if len(group) == 1 and proc.returncode == 0 and f"lean-fast-build: {group[0]} ->" not in text_parts[-1]:
                text_parts.append(f"lean-fast-build: {group[0]} -> 0 (0.0s)\n")  # already fresh
        text = "".join(text_parts)
        log_path.write_text(text, encoding="utf-8")

        class _P:  # minimal stand-in so the receipt code below reads one rc
            returncode = rc_max
        proc = _P()
        results = {m: {"rc": int(rc), "seconds": float(s)} for m, rc, s in RESULT_RE.findall(text)}
        errors: dict[str, list[dict]] = {}
        for file, line, col, msg in ERROR_RE.findall(text):
            mod = file.replace("/", ".").removesuffix(".lean")
            errors.setdefault(mod, []).append({"line": int(line), "col": int(col), "message": msg[:400]})
        for file, msg in FILE_ERROR_RE.findall(text):
            mod = file.replace("/", ".").removesuffix(".lean")
            errors.setdefault(mod, []).append({"line": 0, "col": 0, "message": msg[:400]})
        per_module = {}
        for m in targets:
            if m in results:
                status = "compiled" if results[m]["rc"] == 0 else "failed"
            elif proc.returncode == 0:
                status = "compiled"  # already fresh, no rebuild needed
            else:
                status = "not_reached"
            per_module[m] = {"status": status, **results.get(m, {}), "errors": errors.get(m, [])}
        # modules that were prebuilt as dependencies but are not targets still carry useful errors
        extra = {m: {"status": "failed_dependency", **results[m], "errors": errors.get(m, [])}
                 for m in results if m not in targets and results[m]["rc"] != 0}
        receipt = {
            "schema": "r7_compile_pass_v1", "problem": problem, "pass_id": args.pass_id,
            "fast_build_rc": proc.returncode, "seconds": round(time.monotonic() - started, 1),
            "targets": per_module, "failed_dependencies": extra, "log": str(log_path),
        }
        (args.out_dir / f"compile_{args.pass_id}_{problem}.json").write_text(
            json.dumps(receipt, indent=1, ensure_ascii=False), encoding="utf-8")
        counts = {}
        for row in per_module.values():
            counts[row["status"]] = counts.get(row["status"], 0) + 1
        summary[problem] = {"fast_build_rc": proc.returncode, "counts": counts, "seconds": receipt["seconds"]}
        print(f"r7_compile_pass: #{problem} rc={proc.returncode} {counts} ({receipt['seconds']}s)", flush=True)
        if proc.returncode == 75:
            overall_rc = 75
            break
        if proc.returncode:
            overall_rc = overall_rc or 1
    (args.out_dir / f"compile_{args.pass_id}_summary.json").write_text(
        json.dumps(summary, indent=1), encoding="utf-8")
    return overall_rc


if __name__ == "__main__":
    raise SystemExit(main())
