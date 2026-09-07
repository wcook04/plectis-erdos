#!/usr/bin/env python3
"""Drive `lean_fast_build.py` to completion over a target list, shedding failures.

WHY
---
`lean_fast_build.py` builds stale modules in topological waves with a bounded
concurrent pool, but it stops after the first wave containing a failure, so one
broken leaf in problem A hides every later wave of problems B..H.  Rerunning by
hand after each failure wastes an operator turn per failure.  This loop reruns
automatically: after every pass it removes the failed modules and every target
that (transitively) imports one of them from the target list, records them, and
launches the next pass, until a pass succeeds or no targets remain.

Repairs still happen elsewhere; this only keeps the build engine busy on what
can compile now and produces a per-module receipt the repair lane can act on.

USAGE
-----
    ./repo-python formal_math/erdos257_period_noncollapse/scripts/r7_build_loop.py \
        --modules <file> --out-dir <dir> [--jobs 2] [--max-passes 8] [--exclude MOD ...]

Writes <out-dir>/build_loop_<stamp>.json (per-module status + first errors) and
pass logs <out-dir>/build_loop_<stamp>_pass<k>.log.  Exit 0 when every module in
the final target list built, 1 when some were shed, 75 if the host slot never freed.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve()
PROJECT = HERE.parents[1]
REPO = PROJECT.parents[1]
FAST_BUILD = HERE.with_name("lean_fast_build.py")
RESULT_RE = re.compile(r"^lean-fast-build: (\S+) -> (\d+) \(([\d.]+)s\)$", re.M)
ERROR_RE = re.compile(r"^error: (\S+\.lean):(\d+):(\d+): (.*)$", re.M)
FILE_ERROR_RE = re.compile(r"^error: (\S+\.lean): (.*)$", re.M)
IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)


def module_file(mod: str) -> Path:
    return PROJECT / (mod.replace(".", "/") + ".lean")


def local_imports(mod: str) -> set[str]:
    f = module_file(mod)
    if not f.is_file():
        return set()
    # A bare `import ErdosProblems` / `import Erdos257PeriodNoncollapse` is the library barrel file.
    return {m for m in IMPORT_RE.findall(f.read_text(encoding="utf-8"))
            if m.startswith("ErdosProblems") or m.startswith("Erdos257PeriodNoncollapse")}


def transitive_dependents(targets: list[str], bad: set[str]) -> set[str]:
    """Targets that import (transitively, through local modules) any module in `bad`."""
    memo: dict[str, bool] = {}

    def depends(mod: str, stack: set[str]) -> bool:
        if mod in memo:
            return memo[mod]
        if mod in bad:
            memo[mod] = True
            return True
        if mod in stack:
            return False
        stack.add(mod)
        result = any(depends(i, stack) for i in local_imports(mod))
        stack.discard(mod)
        memo[mod] = result
        return result

    return {t for t in targets if depends(t, set())}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--modules", type=Path, required=True)
    ap.add_argument("--out-dir", type=Path, required=True)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--max-passes", type=int, default=8)
    ap.add_argument("--exclude", action="append", default=[])
    ap.add_argument("--wait-seconds", type=float, default=7200)
    args = ap.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    all_targets = [m.strip() for m in args.modules.read_text().splitlines() if m.strip() and not m.startswith("#")]
    shed: dict[str, dict] = {}
    for ex in args.exclude:
        shed[ex] = {"status": "excluded_by_operator", "errors": []}
    targets = [m for m in all_targets if m not in shed]
    built: dict[str, dict] = {}
    env = {**os.environ, "AIW_RESOURCE_LEAN_BUILD_CHILD_BUDGET": str(args.jobs), "AIW_LAKE_GUARD_JOBS": str(args.jobs)}
    final_rc = 1
    for k in range(1, args.max_passes + 1):
        if not targets:
            break
        log_path = args.out_dir / f"build_loop_{stamp}_pass{k}.log"
        deadline = time.monotonic() + args.wait_seconds
        while True:
            proc = subprocess.run(
                [str(REPO / "repo-python"), str(FAST_BUILD), "--jobs", str(args.jobs), "--lake-staleness",
                 "--no-final-build", "--project-root", str(PROJECT), *targets],
                cwd=str(REPO), capture_output=True, text=True, env=env,
            )
            if proc.returncode != 75 or time.monotonic() >= deadline:
                break
            time.sleep(20)
        text = (proc.stdout or "") + "\n" + (proc.stderr or "")
        log_path.write_text(text, encoding="utf-8")
        results = {m: int(rc) for m, rc, _ in RESULT_RE.findall(text)}
        errors: dict[str, list] = {}
        for file, line, col, msg in ERROR_RE.findall(text):
            errors.setdefault(file.replace("/", ".").removesuffix(".lean"), []).append({"line": int(line), "col": int(col), "message": msg[:400]})
        for file, msg in FILE_ERROR_RE.findall(text):
            errors.setdefault(file.replace("/", ".").removesuffix(".lean"), []).append({"line": 0, "col": 0, "message": msg[:400]})
        for m, rc in results.items():
            if rc == 0 and m in targets:
                built[m] = {"status": "built", "pass": k}
        failed = {m for m, rc in results.items() if rc != 0}
        print(f"build_loop pass {k}: rc={proc.returncode} built_so_far={len(built)} failed={sorted(failed)}", flush=True)
        if proc.returncode == 75:
            final_rc = 75
            break
        if proc.returncode == 0:
            for m in targets:
                built.setdefault(m, {"status": "built", "pass": k})
            final_rc = 0 if not shed else 1
            break
        if not failed:
            break  # unknown failure shape; do not loop forever
        for m in failed:
            shed[m] = {"status": "failed", "pass": k, "errors": errors.get(m, [])}
        dependents = transitive_dependents(targets, failed)
        for m in dependents - failed:
            shed[m] = {"status": "blocked_by_failed_import", "pass": k, "blocked_on": sorted(failed & set(local_imports(m))) or sorted(failed)[:3], "errors": []}
        targets = [m for m in targets if m not in shed and m not in built]
    receipt = {
        "schema": "r7_build_loop_receipt_v1", "stamp": stamp, "jobs": args.jobs, "final_rc": final_rc,
        "built": built, "shed": shed, "remaining_unbuilt": [m for m in all_targets if m not in built and m not in shed],
    }
    (args.out_dir / f"build_loop_{stamp}.json").write_text(json.dumps(receipt, indent=1, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({"built": len(built), "shed": len(shed), "final_rc": final_rc, "receipt": str(args.out_dir / f'build_loop_{stamp}.json')}))
    return final_rc


if __name__ == "__main__":
    raise SystemExit(main())
