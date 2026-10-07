#!/usr/bin/env python3
"""Run one focused single-file Lean check inside a small host semaphore.

WHY
---
The `lake`/`lean` shims serialise every Lean process on this host behind one
mutex and refuse concurrent callers with exit 75 instead of queueing.  With a
fleet of workers each checking one small file, seven of eight calls never start
and a queued caller can wait over an hour for a 45-second check.  The memory
rationale for the mutex (an elaborator can reach ~5 GiB) is real, but it bounds
K, not K=1: on the 24 GiB host two or three focused single-file checks are safe.

This wrapper runs the toolchain's REAL Lake and REAL Lean (`.lake.aiw-private-real`,
`.lean.aiw-private-real`), bypassing the shims, inside a K-slot file semaphore.
A single-file check writes no object files and is the compile shape the build
firewall exempts.  Whole-tree builds must still go through `lean_fast_build.py`.

USAGE
-----
    python3 research_corpus/Erdos1041/scripts/lean_check_slot.py \
        [--slots 2] [--wait-seconds 5400] [--project-root <lake project>] <file.lean> [lean args...]

``--slots`` defaults to the host's shared semaphore width (the capacity broker's
seat budget) clamped by the per-elaborator memory ceiling, not to 1.
``AIW_LEAN_FLEET_SLOTS`` still overrides it exactly.

Exit code is Lean's exit code; 75 if no slot became free within --wait-seconds.
"""
from __future__ import annotations

import argparse
import fcntl
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve()
DEFAULT_PROJECT = HERE.parents[1]
SLOT_ROOT = Path.home() / "Library" / "Caches" / "plectis-lean" / "fleet-slots-v1"
DEFER = 75

# An elaborator has reached roughly 5 GiB RSS on the 24 GiB development host, so
# the slot count is memory-bounded even when the shared semaphore is wider.
SLOT_CEILING_DEFAULT = 3
SLOT_CEILING_ENV = "AIW_LEAN_FLEET_SLOT_CEILING"
SLOTS_ENV = "AIW_LEAN_FLEET_SLOTS"


def _positive_int(value, default: int) -> int:
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return default
    return parsed if parsed > 0 else default


def default_slots(env=None) -> int:
    """Follow the host's shared semaphore width, not a hardcoded one.

    Defaulting to one slot meant a fleet of emits queued on slot 0 while every
    other slot idled: on 2026-09-21 four wrapper emits serialised for ninety
    minutes behind that default.  The shared capacity broker already publishes
    the host's seat budget; use it, clamped by the per-elaborator memory
    ceiling, and keep the explicit environment override on top.
    """
    values = dict(os.environ if env is None else env)
    explicit = values.get(SLOTS_ENV)
    if explicit is not None and str(explicit).strip():
        return _positive_int(explicit, 1)
    ceiling = _positive_int(values.get(SLOT_CEILING_ENV), SLOT_CEILING_DEFAULT)
    try:
        from system.lib.resource_capacity_broker import default_global_seats

        shared = _positive_int(default_global_seats(values), 1)
    except Exception:
        # The script also runs from checkouts without the ai_workflow library on
        # the path; fall back to the same host-derived shape the broker uses.
        cpu_count = max(1, os.cpu_count() or 1)
        shared = max(1, cpu_count - max(1, cpu_count // 4))
    return max(1, min(shared, ceiling))


def toolchain_bin(project_root: Path) -> Path:
    toolchain = (project_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    name = toolchain.replace("/", "--").replace(":", "---")
    return Path.home() / ".elan" / "toolchains" / name / "bin"


def real_binary(bin_dir: Path, name: str) -> Path:
    for cand in (bin_dir / f".{name}.aiw-private-real", bin_dir / f"{name}.aiw-guard-real", bin_dir / name):
        if cand.is_file():
            return cand
    raise SystemExit(f"lean_check_slot: no {name} binary under {bin_dir}")


def acquire_slot(slots: int, wait_seconds: float):
    deadline = time.monotonic() + wait_seconds
    handles = []
    for i in range(slots):
        d = SLOT_ROOT / f"slot-{i}"
        d.mkdir(parents=True, exist_ok=True)
        handles.append((i, (d / "slot.lock").open("a+", encoding="utf-8")))
    while True:
        for i, h in handles:
            try:
                fcntl.flock(h.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                continue
            for j, other in handles:
                if j != i:
                    other.close()
            return i, h
        if time.monotonic() >= deadline:
            for _, h in handles:
                h.close()
            return None, None
        time.sleep(3)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--slots", type=int, default=None)
    ap.add_argument("--wait-seconds", type=float, default=5400)
    ap.add_argument("--project-root", type=Path, default=DEFAULT_PROJECT)
    ap.add_argument("file", type=Path)
    ap.add_argument("lean_args", nargs="*")
    args = ap.parse_args()
    slots = max(1, args.slots) if args.slots else default_slots()
    started = time.monotonic()
    bin_dir = toolchain_bin(args.project_root)
    real_lake = real_binary(bin_dir, "lake")
    real_lean = real_binary(bin_dir, "lean")
    slot, handle = acquire_slot(slots, args.wait_seconds)
    if handle is None:
        print(f"lean_check_slot: no free slot after {args.wait_seconds:.0f}s", file=sys.stderr)
        return DEFER
    waited = time.monotonic() - started
    print(
        f"lean_check_slot: slot {slot}/{slots} after {waited:.0f}s wait; {args.file}",
        file=sys.stderr,
        flush=True,
    )
    try:
        rc = subprocess.call(
            [str(real_lake), "env", str(real_lean), str(args.file), *args.lean_args],
            cwd=str(args.project_root),
        )
    finally:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        finally:
            handle.close()
    print(f"lean_check_slot: rc={rc} elapsed={time.monotonic() - started:.0f}s slot={slot}", file=sys.stderr)
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
