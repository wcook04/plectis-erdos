#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the replay record in routes.json against the records it was read from.

The replay read the long records and short papers at one pinned commit
(``source_commit``). This script reads the same files at that commit through
``git show`` and checks, for every route: a known closure class; for every
route with a ``needle``, that the needle occurs verbatim in the named record;
and for every route recorded as never tried with ``absent_terms``, that none
of those terms occurs in the named records. It also checks that every
reopened route names a result. It proves nothing about the mathematics: it
keeps the recorded reading honest about what the records said at the time.
Run with --output PATH to retain the JSON receipt; otherwise print it.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CLASSES = {
    "proved", "obstruction_proved", "counterexample", "finite_outcome",
    "attempt_closed", "superseded", "out_of_support",
}


def read_at_commit(commit, relpath, root=ROOT):
    """Return the text of relpath at commit, or raise with a clear message."""
    proc = subprocess.run(
        ["git", "-C", str(root), "show", f"{commit}:{relpath}"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"cannot read {relpath} at {commit}: {proc.stderr.strip()} "
            "(a full-history clone is required)"
        )
    return proc.stdout


def check(record, reader=read_at_commit):
    commit = record["source_commit"]
    base = record["records"]
    cache = {}

    def text(name):
        if name not in cache:
            cache[name] = reader(commit, f"{base}/{name}")
        return cache[name]

    problems, counts, needles, absences = [], {}, 0, 0
    for block in record["readers"]:
        for route in block["routes"]:
            rid = route["id"]
            cls = route.get("closure")
            if cls not in CLASSES:
                problems.append(f"{rid}: unknown closure class {cls!r}")
                continue
            counts[cls] = counts.get(cls, 0) + 1
            if "needle" in route:
                needles += 1
                if route["needle"] not in text(route["file"]):
                    problems.append(f"{rid}: needle not found in {route['file']}")
            for term in route.get("absent_terms", []):
                for name in route.get("absent_files", []):
                    absences += 1
                    if term in text(name):
                        problems.append(f"{rid}: {term!r} occurs in {name}")
            tag = route.get("reopened")
            if tag and tag not in record.get("reopened", {}):
                problems.append(f"{rid}: reopened tag {tag} has no result")
    for tag, row in record.get("reopened", {}).items():
        for key in ("transport", "result", "evidence"):
            if not row.get(key):
                problems.append(f"{tag}: missing {key}")
    return {
        "schema": "plectis-replay-routes-check/1",
        "source_commit": commit,
        "routes": sum(counts.values()),
        "closure_counts": dict(sorted(counts.items())),
        "needles_checked": needles,
        "absence_checks": absences,
        "reopened": sorted(record.get("reopened", {})),
        "problems": problems,
        "ok": not problems,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--routes", default=str(HERE / "routes.json"))
    parser.add_argument("--output")
    args = parser.parse_args(argv)
    receipt = check(json.loads(Path(args.routes).read_text()))
    payload = json.dumps(receipt, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        Path(args.output).write_text(payload)
    else:
        sys.stdout.write(payload)
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
