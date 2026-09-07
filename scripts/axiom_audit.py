#!/usr/bin/env python3
"""Audit which axioms a set of Lean declarations actually depends on.

Why this exists.  ``grep -c sorry`` over a source file is not an axiom audit: it
false-positives on the word "admit**s**" in a docstring and it says nothing about
a `sorry` reached through an imported module.  ``grep -ac sorryAx`` over a single
``.olean`` is better but still local to that module.  The real check is
``#print axioms``, which follows the whole dependency closure — and writing that
by hand means composing a throwaway Lean file, remembering the namespace, and
parsing the output, every time.

What it does.  Composes the ``#print axioms`` file, runs it through the project's
own Lean, and reports one OK/BAD line per declaration against the permitted set
``{propext, Classical.choice, Quot.sound}``.  Exit 0 only when every requested
declaration is clean.

Launch-context contract.  This project's ``lean``/``lake`` are shimmed through
``tools/meta/control/lake_command_guard.py``, and a host firewall enforces one
concurrent Lean process. Under contention the guard returns a deferral (exit 75,
or 241, or a JSON command-future payload) with **empty diagnostics**, which reads
like a broken tool rather than a queue.  This module therefore always reports the
launch context it used — project root, command, toolchain and manifest basis —
and distinguishes ``deferred`` from ``clean`` from ``violation``.  A deferral is
never reported as a pass.

Do not wrap this in a retry loop.  Each deferred attempt itself spawns a
command future that consumes the very host capacity the next attempt needs, so a
tight retry loop makes the queue longer rather than shorter.  Four consecutive
retries were observed to defer for that reason while the same command succeeded
minutes earlier and minutes later.  Wait for the concurrent Lean work to finish,
then run this once.

Boundary.  An axiom audit is not a build.  It reports what a declaration rests
on, not that the module is the right statement of anything.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


PERMITTED = frozenset({"propext", "Classical.choice", "Quot.sound"})
AXIOM_LINE = re.compile(r"'([\w.']+)' depends on axioms: \[([^\]]*)\]", re.S)
DEFERRAL_MARKERS = ("automatic_future", "command_future", "blocked_on", "capacity")


def launch_context(project_root: Path) -> dict[str, object]:
    """Everything needed to re-run this audit, or to explain why it did not run."""

    toolchain = project_root / "lean-toolchain"
    lakefile = project_root / "lakefile.toml"
    manifest = project_root / "lake-manifest.json"
    build_lib = project_root / ".lake" / "build" / "lib" / "lean"
    return {
        "cwd": str(project_root),
        "project_root": str(project_root),
        "toolchain": toolchain.read_text(encoding="utf-8").strip()
        if toolchain.is_file()
        else None,
        "lakefile_present": lakefile.is_file(),
        "lake_manifest_present": manifest.is_file(),
        "build_lib_present": build_lib.is_dir(),
        "lean_launcher": "lake env lean <generated file>",
        "guard": (
            "tools/meta/control/lake_command_guard.py intercepts lean/lake; the host "
            "firewall allows one concurrent Lean process, so a busy slot yields a "
            "deferral with empty diagnostics rather than an error"
        ),
        "readiness_command": (
            "../../repo-python scripts/axiom_audit.py --module <Lean.Module> "
            "--namespace <Namespace> --declaration <name> [--declaration <name> ...]"
        ),
        "re_entry_condition": (
            "status 'deferred' means the host build slot was busy; nothing was "
            "audited and nothing may be recorded as audited. Re-run ONCE when the "
            "slot clears -- do not retry in a loop, since each deferred attempt "
            "spawns a future that consumes the capacity the next attempt needs. "
            "Only status 'clean' licenses writing an axiom claim into a packet, a "
            "claim-frontier row, or a comparator entry."
        ),
    }


def classify_output(
    output: str, exit_code: int, declarations: list[str]
) -> dict[str, object]:
    """Turn raw kernel output into a verdict. Pure, so it is testable without Lean.

    A deferral is never a pass: when the guard returns no axiom lines, the result
    is ``deferred`` (or ``no_output``) and ``audited`` is empty.
    """

    rows = AXIOM_LINE.findall(output)
    if not rows:
        deferred = exit_code in (75, 241) or any(
            marker in output for marker in DEFERRAL_MARKERS
        )
        return {
            "status": "deferred" if deferred else "no_output",
            "requested": declarations,
            "exit_code": exit_code,
            "diagnostic_excerpt": " ".join(output.split())[:600],
            "audited": [],
            "violations": [],
            "not_reported": list(declarations),
        }

    audited, violations = [], []
    for name, raw in rows:
        axioms = sorted(
            {a.strip() for a in raw.replace("\n", " ").split(",") if a.strip()}
        )
        clean = set(axioms) <= PERMITTED
        audited.append({"declaration": name, "axioms": axioms, "permitted_only": clean})
        if not clean:
            violations.append({"declaration": name, "axioms": axioms})

    missing = [
        d for d in declarations
        if not any(r["declaration"].endswith(d) for r in audited)
    ]
    status = (
        "violation" if violations else ("incomplete" if missing else "clean")
    )
    return {
        "status": status,
        "requested": declarations,
        "exit_code": exit_code,
        "audited": audited,
        "violations": violations,
        "not_reported": missing,
    }


def run_audit(
    project_root: Path, module: str, namespace: str | None, declarations: list[str]
) -> dict[str, object]:
    lines = [f"import {module}"]
    if namespace:
        lines.append(f"open {namespace}")
    lines.extend(f"#print axioms {d}" for d in declarations)
    source = "\n".join(lines) + "\n"

    handle, path = tempfile.mkstemp(suffix=".lean", prefix="axiom_audit_")
    try:
        with os.fdopen(handle, "w", encoding="utf-8") as stream:
            stream.write(source)
        completed = subprocess.run(
            ["lake", "env", "lean", path],
            cwd=project_root,
            capture_output=True,
            text=True,
        )
    finally:
        Path(path).unlink(missing_ok=True)

    return classify_output(
        completed.stdout + completed.stderr, completed.returncode, declarations
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Lean project root (defaults to this script's parent)",
    )
    parser.add_argument("--module", required=True, help="Lean module to import")
    parser.add_argument("--namespace", help="namespace to open before printing")
    parser.add_argument(
        "--declaration",
        action="append",
        required=True,
        dest="declarations",
        help="declaration to audit; repeatable",
    )
    parser.add_argument("--json", action="store_true", help="emit the full record")
    args = parser.parse_args()

    project_root = args.project_root.resolve()
    context = launch_context(project_root)
    result = run_audit(project_root, args.module, args.namespace, args.declarations)
    record = {
        "schema": "lean_axiom_audit_v0",
        "permitted_axioms": sorted(PERMITTED),
        "module": args.module,
        "namespace": args.namespace,
        "launch_context": context,
        "result": result,
        "boundary": (
            "An axiom audit reports what a declaration rests on. It is not a build "
            "and it does not judge whether the statement is the intended one."
        ),
    }

    if args.json:
        print(json.dumps(record, indent=2, sort_keys=True))
    else:
        print(f"module    {args.module}")
        print(f"project   {context['project_root']}  (toolchain {context['toolchain']})")
        print(f"status    {result['status']}  (exit {result['exit_code']})")
        for row in result["audited"]:
            mark = "OK " if row["permitted_only"] else "BAD"
            tail = "" if row["permitted_only"] else f"  {row['axioms']}"
            print(f"  {mark} {row['declaration']}{tail}")
        if result["status"] == "deferred":
            print("  the host build slot was busy; NOTHING was audited")
            print("  do NOT retry in a loop: each deferred attempt spawns a future")
            print("  that consumes the capacity the next attempt needs")
            print(f"  re-run once when the slot clears: {context['readiness_command']}")
        for name in result.get("not_reported", []):
            print(f"  MISSING {name} — not reported by the kernel")

    return 0 if result["status"] == "clean" else 1


if __name__ == "__main__":
    raise SystemExit(main())
