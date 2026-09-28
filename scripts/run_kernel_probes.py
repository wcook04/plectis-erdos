#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run scratch Lean probes against the built corpus and record the verdicts.

Each `research/probes/*.lean` file is checked with `lake env lean` in the
repository root, so it may import any module of the two corpus libraries. For
each probe the runner writes `<out>/<stem>.json` with the exit status, the
elapsed time, the error and warning messages (file, line, text), whether any
declaration uses `sorry`, the axioms the file declares, the axioms each
`#print axioms` line reports, and the SHA-256 of the probe source, and
`<out>/<stem>.log` with the full compiler output (the JSON keeps only its
last 4,000 characters); `<out>/summary.json` lists them all.

A probe is accepted (`accepted`) when Lean exits 0, reports no error, no
declaration uses `sorry`, the file declares no axiom, and no `#print axioms`
line names an axiom other than `propext`, `Classical.choice` and
`Quot.sound`; `compilation_accepted` is the first three alone. Print the axioms
of every declaration that matters: an axiom reached only through an imported
module shows nowhere else. Acceptance is a compilation receipt for the probe
file at the checked commit (`evidence_class: compilation_probe`): it does not
check that the probe states the intended target, and it replays nothing
(`exact_target_checked` and `environment_replayed` are false). A result that
matters moves into `lean/` through the ordinary landing path, where the exact
statement checks and the release checks apply.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROBES = ROOT / "research" / "probes"
MESSAGE = re.compile(r"^(?P<file>[^:\n]+\.lean):(?P<line>\d+):(?P<col>\d+): (?P<kind>error|warning)(?:\([^)]*\))?: (?P<text>.*)$")
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
# `#print axioms` output: `'X' depends on axioms: [a, b]` (the list may wrap
# over several lines) or `'X' does not depend on any axioms`.
PRINTED_AXIOMS = re.compile(r"'(?P<name>[^'\n]+)' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
                            r"|(?P<none>does not depend on any axioms))")
DECLARED_AXIOM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*"
                            r"axiom\s+(?P<name>[^\s:({\[]+)", re.MULTILINE)
COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.DOTALL)


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


def printed_axioms(output: str) -> dict[str, list[str]]:
    """Declaration -> the axioms its `#print axioms` line names."""
    found: dict[str, list[str]] = {}
    for match in PRINTED_AXIOMS.finditer(output):
        names = [] if match["none"] else [a.strip() for a in match["axioms"].replace("\n", " ").split(",")
                                          if a.strip()]
        found[match["name"]] = names
    return found


def declared_axioms(source: str) -> list[str]:
    """The axioms the probe file itself declares (comments ignored)."""
    return sorted({match["name"] for match in DECLARED_AXIOM.finditer(COMMENT.sub(" ", source))})


def _text(value: str | bytes | None) -> str:
    # On a timeout, subprocess hands back what the probe printed as bytes even
    # when text=True; keep it, decoded, since it says where Lean stopped.
    return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else (value or "")


def run_probe(path: Path, timeout: int) -> dict:
    if timeout <= 0:
        raise ValueError("timeout must be a positive number of seconds")
    source = path.read_bytes()
    started = time.monotonic()
    try:
        completed = subprocess.run(["lake", "env", "lean", str(path.relative_to(ROOT))], cwd=ROOT,
                                   text=True, capture_output=True, timeout=timeout)
        exit_code, output = completed.returncode, _text(completed.stdout) + _text(completed.stderr)
    except subprocess.TimeoutExpired as expired:
        exit_code = None
        output = _text(expired.stdout) + _text(expired.stderr)
    messages = parse_messages(output)
    errors = [m for m in messages if m["kind"] == "error"]
    uses_sorry = any("declaration uses 'sorry'" in m["text"] for m in messages)
    declared = declared_axioms(source.decode("utf-8", errors="replace"))
    printed = printed_axioms(output)
    nonstandard = sorted({a for axioms in printed.values() for a in axioms} - STANDARD_AXIOMS)
    compiled = exit_code == 0 and not errors and not uses_sorry
    return {
        "probe": str(path.relative_to(ROOT)),
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "evidence_class": "compilation_probe",
        "exact_target_checked": False,
        "environment_replayed": False,
        "exit_code": exit_code,
        "timed_out": exit_code is None,
        "elapsed_seconds": round(time.monotonic() - started, 1),
        "errors": errors,
        "warnings": [m for m in messages if m["kind"] == "warning"][:50],
        "uses_sorry": uses_sorry,
        "axioms_declared": declared,
        "axioms_printed": printed,
        "nonstandard_axioms": nonstandard,
        "compilation_accepted": compiled,
        "accepted": compiled and not declared and not nonstandard,
        "output_tail": output[-4000:],
        "_output": output,
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
        # The verdict keeps a 4,000-character tail; the full compiler output
        # goes beside it so a long error or axiom listing is never cut off.
        (args.out / f"{path.stem}.log").write_text(result.pop("_output", ""), encoding="utf-8")
        (args.out / f"{path.stem}.json").write_text(json.dumps(result, indent=1) + "\n", encoding="utf-8")
        results.append({k: result[k] for k in ("probe", "accepted", "compilation_accepted", "exit_code",
                                                "timed_out", "elapsed_seconds", "uses_sorry", "axioms_declared",
                                                "nonstandard_axioms", "source_sha256", "evidence_class")}
                       | {"error_count": len(result["errors"])})
        reasons = ([f"{len(result['errors'])} errors"] + (["sorry"] if result["uses_sorry"] else [])
                   + [f"axiom {a}" for a in result["axioms_declared"] + result["nonstandard_axioms"]])
        print(f"{'ACCEPTED' if result['accepted'] else 'REJECTED'} {result['probe']} "
              f"({', '.join(reasons)}, {result['elapsed_seconds']} s)")
    (args.out / "summary.json").write_text(json.dumps({"probes": results}, indent=1) + "\n", encoding="utf-8")
    if not probes:
        print("no probes under research/probes/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
