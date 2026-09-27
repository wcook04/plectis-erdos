#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Per-command verdicts of a kernel probe of the argument frontier.

A frontier probe (``research/probes/*.lean`` on a ``claude/kernel-probe-*``
branch, written by ``build_argument_frontier.py --probes``) carries ``derive_*``
commands, one per line, each preceded by a marker message ``@@COMMAND <line>``
naming the line of the command after it. For every theorem a command adds, after
the kernel accepted it, Lean logs ``added <name> : <statement>`` as an
information message; Lean prints information messages without their position,
and in the order of the commands, so an ``added`` line belongs to the command the
last marker named. Warnings and errors carry their line. The verdict of a command rests on
that evidence and nothing else: ``added`` is true when at least one such message
is at its line and no error is. A failure is a warning (outside
``argumentGraph.strict``) or an error at the line; a command with neither an
``added`` message nor a failure has no verdict (the probe stopped before it, or
the log was lost), so it stays unverified rather than passing or failing.

The probe's closing ``DERIVED <name> <hash>`` lines, when present, give the
statement hash of every theorem the file added; the frontier records them so a
later regeneration can check that a name still states what it stated.

Usage:
    python3 scripts/frontier_verdicts.py --run RUN_ID --artifact DIR --probes DIR --out OUT.json

``--artifact`` is the downloaded ``kernel-probe-<sha>`` directory (``<stem>.log``
holds a probe's full output); ``--probes`` holds the probe sources that ran.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

MESSAGE = re.compile(r"^(?P<file>[^:\n]+\.lean):(?P<line>\d+):(?P<col>\d+): "
                     r"(?P<kind>error|warning|info)(?:\([^)]*\))?: (?P<text>.*)$")
ADDED = re.compile(r"^added (?P<name>\S+) : (?P<statement>.*)$", re.S)
PLACED = re.compile(r"^placed (?P<name>\S+) :: (?P<hypothesis>.*?) :: (?P<claims>.*)$", re.S)
DERIVED = re.compile(r"^DERIVED\t(?P<name>\S+)\t(?P<hash>[0-9a-f]+)$", re.M)


MARKER = re.compile(r"^@@COMMAND (?P<line>\d+)$")


def marker_lines(source: str) -> dict[int, int]:
    """Marker value -> the line of the command after it. The value only identifies the
    marker; the command's line is read from the source."""
    lines = source.splitlines()
    out: dict[int, int] = {}
    for i, line in enumerate(lines):
        match = re.search(r'"@@COMMAND (\d+)"', line)
        if match and line.lstrip().startswith("run_cmd"):
            out[int(match.group(1))] = i + 2
    return out


def messages(log: str, markers: dict[int, int] | None = None) -> list[dict]:
    """The log's messages, each with its continuation lines. A positionless line after
    a marker is an information message of the command the marker names."""
    out: list[dict] = []
    current: dict | None = None
    command_line = 0
    for line in log.splitlines():
        match = MESSAGE.match(line)
        marker = MARKER.match(line)
        if match:
            current = {"line": int(match["line"]), "kind": match["kind"], "text": match["text"]}
            out.append(current)
        elif marker:
            value = int(marker["line"])
            command_line = (markers or {}).get(value, value)
            current = None
        elif (line.startswith("added ") or line.startswith("placed ")) and command_line:
            current = {"line": command_line, "kind": "info", "text": line}
            out.append(current)
        elif current is not None:
            current["text"] += "\n" + line
    return out


def probe_verdicts(source: str, log: str, stem: str) -> dict[str, dict]:
    commands = {i + 1: line.strip() for i, line in enumerate(source.splitlines())
                if line.startswith("derive_") or line.startswith("set_option argumentGraph.strict false in derive_")}
    by_line: dict[int, list[dict]] = {}
    for m in messages(log, marker_lines(source)):
        by_line.setdefault(m["line"], []).append(m)
    out: dict[str, dict] = {}
    for line, raw in commands.items():
        command = raw.removeprefix("set_option argumentGraph.strict false in ").strip()
        here = by_line.get(line, [])
        added = {}
        placements = []
        for m in here:
            match = ADDED.match(m["text"]) if m["kind"] == "info" else None
            if match:
                added[match["name"]] = " ".join(match["statement"].split())
            placed = PLACED.match(m["text"]) if m["kind"] == "info" else None
            if placed:
                placements.append({"derived": placed["name"],
                                   "hypothesis": " ".join(placed["hypothesis"].split()),
                                   "claims": " ".join(placed["claims"].split())})
        failures = [m["text"] for m in here if m["kind"] in ("error", "warning")
                    and not m["text"].startswith("unused variable") and not m["text"].startswith("linter")]
        errors = [m for m in here if m["kind"] == "error"]
        if not added and not failures:
            continue
        out[command] = {"added": bool(added) and not errors, "names": sorted(added),
                        "statements": added, "placements": placements,
                        "message": " | ".join(failures)[:800], "probe": stem}
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--run", required=True)
    parser.add_argument("--artifact", type=Path, required=True)
    parser.add_argument("--probes", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    verdicts: dict[str, dict] = {}
    hashes: dict[str, str] = {}
    missing: list[str] = []
    for source_path in sorted(args.probes.glob("*.lean")):
        log_path = args.artifact / f"{source_path.stem}.log"
        if not log_path.exists():
            missing.append(source_path.stem)
            continue
        log = log_path.read_text(encoding="utf-8", errors="replace")
        for command, verdict in probe_verdicts(source_path.read_text(encoding="utf-8"), log,
                                               source_path.stem).items():
            # the same command in two probes: a success anywhere is the evidence
            if command not in verdicts or (verdict["added"] and not verdicts[command]["added"]):
                verdicts[command] = verdict
        hashes.update({m["name"]: m["hash"] for m in DERIVED.finditer(log)})
    args.out.write_text(json.dumps({"probe_run": args.run, "commands": verdicts, "statement_hashes": hashes,
                                    "probes_without_log": missing}, indent=1, ensure_ascii=False) + "\n",
                        encoding="utf-8")
    added = sum(1 for v in verdicts.values() if v["added"])
    print(f"{len(verdicts)} commands with a verdict: {added} added theorems, {len(verdicts) - added} did not; "
          f"{len(hashes)} statement hashes; {len(missing)} probes without a log -> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
