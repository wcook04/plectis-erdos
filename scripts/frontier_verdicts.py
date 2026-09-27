#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Per-command verdicts of a kernel probe of the argument frontier.

A frontier probe (``research/probes/*.lean`` on a ``claude/kernel-probe-*``
branch, written by ``build_argument_frontier.py --probes``) carries ``derive_*``
commands, one per line, each preceded by a marker message ``@@COMMAND <line>``
naming the line of the command after it. For every theorem a command adds or finds
already present with the same statement, after the kernel accepted it, Lean logs
``added <name> : <statement>`` as an information message; Lean prints information
messages without their position, and in the order of the commands, so an ``added``
line belongs to the command the last marker named. Warnings and errors carry their
line.

A command is credited only with what it was asked for. Each command names its own
outputs: ``derive_idle T`` adds ``T.idle``, ``derive_conjuncts T`` the ``T.part_k``,
``derive_weakening T`` the ``T.weakened_i`` and ``T.use_i_j``, ``derive_frontier T``
the ``T.frontier_…``, and ``derive_factor T`` only ``T.factored`` (or
``ErdosProblems.ArgumentGraph.Factored.T``). The factorings of the lemmas a
``derive_factor`` derives on the way are checked theorems too, and are recorded as
``helpers``, but a command whose own factoring was refused is not satisfied by them.
A verdict has three parts:

* ``satisfied``: some requested output was added and no error is at the line;
* ``clean``: satisfied and no failure (a warning outside ``argumentGraph.strict``)
  either, so the command can run in strict mode; ``added`` is ``clean``;
* ``complete``: the log reaches past the command (a later marker, or the probe's
  closing ``@@END``). A command whose evidence the log does not close has no
  verdict: it stays unverified rather than passing or failing.

The probe's closing ``DERIVED <name> <hash>`` lines give the statement hash of
every theorem the file itself added. A name a command reports that the file did not
add, or that an earlier command of the file already reported, was ``reused``; the
others were ``created`` by it.

Usage:
    python3 scripts/frontier_verdicts.py --run RUN_ID [--run RUN_ID ...] --artifact DIR --probes DIR --out OUT.json

``--artifact`` holds the probes' logs (``<stem>.log`` is a probe's full output);
``--probes`` holds the probe sources that ran.
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
END = "@@END"
FACTORED_PREFIX = "ErdosProblems.ArgumentGraph.Factored."


def unescape(name: str) -> str:
    return name.replace("«", "").replace("»", "")


def requested(command: str, name: str) -> bool:
    """Whether ``name`` is an output ``command`` was asked for (not a helper)."""
    parts = command.split()
    if len(parts) < 2:
        return False
    verb, theorem = parts[0], unescape(parts[1])
    if verb == "derive_factor":
        return name in (f"{theorem}.factored", FACTORED_PREFIX + theorem)
    if verb == "derive_idle":
        return name == f"{theorem}.idle"
    suffixes = {"derive_conjuncts": ("part_",), "derive_weakening": ("weakened_", "use_"),
                "derive_frontier": ("frontier_",)}.get(verb, ())
    if not name.startswith(theorem + "."):
        return False
    rest = name[len(theorem) + 1:]
    return "." not in rest and rest.startswith(suffixes)


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


def messages(log: str, markers: dict[int, int] | None = None) -> tuple[list[dict], list[int], bool]:
    """The log's messages, each with its continuation lines; the command lines whose
    markers the log reached, in order; and whether it reached the closing ``@@END``
    (or, for a log from before that marker, the ``DERIVED`` lines). A positionless line
    after a marker is an information message of the command the marker names."""
    out: list[dict] = []
    reached: list[int] = []
    ended = False
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
            reached.append(command_line)
            current = None
        elif line.strip() == END or line.startswith("DERIVED\t"):
            ended = True
            current = None
            command_line = 0
        elif (line.startswith("added ") or line.startswith("placed ")) and command_line:
            current = {"line": command_line, "kind": "info", "text": line}
            out.append(current)
        elif current is not None:
            current["text"] += "\n" + line
    return out, reached, ended


def probe_verdicts(source: str, log: str, stem: str) -> dict[str, dict]:
    commands = {i + 1: line.strip() for i, line in enumerate(source.splitlines())
                if line.startswith("derive_") or line.startswith("set_option argumentGraph.strict false in derive_")}
    found, reached, ended = messages(log, marker_lines(source))
    by_line: dict[int, list[dict]] = {}
    for m in found:
        by_line.setdefault(m["line"], []).append(m)
    created_here = {m["name"] for m in DERIVED.finditer(log)}
    seen: set[str] = set()
    closed = set(reached[:-1]) | (set(reached[-1:]) if ended else set())
    out: dict[str, dict] = {}
    for line, raw in sorted(commands.items()):
        command = raw.removeprefix("set_option argumentGraph.strict false in ").strip()
        here = by_line.get(line, [])
        statements: dict[str, str] = {}
        placements = []
        for m in here:
            match = ADDED.match(m["text"]) if m["kind"] == "info" else None
            if match:
                statements[match["name"]] = " ".join(match["statement"].split())
            placed = PLACED.match(m["text"]) if m["kind"] == "info" else None
            if placed:
                placements.append({"derived": placed["name"],
                                   "hypothesis": " ".join(placed["hypothesis"].split()),
                                   "claims": " ".join(placed["claims"].split())})
        failures = [m["text"] for m in here if m["kind"] in ("error", "warning")
                    and not m["text"].startswith("unused variable") and not m["text"].startswith("linter")]
        errors = [m for m in here if m["kind"] == "error"]
        names = sorted(statements)
        own = [n for n in names if requested(command, n)]
        created = [n for n in names if n in created_here and n not in seen]
        seen.update(names)
        if line not in closed or (not statements and not failures):
            continue
        satisfied = bool(own) and not errors
        clean = satisfied and not failures
        out[command] = {"added": clean, "satisfied": satisfied, "clean": clean, "complete": True,
                        "names": own, "helpers": [n for n in names if n not in own],
                        "created": created, "reused": [n for n in names if n not in created],
                        "statements": statements, "placements": placements,
                        "message": " | ".join(failures)[:800], "probe": stem}
    return out


def better(new: dict, old: dict) -> bool:
    """Of two verdicts for one command (it ran in two probes), the stronger evidence."""
    rank = lambda v: (v["clean"], v["satisfied"], len(v["names"]))
    return rank(new) > rank(old)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--run", action="append", required=True)
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
            if command not in verdicts or better(verdict, verdicts[command]):
                verdicts[command] = verdict
        hashes.update({m["name"]: m["hash"] for m in DERIVED.finditer(log)})
    args.out.write_text(json.dumps({"probe_run": args.run, "commands": verdicts, "statement_hashes": hashes,
                                    "probes_without_log": missing}, indent=1, ensure_ascii=False) + "\n",
                        encoding="utf-8")
    clean = sum(1 for v in verdicts.values() if v["clean"])
    partial = sum(1 for v in verdicts.values() if v["satisfied"] and not v["clean"])
    helpers = {n for v in verdicts.values() for n in v["helpers"]}
    print(f"{len(verdicts)} commands with a verdict: {clean} clean, {partial} satisfied with failures, "
          f"{len(verdicts) - clean - partial} not satisfied; {len(helpers)} helper theorems; "
          f"{len(hashes)} statement hashes; {len(missing)} probes without a log -> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
