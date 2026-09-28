#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check docs/semantic/barriers.json against the source it cites (no Lean needed).

For every entry: the schema keys and enumerations; for a Lean entry, the file
exists, the cited line starts the named `theorem`/`lemma` (possibly with the name
on the next line), and the recorded statement (minus any ` ... ` elision)
occurs verbatim in the whitespace-collapsed source from that line; for an
authored entry, its JSON pointer resolves. Every authored pointer and every
sibling reference resolves too.

The check binds the registry's quotations to the source. Whether a barrier
rules out the class of arguments its `blocks` field describes is an authored
reading, and the kernel checks only the declaration itself.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "docs" / "semantic" / "barriers.json"
KEYS = ["id", "problem", "barrier_kind", "declaration", "source_ref", "statement", "plain_statement",
        "blocks", "route_predicates", "does_not_block", "target", "evidence_class", "axioms_note"]
KINDS = {"countermodel", "endpoint_equivalence", "method_ceiling", "finite_blindness",
         "scoped_failure_receipt", "other"}
PROBLEMS = {"249", "257", "269", "1049", "243", "251", "68", "1041", "cross"}
EVIDENCE = {"kernel_checked", "authored_record", "both"}
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(theorem|lemma)\s+([^\s(:{\[]+)")
BARE_KEYWORD = re.compile(r"^\s*(?:private\s+)?(theorem|lemma)\s*$")


class Source:
    def __init__(self, root: Path):
        self.root = root
        self._lines: dict[str, list[str]] = {}

    def lines(self, path: str) -> list[str]:
        if path not in self._lines:
            self._lines[path] = (self.root / path).read_text(encoding="utf-8").split("\n")
        return self._lines[path]

    def declaration_at(self, path: str, line: int) -> str | None:
        rows = self.lines(path)
        if not 1 <= line <= len(rows):
            return None
        text = rows[line - 1]
        match = DECLARATION.match(text)
        if match:
            return match.group(2)
        if BARE_KEYWORD.match(text) and line < len(rows):
            follow = re.match(r"^([^\s(:{\[]+)", rows[line].strip())
            return follow.group(1) if follow else None
        return None

    def resolve(self, pointer: str):
        path, fragment = pointer.split("#", 1)
        value = json.loads((self.root / path).read_text(encoding="utf-8"))
        for token in [t for t in fragment.split("/") if t]:
            value = value[int(token)] if isinstance(value, list) else value[token]
        return value


def collapse(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def check(registry: dict, root: Path = ROOT) -> list[str]:
    source = Source(root)
    failures: list[str] = []
    seen: set[str] = set()
    for entry in registry.get("entries", []):
        eid = entry.get("id")
        if list(entry.keys()) != KEYS:
            failures.append(f"{eid}: keys {list(entry.keys())}")
            continue
        if eid in seen:
            failures.append(f"{eid}: duplicate id")
        seen.add(eid)
        if (entry["problem"] not in PROBLEMS or entry["barrier_kind"] not in KINDS
                or entry["evidence_class"] not in EVIDENCE):
            failures.append(f"{eid}: value outside its enumeration")
        for field in ("plain_statement", "blocks", "target"):
            if not entry[field]:
                failures.append(f"{eid}: empty {field}")
        if entry["declaration"]:
            path, _, line_text = entry["source_ref"].rpartition(":")
            try:
                line = int(line_text)
                name = source.declaration_at(path, line)
            except (OSError, ValueError) as error:
                failures.append(f"{eid}: unreadable source_ref {entry['source_ref']} ({error})")
                continue
            if name is None or name.split(".")[-1] != entry["declaration"].split(".")[-1]:
                failures.append(f"{eid}: {entry['source_ref']} starts {name!r}, not {entry['declaration']}")
                continue
            window = collapse(" ".join(source.lines(path)[line - 1: line + 150]))
            for fragment in (entry["statement"] or "").split(" ... "):
                if collapse(fragment) not in window:
                    failures.append(f"{eid}: statement fragment not in source: {fragment[:80]}")
                    break
        else:
            try:
                source.resolve(entry["source_ref"])
            except Exception as error:  # noqa: BLE001 - any resolution failure is a finding
                failures.append(f"{eid}: authored source_ref does not resolve ({error})")
    for eid, pointers in (registry.get("authored_pointers") or {}).items():
        for pointer in pointers:
            try:
                source.resolve(pointer)
            except Exception as error:  # noqa: BLE001
                failures.append(f"{eid}: pointer does not resolve {pointer} ({error})")
    for eid, siblings in (registry.get("siblings") or {}).items():
        for sibling in siblings:
            path, _, line_text = sibling["source_ref"].rpartition(":")
            name = source.declaration_at(path, int(line_text))
            if name is None or name.split(".")[-1] != sibling["declaration"].split(".")[-1]:
                failures.append(f"{eid}: sibling {sibling['source_ref']} starts {name!r}")
    return failures


def main() -> int:
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    failures = check(registry)
    entries = len(registry.get("entries", []))
    if failures:
        print(f"barrier registry: {len(failures)} failures in {entries} entries")
        for failure in failures:
            print("  ", failure)
        return 1
    print(f"ok: barrier registry ({entries} entries checked against source)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
