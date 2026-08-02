#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Assemble the two long reasoning papers from reviewable authored parts.

The public manuscripts are deliberately flat: Pandoc and TeX must see every
section without following a private include tree. The authored sources live
under paper/reasoning-parts and this builder inlines them, retaining a visible
marker before every part. The --check mode is a release freshness gate.

The --bootstrap mode is a one-time migration aid. It splits an existing flat
manuscript at its part markers and refuses to overwrite an existing parts
directory. Normal authoring uses --write after editing a part.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
PARTS_ROOT = ROOT / "paper" / "reasoning-parts"
MARKER_RE = re.compile(r"^% ---- part ([a-z0-9_]+) ----\n", re.MULTILINE)

PAPERS = {
    "249": {
        "output": ROOT / "paper" / "erdos249-totient-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos249",
        "parts": (
            "a249_front",
            "a249_p0",
            "a249_p1a",
            "a249_p1b",
            "a249_newdecls",
            "a249_p2",
            "a249_p3",
            "a249_p4",
            "a249_invent",
            "a249_p5",
        ),
    },
    "257": {
        "output": ROOT / "paper" / "erdos257-mersenne-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos257",
        "parts": (
            "a257_front",
            "a257_p0",
            "a257_p1a",
            "a257_p1b",
            "a257_newdecls",
            "a257_p2",
            "a257_p3",
            "a257_p4",
            "a257_invent",
            "a257_p5",
        ),
    },
}


def split_flat(text: str, expected: tuple[str, ...]) -> tuple[str, dict[str, str]]:
    matches = list(MARKER_RE.finditer(text))
    names = tuple(match.group(1) for match in matches)
    if names != expected:
        raise ValueError(f"part markers {names!r} do not match manifest {expected!r}")
    preamble = text[: matches[0].start()]
    parts: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        parts[match.group(1)] = text[match.end() : end]
    return preamble, parts


def bootstrap(key: str) -> None:
    row = PAPERS[key]
    directory: Path = row["directory"]
    if directory.exists():
        raise ValueError(f"refusing to overwrite existing authored parts: {directory}")
    output: Path = row["output"]
    preamble, parts = split_flat(output.read_text(encoding="utf-8"), row["parts"])
    directory.mkdir(parents=True)
    (directory / "preamble.tex").write_text(preamble, encoding="utf-8")
    for name, text in parts.items():
        (directory / f"{name}.tex").write_text(text, encoding="utf-8")


def assemble(key: str) -> str:
    row = PAPERS[key]
    directory: Path = row["directory"]
    chunks = [(directory / "preamble.tex").read_text(encoding="utf-8")]
    for name in row["parts"]:
        chunks.append(f"% ---- part {name} ----\n")
        chunks.append((directory / f"{name}.tex").read_text(encoding="utf-8"))
    return "".join(chunks)


def check_one(key: str) -> bool:
    row = PAPERS[key]
    output: Path = row["output"]
    actual = output.read_text(encoding="utf-8")
    expected = assemble(key)
    if actual == expected:
        return True
    relative = output.relative_to(ROOT)
    print(f"{relative}: assembled output is stale", file=sys.stderr)
    diff = difflib.unified_diff(
        actual.splitlines(),
        expected.splitlines(),
        fromfile=str(relative),
        tofile=f"assembled:{relative}",
        lineterm="",
        n=2,
    )
    for line in list(diff)[:80]:
        print(line, file=sys.stderr)
    return False


def write_one(key: str) -> None:
    row = PAPERS[key]
    output: Path = row["output"]
    expected = assemble(key)
    if not output.exists() or output.read_text(encoding="utf-8") != expected:
        output.write_text(expected, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--bootstrap", action="store_true")
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    parser.add_argument("--paper", choices=("all", "249", "257"), default="all")
    args = parser.parse_args()
    keys = tuple(PAPERS) if args.paper == "all" else (args.paper,)

    try:
        if args.bootstrap:
            for key in keys:
                bootstrap(key)
            for key in keys:
                if not check_one(key):
                    return 1
            return 0
        if args.write:
            for key in keys:
                write_one(key)
            return 0
        return 0 if all(check_one(key) for key in keys) else 1
    except (OSError, ValueError) as exc:
        print(f"assemble_reasoning_surfaces: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
