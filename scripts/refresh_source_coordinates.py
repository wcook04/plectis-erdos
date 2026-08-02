#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Refresh claim and paper source lines from the declaration atlas.

Declaration names and module paths remain authored.  This script updates only
their line coordinates after a checked Lean-source change.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "docs" / "claims.json"
ATLAS = ROOT / "docs" / "declaration_atlas.json"
PAPERS = (
    ROOT / "paper" / "erdos249-257-main-paper.tex",
    ROOT / "paper" / "erdos-257-mersenne-support-subseries.tex",
)
LINK_RE = re.compile(
    r"\\([lm](?:refx?|word))\{([^}]+)\}\{\d+\}\{([^}]+)\}"
    r"(?:\{((?:[^{}]|\{[^{}]*\})*)\})?"
)


def paper_anchor_line(anchor: dict[str, object]) -> int:
    path = ROOT / str(anchor["source"])
    text = path.read_text(encoding="utf-8")
    pattern = re.compile(
        rf"\\begin\{{{re.escape(str(anchor['environment']))}\}}"
        rf"\[{re.escape(str(anchor['title']))}\]"
    )
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise RuntimeError(
            f"paper anchor must resolve exactly once: {anchor} (matches={len(matches)})"
        )
    return text.count("\n", 0, matches[0].start()) + 1


def declaration_lines() -> dict[tuple[str, str], int]:
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    rows: dict[tuple[str, str], list[int]] = {}
    for decl in atlas["declarations"]:
        rows.setdefault((decl["module"], decl["name"]), []).append(decl["line"])
    duplicate = {key: values for key, values in rows.items() if len(values) != 1}
    if duplicate:
        raise RuntimeError(f"ambiguous declaration coordinates: {duplicate}")
    return {key: values[0] for key, values in rows.items()}


def render() -> tuple[str, dict[Path, str]]:
    lines = declaration_lines()
    claims = json.loads(CLAIMS.read_text(encoding="utf-8"))
    for claim in claims["claims"]:
        for decl in claim["declarations"]:
            key = (decl["module"], decl["name"])
            if key not in lines:
                raise RuntimeError(f"claim declaration absent from atlas: {key}")
            decl["line"] = lines[key]
    for proposition in claims["remaining_open_propositions"]:
        anchor = proposition.get("paper_anchor")
        if anchor:
            anchor["line"] = paper_anchor_line(anchor)

    def replace(match: re.Match[str]) -> str:
        macro, filename, name, label = match.groups()
        if filename.startswith("Erdos249257/"):
            module = filename
        elif filename.startswith("ErdosProblems/"):
            module = filename
        elif re.match(r"Erdos\d+/", filename):
            module = f"ErdosProblems/{filename}"
        elif macro.startswith("m"):
            module = f"ErdosProblems/{filename}"
        else:
            module = f"Erdos249257/{filename}"
        key = (module, name)
        if key not in lines:
            raise RuntimeError(f"paper declaration absent from atlas: {key}")
        rendered = f"\\{macro}{{{filename}}}{{{lines[key]}}}{{{name}}}"
        if macro.endswith("word"):
            if label is None:
                raise RuntimeError(f"semantic paper link lacks a label: {key}")
            rendered += f"{{{label}}}"
        return rendered

    papers = {
        path: LINK_RE.sub(replace, path.read_text(encoding="utf-8"))
        for path in PAPERS
    }
    return json.dumps(claims, ensure_ascii=False, indent=2) + "\n", papers


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--claims-only",
        action="store_true",
        help="refresh docs/claims.json without writing the authored paper",
    )
    args = parser.parse_args()
    claims, papers = render()
    if args.check:
        stale = []
        if CLAIMS.read_text(encoding="utf-8") != claims:
            stale.append("docs/claims.json")
        if not args.claims_only:
            for path, paper in papers.items():
                if path.read_text(encoding="utf-8") != paper:
                    stale.append(str(path.relative_to(ROOT)))
        if stale:
            print("source coordinates are stale: " + ", ".join(stale))
            return 1
        print("source coordinates current")
        return 0
    CLAIMS.write_text(claims, encoding="utf-8")
    if args.claims_only:
        print("refreshed claim source coordinates")
    else:
        for path, paper in papers.items():
            path.write_text(paper, encoding="utf-8")
        print("refreshed claim and paper source coordinates")
    return 0


if __name__ == "__main__":
    sys.exit(main())
