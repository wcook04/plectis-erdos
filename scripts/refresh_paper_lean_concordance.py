#!/usr/bin/env python3
"""Refresh one long-paper concordance entry from its proof-coverage row.

The concordance block lives in an authored reasoning part but is generated
from ``docs/paper_lean_coverage.json``.  This focused writer lets a changed
statement replace its old proof links without editing the generated block by
hand.  Run with ``--row ID --write``; omission of ``--write`` checks freshness.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "docs/paper_lean_coverage.json"
BEGIN = "% BEGIN GENERATED CONCORDANCE"
END = "% END GENERATED CONCORDANCE"


def declaration_line(file: str, name: str) -> int:
    source = (ROOT / file).read_text(encoding="utf-8")
    local = name.rsplit(".", 1)[-1]
    match = re.search(r"^[ \t]*(?:theorem|lemma|def)[ \t]+" + re.escape(local) + r"\b", source, re.M)
    if match is None:
        raise ValueError(f"{file} does not declare {name}")
    return source.count("\n", 0, match.start()) + 1


def render(row: dict, pin: str) -> str:
    links = []
    for declaration in row["lean"]["declarations"]:
        name, file = declaration["name"], declaration["file"]
        line = declaration_line(file, name)
        links.append(
            r"\href{https://github.com/wcook04/plectis-erdos/blob/"
            + pin + "/" + file + r"\#L" + str(line) + r"}{\nolinkurl{"
            + name.rsplit(".", 1)[-1] + "}}"
        )
    status = row["comparator"]["status"]
    if status != "pending" or row["palomar"]["status"] != "pending":
        raise ValueError("focused writer requires pending Comparator and Palomar statuses")
    return (
        r"\par\noindent\hangindent=1.5em The statement at~\ref{"
        + row["label"] + "}: " + ", ".join(links)
        + r". \emph{Comparator replay pending; Palomar entry pending.}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", required=True, help="exact proof-coverage row ID")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    matches = [row for row in ledger["rows"] if row["id"] == args.row]
    if len(matches) != 1 or matches[0]["side"] != "long":
        raise SystemExit(f"expected one long-paper row: {args.row}")
    row = matches[0]
    candidates = []
    for paper in ledger["papers"]:
        if paper["paper_id"] != row["paper_id"]:
            continue
        for relative in paper["sources"]:
            path = ROOT / relative
            text = path.read_text(encoding="utf-8")
            if BEGIN in text and r"\ref{" + row["label"] + "}" in text:
                candidates.append((path, text))
    if len(candidates) != 1:
        raise SystemExit(f"expected one generated concordance for {args.row}; found {len(candidates)}")
    path, text = candidates[0]
    start, end = text.index(BEGIN), text.index(END)
    prefix, block, suffix = text[:start], text[start:end], text[end:]
    old = [line for line in block.splitlines() if r"\ref{" + row["label"] + "}" in line]
    if len(old) != 1:
        raise SystemExit(f"expected one concordance entry for {args.row}; found {len(old)}")
    updated = block.replace(old[0], render(row, ledger["lean_pin"]))
    updated = re.sub(
        r"Each name links to its declaration at revision\n\\texttt\{[0-9a-f]+\}\.",
        "Each name links to the source revision in its URL.",
        updated,
        count=1,
    )
    target = prefix + updated + suffix
    if args.write:
        path.write_text(target, encoding="utf-8")
    elif target != text:
        raise SystemExit(f"stale concordance entry: {args.row}; run --write")
    print(f"concordance {'wrote' if args.write else 'current'}: {args.row} in {path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
