#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the evidence marks as a reader meets them: in the rendered PDFs.

For each of the sixteen papers, against its generated evidence file
paper/evidence/<paper>.tex and evidence/paper_evidence.json:

  * every declared result has a "Lean" link in the right margin whose target is the
    declared one, and a "Comparator" link just below it when one is declared;
  * the mark sits level with the result's printed heading ("Theorem 2.1", ...) on the page
    where its label is set, so it cannot be attached to the wrong result;
  * no margin link is unexplained, no two marks overlap, and none runs off the page;
  * no link in the paper points at a workflow run page;
  * the paper is no longer than its frozen baseline (docs/paper_page_baseline.json).

Needs pypdf.  PDFs are read from their storage paths in the publication contract, or from
--pdf-dir (a build directory holding <paper>.pdf).

  check_paper_evidence_pdfs.py [--pdf-dir DIR] [--paper PAPER_ID ...]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_MAP = ROOT / "evidence/paper_evidence.json"
BASELINE = ROOT / "docs/paper_page_baseline.json"
DECLARE = re.compile(r"\\DeclareResultEvidence\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}")
RUN_URL = re.compile(r"/actions/runs/\d+")
TOLERANCE = 7.0  # points between the mark's first baseline and the heading's baseline


def untex(url: str) -> str:
    return url.replace("\\#", "#").replace("\\%", "%")


def declared(paper_id: str) -> dict[str, tuple[str, str, str]]:
    text = (ROOT / "paper/evidence" / f"{paper_id}.tex").read_text(encoding="utf-8")
    return {m.group(1): (m.group(2), untex(m.group(3)), untex(m.group(4))) for m in DECLARE.finditer(text)}


def page_links(reader) -> list[tuple[int, list[float], str]]:
    out = []
    for number, page in enumerate(reader.pages, start=1):
        for ref in page.get("/Annots") or []:
            annot = ref.get_object()
            if annot.get("/Subtype") != "/Link":
                continue
            action = annot.get("/A")
            uri = action.get_object().get("/URI") if action is not None else None
            if uri is None:
                continue
            out.append((number, [float(v) for v in annot["/Rect"]], str(uri)))
    return out


def heading_lines(page) -> list[tuple[float, float, str]]:
    """(x, y, text) of every text run on the page, for locating result headings."""
    runs: list[tuple[float, float, str]] = []

    def visit(text, cm, tm, _font, _size):
        if text.strip():
            x = tm[4] * cm[0] + tm[5] * cm[2] + cm[4]
            y = tm[4] * cm[1] + tm[5] * cm[3] + cm[5]
            runs.append((x, y, text))

    page.extract_text(visitor_text=visit)
    return runs


def check_paper(pdf: Path, paper: dict, marks: dict, baseline: int | None) -> list[str]:
    from pypdf import PdfReader

    problems: list[str] = []
    reader = PdfReader(str(pdf))
    pages = len(reader.pages)
    if baseline is not None and pages > baseline:
        problems.append(f"{pages} pages, longer than the baseline {baseline}")
    width = float(reader.pages[0].mediabox.width)
    text_right = (width + 418.0) / 2.0
    links = page_links(reader)
    for number, _rect, uri in links:
        if RUN_URL.search(uri):
            problems.append(f"page {number}: links a workflow run ({uri})")
    margin = [(n, r, u) for n, r, u in links if r[0] >= text_right]
    used: set[int] = set()
    results = {r["label"]: r for r in paper["results"]}
    text_cache: dict[int, list] = {}
    for label, (text, lean, comparator) in marks.items():
        result = results.get(label)
        hits = [i for i, (n, r, u) in enumerate(margin) if u == lean and i not in used]
        if result and result.get("page"):
            hits = [i for i in hits if margin[i][0] == int(result["page"])]
        if not hits:
            problems.append(f"{label}: no Lean mark with its target in the margin"
                            + (f" of page {result['page']}" if result and result.get('page') else ""))
            continue
        chosen = None
        for i in hits:
            n, rect, _u = margin[i]
            if result and result.get("number"):
                if n not in text_cache:
                    text_cache[n] = heading_lines(reader.pages[n - 1])
                want = f"{result['printed_kind']} {result['number']}"
                level = [t for t in text_cache[n]
                         if abs(t[1] - rect[1]) <= TOLERANCE + (rect[3] - rect[1]) and t[0] < text_right
                         and t[2].strip().startswith(want)]
                if not level:
                    continue
            chosen = i
            break
        if chosen is None:
            problems.append(f"{label}: its Lean mark is not level with the heading "
                            f"{result['printed_kind']} {result['number']}")
            continue
        used.add(chosen)
        n, rect, _u = margin[chosen]
        if comparator:
            below = [i for i, (m, r, u) in enumerate(margin)
                     if i not in used and m == n and u == comparator and 0 < rect[1] - r[1] <= 16]
            if not below:
                problems.append(f"{label}: no Comparator mark just below its Lean mark on page {n}")
            else:
                used.add(below[0])
    for i, (n, rect, uri) in enumerate(margin):
        if i not in used:
            problems.append(f"page {n}: margin link to {uri} belongs to no declared result")
        if rect[2] > width - 4 or rect[1] < 4:
            problems.append(f"page {n}: margin link to {uri} runs off the page")
    by_page: dict[int, list[list[float]]] = {}
    for n, rect, _u in margin:
        for other in by_page.get(n, []):
            if rect[0] < other[2] and other[0] < rect[2] and rect[1] < other[3] and other[1] < rect[3]:
                problems.append(f"page {n}: two margin marks overlap")
        by_page.setdefault(n, []).append(rect)
    return problems


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--pdf-dir", type=Path)
    ap.add_argument("--paper", action="append")
    args = ap.parse_args(argv)
    evidence = json.loads(EVIDENCE_MAP.read_text(encoding="utf-8"))
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))["pages"] if BASELINE.is_file() else {}
    contract = json.loads((ROOT / "docs/publication_contract.json").read_text(encoding="utf-8"))
    storage = {}
    for artifact in contract.get("artifacts", []):
        path = artifact.get("storage_path") or artifact.get("rendered_path")
        if path:
            storage[Path(path).stem] = ROOT / path
    failures = 0
    for paper in evidence["papers"]:
        pid = paper["paper_id"]
        if args.paper and pid not in args.paper:
            continue
        pdf = (args.pdf_dir / f"{pid}.pdf") if args.pdf_dir else storage.get(pid)
        if pdf is None or not pdf.is_file():
            print(f"FAIL {pid}: no PDF at {pdf}")
            failures += 1
            continue
        problems = check_paper(pdf, paper, declared(pid), baseline.get(pid))
        for p in problems:
            print(f"FAIL {pid}: {p}")
        failures += len(problems)
        if not problems:
            print(f"ok   {pid}: {len(declared(pid))} results marked")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
