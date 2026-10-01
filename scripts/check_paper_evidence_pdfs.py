#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the evidence marks as a reader meets them: in the rendered PDFs.

For each of the sixteen papers, against its generated evidence file
paper/evidence/<paper>.tex and evidence/paper_evidence.json:

  * every declared result has one inline "Lean" link with its declared target, and
    one inline "Comparator" link when compared, or its own pending-record link;
  * the links sit level with the result's printed heading ("Theorem 2.1", ...) on the page
    where its label is set, so it cannot be attached to the wrong result;
  * no evidence links repeat in the margin, no margin link is unexplained, no two
    inline marks overlap, and no evidence link runs off the page;
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
DECLARE = re.compile(r"\\DeclareResultEvidence\{([^}]*)\}\{((?:[^{}]|\{[^{}]*\})*)\}\{([^}]*)\}\{([^}]*)\}")
RECORD = re.compile(r"\\DeclareResultEvidenceRecord\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}")
RUN_URL = re.compile(r"/actions/runs/\d+")
TOLERANCE = 7.0  # points between the mark's first baseline and the heading's baseline
# The 11pt article baseline (13.6 TeX points), with paper-house-style's 1.045
# linespread, in PDF points. A long title can put its inline links on the next line.
HEADING_LINE_STEP = 13.6 * 1.045 * 72.0 / 72.27
HYPERREF_LINK_MARGIN = 1.0
LINK_PIECE_GAP = 4.0


def untex(url: str) -> str:
    return url.replace("\\#", "#").replace("\\%", "%")


def declared(paper_id: str) -> dict[str, tuple[str, str, str]]:
    text = (ROOT / "paper/evidence" / f"{paper_id}.tex").read_text(encoding="utf-8")
    return {m.group(1): (m.group(2), untex(m.group(3)), untex(m.group(4))) for m in DECLARE.finditer(text)}


def recorded(paper_id: str) -> dict[str, tuple[str, str, str]]:
    text = (ROOT / "paper/evidence" / f"{paper_id}.tex").read_text(encoding="utf-8")
    return {m.group(1): (untex(m.group(2)), m.group(3), m.group(4)) for m in RECORD.finditer(text)}


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


def link_groups(indices: list[int], links: list, split: str = "") -> list[list[int]]:
    """Count presentations, allowing a dagger or a wrapped pending label to split.

    Hyperref can make a superscript dagger a second annotation.  A pending label
    can break at its space.  Complete, repeated labels must remain separate groups.
    """
    def joins(a: list[float], b: list[float]) -> bool:
        short_piece = min(a[2] - a[0], b[2] - b[0])
        beside = (abs(a[1] - b[1]) <= TOLERANCE
                  and -2 * HYPERREF_LINK_MARGIN <= b[0] - a[2] <= LINK_PIECE_GAP)
        wrapped = (0 < a[1] - b[1] <= TOLERANCE + a[3] - a[1] and b[0] < a[0])
        return ((split == "dagger" and short_piece <= 8.0 and beside)
                or (split == "pending" and short_piece <= 32.0 and (beside or wrapped)))

    groups: list[list[int]] = []
    for i in indices:
        matches = [group for group in groups
                   if any(joins(links[j][1], links[i][1]) or joins(links[i][1], links[j][1])
                          for j in group)]
        if matches:
            merged = [i] + [j for group in matches for j in group]
            groups = [group for group in groups if group not in matches]
            groups.append(merged)
        else:
            groups.append([i])
    return groups


def check_paper(pdf: Path, paper: dict, marks: dict, baseline: int | None,
                records: dict | None = None) -> list[str]:
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
    evidence_uris = {u for _text, lean, comparator in marks.values()
                     for u in (lean, comparator) if u}
    evidence_uris.update(record[0] + "-comparator" for record in (records or {}).values()
                         if record[2] == "pending")
    for n, _rect, uri in margin:
        if uri in evidence_uris:
            problems.append(f"page {n}: margin evidence presentation is forbidden ({uri})")
        else:
            problems.append(f"page {n}: margin link to {uri} belongs to no declared result")
    used: set[int] = set()
    results = {r["label"]: r for r in paper["results"]}
    text_cache: dict[int, list] = {}
    for label, (text, lean, comparator) in marks.items():
        result = results.get(label)
        if result is None:
            problems.append(f"{label}: no result in the evidence mapping")
        record = records.get(label) if records is not None else None
        if records is not None and record is None:
            problems.append(f"{label}: no generated evidence record/status mapping")
        hits = [i for i, (n, r, u) in enumerate(links)
                if u == lean and r[0] < text_right and i not in used]
        if result and result.get("page"):
            hits = [i for i in hits if links[i][0] == int(result["page"])]
        if not hits:
            problems.append(f"{label}: no inline Lean link with its target beside the heading"
                            + (f" of page {result['page']}" if result and result.get('page') else ""))
            continue
        chosen = None
        for i in hits:
            n, rect, _u = links[i]
            if result and result.get("number"):
                if n not in text_cache:
                    text_cache[n] = heading_lines(reader.pages[n - 1])
                # Text extraction may drop the space inside a bold heading ("Theorem1.3").
                want = f"{result['printed_kind']}{result['number']}"
                level = [t for t in text_cache[n]
                         if abs(t[1] - rect[1]) <= TOLERANCE + max(rect[3] - rect[1], HEADING_LINE_STEP)
                         and t[0] < text_right
                         and re.match(re.escape(want) + r"(?:\D|$)", "".join(t[2].split()))]
                if not level:
                    continue
            chosen = i
            break
        if chosen is None:
            problems.append(f"{label}: its inline Lean link is not level with the heading "
                            f"{result['printed_kind']} {result['number']}")
            continue
        n, rect, _u = links[chosen]
        inline = [i for i, (m, r, _u) in enumerate(links)
                  if m == n and r[0] < text_right and i not in used
                  and abs(r[1] - rect[1]) <= TOLERANCE + (rect[3] - rect[1])]

        def require_inline(name: str, uri: str, split: str = "") -> None:
            candidates = [i for i in inline if links[i][2] == uri]
            groups = link_groups(candidates, links, split)
            if not groups:
                problems.append(f"{label}: no inline {name} link with its target beside the heading on page {n}")
            elif len(groups) != 1 or any(len(group) > 2 for group in groups):
                problems.append(f"{label}: duplicate inline {name} presentation on page {n}")
            used.update(candidates)

        require_inline("Lean", lean, "dagger" if "dag" in text else "")
        if comparator:
            require_inline("Comparator", comparator)
        if record is not None and record[2] == "pending":
            require_inline("Comparator-pending", record[0] + "-comparator", "pending")
    for n, rect, uri in links:
        if uri in evidence_uris or rect[0] >= text_right:
            if (rect[0] < 4 or rect[1] < 4 or rect[2] > width - 4
                    or rect[3] > float(reader.pages[n - 1].mediabox.height) - 4):
                problems.append(f"page {n}: evidence link to {uri} runs off the page")
    # hyperref pads every link rectangle by 1pt (\Hy@linkmargin); two marks collide when
    # the text inside those rectangles would touch.
    pad = HYPERREF_LINK_MARGIN
    by_page: dict[int, list[tuple[list[float], str]]] = {}
    for i in sorted(used):
        n, rect, uri = links[i]
        inner = [rect[0] + pad, rect[1] + pad, rect[2] - pad, rect[3] - pad]
        for other, other_uri in by_page.get(n, []):
            if inner[0] < other[2] and other[0] < inner[2] and inner[1] < other[3] and other[1] < inner[3]:
                problems.append(f"page {n}: inline evidence marks collide ({other_uri} and {uri})")
        by_page.setdefault(n, []).append((inner, uri))
    return problems


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--pdf-dir", type=Path)
    ap.add_argument("--paper", action="append")
    args = ap.parse_args(argv)
    evidence = json.loads(EVIDENCE_MAP.read_text(encoding="utf-8"))
    known_papers = {paper["paper_id"] for paper in evidence["papers"]}
    unknown = sorted(set(args.paper or []) - known_papers)
    if unknown:
        print(
            "unknown evidence-mark paper ID(s): " + ", ".join(unknown)
            + "; valid IDs: " + ", ".join(sorted(known_papers)),
            file=sys.stderr,
        )
        return 2
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
        problems = check_paper(pdf, paper, declared(pid), baseline.get(pid), recorded(pid))
        for p in problems:
            print(f"FAIL {pid}: {p}")
        failures += len(problems)
        if not problems:
            print(f"ok   {pid}: {len(declared(pid))} results marked")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
