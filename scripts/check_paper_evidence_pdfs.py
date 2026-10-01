#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the evidence marks as a reader meets them: in the rendered PDFs.

For each of the sixteen papers, against its generated evidence file
paper/evidence/<paper>.tex and evidence/paper_evidence.json:

  * every declared result has one inline "Lean" link with its declared target, and
    one inline "Comparator" link when compared, or its own pending-record link;
  * final concordance rows bind each statement name and link to its named
    destination; legacy PDFs are checked against their theorem headings;
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

    # pypdf may report the memo matrix of the preceding text object when
    # whitespace separates BT/ET objects. Capture the position at the text
    # operator instead, so the second pair of table columns is read correctly.
    origin: list[tuple[float, float] | None] = [None]

    def before(operator, _operands, cm, tm):
        if operator in (b"Tj", b"TJ") and origin[0] is None:
            origin[0] = (tm[4] * cm[0] + tm[5] * cm[2] + cm[4],
                         tm[4] * cm[1] + tm[5] * cm[3] + cm[5])

    def visit(text, cm, tm, _font, _size):
        if text.strip():
            x, y = origin[0] if origin[0] is not None else (
                tm[4] * cm[0] + tm[5] * cm[2] + cm[4],
                tm[4] * cm[1] + tm[5] * cm[3] + cm[5])
            runs.append((x, y, text))
        origin[0] = None

    page.extract_text(visitor_text=visit, visitor_operand_before=before)
    return runs


def row_left(destination) -> float | None:
    try:
        return float(destination.left)
    except (TypeError, ValueError):
        return None


def row_name_matches(runs: list, name: str, top: float,
                     left: float | None, proof_left: float) -> bool:
    """Match the complete visible name within its column, including one wrap."""
    starts = [(x, y, text) for x, y, text in runs
              if abs(y - top) <= TOLERANCE and x < proof_left - 2
              and (left is None or left - 3 <= x < left + 80)]
    want = "".join(name.split())
    for x, y, _text in starts:
        column_left = left if left is not None else x
        parts = [(xx, yy, text) for xx, yy, text in runs
                 if column_left - 3 <= xx < min(proof_left - 2, column_left + 80)
                 and y - 22 <= yy <= y + 2]
        actual = "".join("".join(text.split())
                         for _xx, _yy, text in sorted(parts, key=lambda t: (-t[1], t[0])))
        if re.match(re.escape(want) + r"(?:\D|$)", actual):
            return True
    return False


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
                records: dict | None = None, names: dict | None = None) -> list[str]:
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
    # A named destination binds each concordance row to its original statement.
    # Legacy PDFs retain the heading-placement check; new PDFs must contain
    # every row, with the correct target and number, in the final concordance.
    destinations = reader.named_destinations
    concordance = any(name.startswith("verification-result.") for name in destinations)
    for label, (text, lean, comparator) in marks.items():
        result = results.get(label)
        if result is None:
            problems.append(f"{label}: no result in the evidence mapping")
        record = records.get(label) if records is not None else None
        if records is not None and record is None:
            problems.append(f"{label}: no generated evidence record/status mapping")
        if record is not None and record[2] == "compared" and not comparator:
            problems.append(f"{label}: compared status has no Comparator target")
        hits = [i for i, (n, r, u) in enumerate(links)
                if u == lean and r[0] < text_right and i not in used]
        row_destination = destinations.get("verification-result." + label)
        if concordance:
            if row_destination is None:
                problems.append(f"{label}: missing verification concordance row")
                continue
            row_page = reader.get_destination_page_number(row_destination) + 1
            row_top = float(row_destination.top)
            hits = [i for i in hits if links[i][0] == row_page
                    and abs(links[i][1][1] - row_top) <= 22.0
                    and (row_left(row_destination) is None or
                         row_left(row_destination) <= links[i][1][0] < row_left(row_destination) + 205)]
        elif result and result.get("page"):
            hits = [i for i in hits if links[i][0] == int(result["page"])]
        if not hits:
            problems.append(f"{label}: no inline Lean link with its target beside the heading"
                            + (f" of page {result['page']}" if result and result.get('page') else ""))
            continue
        chosen = None
        for i in hits:
            n, rect, _u = links[i]
            if result and (result.get("number") or (concordance and names is not None)):
                if n not in text_cache:
                    text_cache[n] = heading_lines(reader.pages[n - 1])
                # Text extraction may drop the space inside a bold heading ("Theorem1.3").
                want = ("".join(names[label].split()) if concordance and names is not None
                        else f"Result{result['number']}" if concordance
                        else f"{result['printed_kind']}{result['number']}")
                if concordance:
                    if not row_name_matches(text_cache[n], want, row_top,
                                            row_left(row_destination), rect[0]):
                        continue
                elif not any(abs(t[1] - rect[1]) <= TOLERANCE + max(rect[3] - rect[1], HEADING_LINE_STEP)
                             and t[0] < text_right
                             and re.match(re.escape(want) + r"(?:\D|$)", "".join(t[2].split()))
                             for t in text_cache[n]):
                    continue
            chosen = i
            break
        if chosen is None:
            problems.append(f"{label}: its inline Lean link is not level with the heading "
                            f"{names.get(label, label) if concordance and names is not None else str(result.get('printed_kind')) + ' ' + str(result.get('number'))}")
            continue
        n, rect, _u = links[chosen]
        inline = [i for i, (m, r, _u) in enumerate(links)
                  if m == n and r[0] < text_right and i not in used
                  and abs(r[1] - rect[1]) <= TOLERANCE + (rect[3] - rect[1])
                  and (not concordance or row_left(row_destination) is None or
                       row_left(row_destination) <= r[0] < row_left(row_destination) + 205)]

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
    if concordance:
        for label, record in (records or {}).items():
            if label in marks:
                continue
            destination = destinations.get("verification-result." + label)
            result = results.get(label)
            if destination is None or result is None:
                problems.append(f"{label}: missing verification row for unmarked statement")
                continue
            n = reader.get_destination_page_number(destination) + 1
            top = float(destination.top)
            hits = [i for i, (page, rect, uri) in enumerate(links)
                    if page == n and abs(rect[1] - top) <= 22.0
                    and uri == record[0] and i not in used
                    and (row_left(destination) is None or
                         row_left(destination) <= rect[0] < row_left(destination) + 205)]
            if len(hits) != 1:
                problems.append(f"{label}: missing or duplicated partial-support record")
            else:
                used.update(hits)
            want = ("".join(names[label].split()) if names is not None
                    else "Result" + str(result.get("number", "")))
            proof_left = min((links[i][1][0] for i in hits), default=(row_left(destination) or 0) + 80)
            if not row_name_matches(heading_lines(reader.pages[n - 1]), want, top,
                                    row_left(destination), proof_left):
                problems.append(f"{label}: wrong unmarked statement number")
        # A second Lean/Comparator presentation elsewhere cannot hide behind
        # the dictionary of named row destinations. Ordinary source citations
        # are permitted; repeated evidence labels are not.
        for i, (n, rect, uri) in enumerate(links):
            if i in used or uri not in evidence_uris:
                continue
            if any(abs(y - rect[1]) <= 3.0 and abs(x - rect[0]) <= 3.0
                   and re.match(r"^(Lean|Comparator)(?:\W|$)", t.strip())
                   for x, y, t in heading_lines(reader.pages[n - 1])):
                problems.append(f"page {n}: duplicate evidence presentation outside its row")
        row_pages = [reader.get_destination_page_number(destination) + 1
                     for name, destination in destinations.items()
                     if name.startswith("verification-result.")]
        if row_pages and not any("Verification concordance" in
                                 reader.pages[n - 1].extract_text()
                                 for n in range(1, min(row_pages) + 1)):
            problems.append("verification rows have no concordance section")
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
        from paper_evidence import concordance_name
        names = {result['label']: concordance_name(result) for result in paper['results']}
        problems = check_paper(pdf, paper, declared(pid), baseline.get(pid), recorded(pid), names)
        for p in problems:
            print(f"FAIL {pid}: {p}")
        failures += len(problems)
        if not problems:
            print(f"ok   {pid}: {len(declared(pid))} results marked")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
