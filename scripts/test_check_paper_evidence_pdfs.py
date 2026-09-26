#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for scripts/check_paper_evidence_pdfs.py.

Each fixture is a one-page PDF written in memory with a result heading and margin links,
so the check runs without TeX.  The sound page must pass; a mark with the wrong target, a
mark away from its heading, a missing Comparator mark, an unexplained margin link, two
colliding marks, a workflow-run link and a paper longer than its baseline must each fail.
The generated evidence file's dagger mark must parse.  A check that cannot fail proves
nothing.  Needs pypdf.
"""

from __future__ import annotations

import io
import tempfile
from contextlib import redirect_stderr
from pathlib import Path

from pypdf import PdfWriter
from pypdf.generic import (
    ArrayObject,
    DecodedStreamObject,
    DictionaryObject,
    FloatObject,
    NameObject,
    TextStringObject,
)

import check_paper_evidence_pdfs as check

LEAN = "https://github.com/wcook04/plectis-erdos/blob/" + "a" * 40 + "/lean/X.lean#L4"
CMP = "https://github.com/wcook04/plectis-erdos/blob/" + "b" * 40 + "/evidence/x.md#res-a-comparator"
HEAD_Y = 700.0


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def link(rect: list[float], uri: str) -> DictionaryObject:
    return DictionaryObject({
        NameObject("/Type"): NameObject("/Annot"),
        NameObject("/Subtype"): NameObject("/Link"),
        NameObject("/Rect"): ArrayObject([FloatObject(v) for v in rect]),
        NameObject("/A"): DictionaryObject({
            NameObject("/S"): NameObject("/URI"),
            NameObject("/URI"): TextStringObject(uri),
        }),
    })


def pdf(links: list[tuple[list[float], str]], pages: int = 1, heading_y: float = HEAD_Y) -> Path:
    writer = PdfWriter()
    for index in range(pages):
        page = writer.add_blank_page(595.28, 841.89)
        if index == 0:
            font = DictionaryObject({
                NameObject("/Type"): NameObject("/Font"),
                NameObject("/Subtype"): NameObject("/Type1"),
                NameObject("/BaseFont"): NameObject("/Helvetica"),
            })
            page[NameObject("/Resources")] = DictionaryObject({
                NameObject("/Font"): DictionaryObject({NameObject("/F1"): writer._add_object(font)}),
            })
            stream = DecodedStreamObject()
            stream.set_data(f"BT /F1 11 Tf 89 {heading_y} Td (Theorem 1.1) Tj ET".encode())
            page[NameObject("/Contents")] = writer._add_object(stream)
            page[NameObject("/Annots")] = ArrayObject([writer._add_object(link(r, u)) for r, u in links])
    handle = tempfile.NamedTemporaryFile(suffix=".pdf", delete=False)
    buffer = io.BytesIO()
    writer.write(buffer)
    handle.write(buffer.getvalue())
    handle.close()
    return Path(handle.name)


PAPER = {"results": [{"label": "res:a", "page": "1", "number": "1.1", "printed_kind": "Theorem"}]}
MARKS = {"res:a": ("Lean", LEAN, CMP)}
SOUND = [([519.8, HEAD_Y - 2.6, 538.1, HEAD_Y + 10.6], LEAN), ([519.8, HEAD_Y - 15.0, 565.0, HEAD_Y - 1.8], CMP)]


def problems(links: list[tuple[list[float], str]], *, marks=MARKS, paper=PAPER, baseline: int | None = 1,
             pages: int = 1) -> list[str]:
    return check.check_paper(pdf(links, pages=pages), paper, marks, baseline)


def test_sound_page_passes() -> None:
    require(problems(SOUND) == [], f"the sound page failed: {problems(SOUND)}")


def test_wrong_target_fails() -> None:
    bad = [([519.8, HEAD_Y - 2.6, 538.1, HEAD_Y + 10.6], LEAN.replace("#L4", "#L5")), SOUND[1]]
    found = problems(bad)
    require(any("no Lean mark" in p for p in found), f"a mark with the wrong target passed: {found}")


def test_mark_away_from_its_heading_fails() -> None:
    low = [([r[0], r[1] - 300, r[2], r[3] - 300], u) for r, u in SOUND]
    require(any("not level" in p for p in problems(low)), "a mark away from its heading passed")


def test_missing_comparator_fails() -> None:
    require(any("no Comparator mark" in p for p in problems(SOUND[:1])), "a missing Comparator mark passed")


def test_unexplained_margin_link_fails() -> None:
    extra = SOUND + [([519.8, 400.0, 538.1, 413.2], "https://example.invalid/x")]
    require(any("belongs to no declared result" in p for p in problems(extra)),
            "an unexplained margin link passed")


def test_colliding_marks_fail() -> None:
    second = {"res:a": MARKS["res:a"], "res:b": ("Lean", LEAN + "0", "")}
    paper = {"results": PAPER["results"] + [{"label": "res:b", "page": "1", "number": None,
                                             "printed_kind": "Theorem"}]}
    clash = SOUND + [([519.8, HEAD_Y - 6.0, 538.1, HEAD_Y + 7.0], LEAN + "0")]
    require(any("collide" in p for p in problems(clash, marks=second, paper=paper)),
            "two overlapping marks passed")


def test_workflow_run_link_fails() -> None:
    run = SOUND + [([100.0, 300.0, 200.0, 312.0], "https://github.com/o/r/actions/runs/123")]
    require(any("workflow run" in p for p in problems(run)), "a workflow-run link passed")


def test_paper_longer_than_baseline_fails() -> None:
    require(any("longer than the baseline" in p for p in problems(SOUND, pages=2, baseline=1)),
            "a paper longer than its baseline passed")


def test_dagger_mark_declaration_parses() -> None:
    line = ("\\DeclareResultEvidence{res:x}{Lean\\textsuperscript{\\dag}}"
            "{https://a/b.md\\#res-x}{https://a/b.md\\#res-x-comparator}")
    found = check.DECLARE.findall(line)
    require(found == [("res:x", "Lean\\textsuperscript{\\dag}", "https://a/b.md\\#res-x",
                       "https://a/b.md\\#res-x-comparator")], f"a dagger mark did not parse: {found}")


def test_unknown_paper_id_cannot_pass_without_checks() -> None:
    error = io.StringIO()
    with redirect_stderr(error):
        result = check.main(["--paper", "not-an-evidence-mark-paper"])
    require(result == 2 and "unknown evidence-mark paper ID" in error.getvalue(),
            "an unknown paper selection passed without checking any PDF")


def main() -> int:
    tests = [
        test_sound_page_passes,
        test_wrong_target_fails,
        test_mark_away_from_its_heading_fails,
        test_missing_comparator_fails,
        test_unexplained_margin_link_fails,
        test_colliding_marks_fail,
        test_workflow_run_link_fails,
        test_paper_longer_than_baseline_fails,
        test_dagger_mark_declaration_parses,
        test_unknown_paper_id_cannot_pass_without_checks,
    ]
    for test in tests:
        test()
    print(f"test_check_paper_evidence_pdfs: {len(tests)} fixtures; every misplaced, missing, "
          "stray or colliding mark, run link and overlong paper fails")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
