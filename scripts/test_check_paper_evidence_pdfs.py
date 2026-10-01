#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for scripts/check_paper_evidence_pdfs.py.

Each fixture is a PDF written in memory with result headings and inline links,
so the check runs without TeX.  The sound page must pass; a mark with the wrong target, a
mark away from its heading, a missing Comparator mark, duplicate inline or margin
presentations, an unexplained margin link, colliding marks, a workflow-run link and a
paper longer than its baseline must each fail. Split dagger/pending annotations and
separate results sharing a target must still pass.
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


def pdf(links: list[tuple[list[float], str]], pages: int = 1, heading_y: float = HEAD_Y,
        headings: list[tuple[float, str]] | None = None) -> Path:
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
            runs = headings if headings is not None else [(heading_y, "Theorem 1.1")]
            stream.set_data("\n".join(f"BT /F1 11 Tf 89 {y} Td ({text}) Tj ET"
                                      for y, text in runs).encode())
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
SOUND = [([175.0, HEAD_Y - 2.6, 200.0, HEAD_Y + 8.0], LEAN),
         ([210.0, HEAD_Y - 2.6, 260.0, HEAD_Y + 8.0], CMP)]
MARGIN = [([519.8, HEAD_Y - 2.6, 538.1, HEAD_Y + 10.6], LEAN),
          ([519.8, HEAD_Y - 15.0, 565.0, HEAD_Y - 1.8], CMP)]


def problems(links: list[tuple[list[float], str]], *, marks=MARKS, paper=PAPER, baseline: int | None = 1,
             pages: int = 1, headings: list[tuple[float, str]] | None = None,
             records: dict | None = None) -> list[str]:
    return check.check_paper(pdf(links, pages=pages, headings=headings), paper, marks, baseline, records)


def test_sound_page_passes() -> None:
    require(problems(SOUND) == [], f"the sound page failed: {problems(SOUND)}")


def test_wrong_target_fails() -> None:
    bad = [(SOUND[0][0], LEAN.replace("#L4", "#L5")), SOUND[1]]
    found = problems(bad)
    require(any("no inline Lean" in p for p in found), f"a mark with the wrong target passed: {found}")


def test_mark_away_from_its_heading_fails() -> None:
    low = [([r[0], r[1] - 300, r[2], r[3] - 300], u) for r, u in SOUND]
    require(any("not level" in p for p in problems(low)), "a mark away from its heading passed")


def test_long_title_allows_only_one_inline_line_wrap() -> None:
    def shifted(lines: int) -> list[tuple[list[float], str]]:
        distance = lines * check.HEADING_LINE_STEP
        return [([r[0], r[1] - distance, r[2], r[3] - distance], u) for r, u in SOUND]

    require(problems(shifted(1)) == [], "links immediately below a long heading failed")
    require(any("not level" in p for p in problems(shifted(2))),
            "links two body lines away from their heading passed")


def test_missing_comparator_fails() -> None:
    require(any("no inline Comparator" in p for p in problems(SOUND[:1])), "a missing Comparator mark passed")


def test_margin_only_does_not_satisfy_inline_coverage() -> None:
    found = problems(MARGIN)
    require(any("no inline Lean" in p for p in found) and
            any("margin evidence presentation is forbidden" in p for p in found),
            f"margin links alone passed inline coverage: {found}")


def test_inline_plus_margin_is_a_duplicate_presentation() -> None:
    found = problems(SOUND + MARGIN)
    require(sum("margin evidence presentation is forbidden" in p for p in found) == 2,
            f"the old duplicate presentation passed: {found}")


def test_wrong_comparator_target_fails() -> None:
    found = problems([SOUND[0], (SOUND[1][0], CMP + "-wrong")])
    require(any("no inline Comparator" in p for p in found),
            f"an inline Comparator with the wrong target passed: {found}")


def test_duplicate_inline_pair_fails() -> None:
    extra = [([r[0] + 120, r[1], r[2] + 120, r[3]], u) for r, u in SOUND]
    found = problems(SOUND + extra)
    require(any("duplicate inline Lean" in p for p in found) and
            any("duplicate inline Comparator" in p for p in found),
            f"two complete inline presentations passed: {found}")


def test_pending_comparator_must_open_its_own_record() -> None:
    record = CMP.removesuffix("-comparator")
    pending = SOUND
    marks = {"res:a": ("Lean", LEAN, "")}
    records = {"res:a": (record, "exact", "pending")}
    require(check.check_paper(pdf(pending), PAPER, marks, 1, records) == [],
            "a correct inline pending link failed")
    bad = pending[:-1]
    require(any("Comparator-pending" in p for p in check.check_paper(pdf(bad), PAPER, marks, 1, records)),
            "a pending result without its pending link passed")
    wrong = [pending[0], (pending[1][0], CMP + "-wrong")]
    require(any("Comparator-pending" in p for p in problems(wrong, marks=marks, records=records)),
            "a pending link to a different result passed")


def test_split_pending_label_passes() -> None:
    pieces = [SOUND[0], ([450.0, HEAD_Y - 2.6, 489.0, HEAD_Y + 8.0], CMP),
              ([89.0, HEAD_Y - 15.6, 113.0, HEAD_Y - 5.0], CMP)]
    marks = {"res:a": ("Lean", LEAN, "")}
    records = {"res:a": (CMP.removesuffix("-comparator"), "exact", "pending")}
    require(problems(pieces, marks=marks, records=records) == [],
            "a pending label split at its space failed")


def test_missing_generated_record_fails() -> None:
    require(any("no generated evidence record/status mapping" in p for p in problems(SOUND, records={})),
            "a result without its record/status mapping passed")


def test_split_dagger_annotation_is_one_presentation() -> None:
    marks = {"res:a": (r"Lean\textsuperscript{\dag}", LEAN, CMP)}
    dagger = ([199.0, HEAD_Y + 1.0, 205.0, HEAD_Y + 10.0], LEAN)
    # Annotation order need not be reading order.
    require(problems([dagger, SOUND[1], SOUND[0]], marks=marks) == [],
            "a Lean mark split at its dagger failed")
    duplicate = ([330.0, HEAD_Y - 2.6, 355.0, HEAD_Y + 8.0], LEAN)
    require(any("duplicate inline Lean" in p for p in problems(SOUND + [duplicate], marks=marks)),
            "two complete dagger-marked Lean presentations passed")


def test_shared_targets_still_require_each_result_heading() -> None:
    second = {"res:a": MARKS["res:a"], "res:b": MARKS["res:a"]}
    paper = {"results": PAPER["results"] + [{"label": "res:b", "page": "1", "number": "1.2",
                                             "printed_kind": "Theorem"}]}
    headings = [(HEAD_Y, "Theorem 1.1"), (HEAD_Y - 100, "Theorem 1.2")]
    both = SOUND + [([r[0], r[1] - 100, r[2], r[3] - 100], u) for r, u in SOUND]
    require(problems(both, marks=second, paper=paper, headings=headings) == [],
            "two result headings sharing their evidence targets failed")
    require(any("res:b: no inline Lean" in p for p in
                problems(SOUND, marks=second, paper=paper, headings=headings)),
            "one presentation satisfied two separate results")


def test_declared_result_must_exist_in_mapping() -> None:
    require(any("no result in the evidence mapping" in p for p in problems(SOUND, paper={"results": []})),
            "a declaration without a mapped result passed")


def test_mark_must_be_on_recorded_page() -> None:
    paper = {"results": [dict(PAPER["results"][0], page="2")]}
    require(any("of page 2" in p for p in problems(SOUND, paper=paper, pages=2, baseline=2)),
            "a mark on a different page passed")


def test_heading_number_cannot_match_a_longer_number() -> None:
    require(any("not level" in p for p in problems(SOUND, headings=[(HEAD_Y, "Theorem 1.10")])),
            "Theorem 1.10 satisfied evidence for Theorem 1.1")


def test_unexplained_margin_link_fails() -> None:
    extra = SOUND + [([519.8, 400.0, 538.1, 413.2], "https://example.invalid/x")]
    require(any("belongs to no declared result" in p for p in problems(extra)),
            "an unexplained margin link passed")


def test_colliding_marks_fail() -> None:
    clash = [SOUND[0], ([190.0, HEAD_Y - 2.6, 240.0, HEAD_Y + 8.0], CMP)]
    require(any("collide" in p for p in problems(clash)),
            "two overlapping marks passed")


def test_inline_mark_off_page_fails() -> None:
    off_page = [([-1.0, HEAD_Y - 2.6, 24.0, HEAD_Y + 8.0], LEAN), SOUND[1]]
    require(any("runs off the page" in p for p in problems(off_page)),
            "an inline evidence mark running off the page passed")


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
        test_long_title_allows_only_one_inline_line_wrap,
        test_missing_comparator_fails,
        test_margin_only_does_not_satisfy_inline_coverage,
        test_inline_plus_margin_is_a_duplicate_presentation,
        test_wrong_comparator_target_fails,
        test_duplicate_inline_pair_fails,
        test_pending_comparator_must_open_its_own_record,
        test_split_pending_label_passes,
        test_missing_generated_record_fails,
        test_split_dagger_annotation_is_one_presentation,
        test_shared_targets_still_require_each_result_heading,
        test_declared_result_must_exist_in_mapping,
        test_mark_must_be_on_recorded_page,
        test_heading_number_cannot_match_a_longer_number,
        test_unexplained_margin_link_fails,
        test_colliding_marks_fail,
        test_inline_mark_off_page_fails,
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
