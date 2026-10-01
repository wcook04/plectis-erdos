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
    NullObject,
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
        headings: list[tuple[float, str] | tuple[float, float, str]] | None = None,
        concordance_labels: tuple[str, ...] | dict[str, float | tuple[float, float]] = ()) -> Path:
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
            positioned = []
            for run in runs:
                if len(run) == 2:
                    y, text = run
                    positioned.append((89.0, y, text))
                else:
                    positioned.append(run)
            stream.set_data("\n".join(f"BT /F1 11 Tf {x} {y} Td ({text}) Tj ET"
                                      for x, y, text in positioned).encode())
            page[NameObject("/Contents")] = writer._add_object(stream)
            page[NameObject("/Annots")] = ArrayObject([writer._add_object(link(r, u)) for r, u in links])
            for label in concordance_labels:
                position = (concordance_labels[label] if isinstance(concordance_labels, dict)
                            else heading_y)
                row_left, row_y = position if isinstance(position, tuple) else (None, position)
                writer.add_named_destination_array(
                    TextStringObject("verification-result." + label),
                    ArrayObject([page.indirect_reference, NameObject("/XYZ"),
                                 FloatObject(row_left) if row_left is not None else NullObject(),
                                 FloatObject(row_y), NullObject()]))
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


def test_concordance_rows_preserve_statement_and_target() -> None:
    headings = [(730.0, "Verification concordance"), (HEAD_Y, "Result 1.1")]
    def checked(links=SOUND, rows=("res:a",), title=headings):
        return check.check_paper(pdf(links, headings=title, concordance_labels=rows),
                                 PAPER, MARKS, 1)
    require(checked() == [], f"sound concordance failed: {checked()}")
    require(checked([(SOUND[0][0], LEAN + "-wrong"), SOUND[1]]),
            "concordance with wrong Lean target passed")
    require(checked(SOUND[:1]), "concordance with missing Comparator passed")
    require(checked(rows=("res:other",)), "missing statement row passed")
    require(checked(title=[(HEAD_Y, "Result 1.2")]), "wrong statement number passed")
    require(checked(SOUND + MARGIN), "duplicate margin presentation passed")
    displaced = [([r[0], r[1] - 100, r[2], r[3] - 100], u) for r, u in SOUND]
    require(checked(displaced), "links displaced from their concordance row passed")


def test_typed_concordance_name_must_be_visible_on_marked_row() -> None:
    paper = {"results": [dict(PAPER["results"][0], number="3.2", page="17")]}
    names = {"res:a": "Theorem 3.2"}

    def checked(heading: str | None) -> list[str]:
        headings = [(730.0, "Verification concordance")]
        if heading is not None:
            headings.append((HEAD_Y, heading))
        return check.check_paper(pdf(SOUND, headings=headings,
                                     concordance_labels=("res:a",)),
                                 paper, MARKS, 1, names=names)

    require(checked("Theorem 3.2") == [], "a correctly typed theorem row failed")
    for wrong in ("Result 3.2", "Lemma 3.2", "Theorem 3.20", None):
        found = checked(wrong)
        require(any("Theorem 3.2" in p for p in found),
                f"a missing or incorrectly named marked theorem row passed: {wrong!r}: {found}")


def test_marked_unnumbered_remark_and_passage_names() -> None:
    for name, result in (
        ("Remark 3.2, p. 17", {"printed_kind": "Remark", "number": None,
                               "statement_markdown": "*Remark 3.2* A qualification."}),
        ("Passage, p. 17", {"printed_kind": "Passage", "number": None,
                             "statement_markdown": None}),
    ):
        paper = {"results": [dict(PAPER["results"][0], page="17", **result)]}

        def checked(heading: str | None) -> list[str]:
            headings = [(730.0, "Verification concordance")]
            if heading is not None:
                headings.append((HEAD_Y, heading))
            return check.check_paper(pdf(SOUND, headings=headings,
                                         concordance_labels=("res:a",)),
                                     paper, MARKS, 1, names={"res:a": name})

        require(checked(name) == [], f"a marked unnumbered {name} row failed")
        for wrong in ("Result 3.2", name.replace("17", "18"), None):
            found = checked(wrong)
            require(any(name in p for p in found),
                    f"a missing or wrong marked unnumbered row passed: {name}: {wrong!r}: {found}")


def test_unmarked_unnumbered_names_require_exact_visible_row() -> None:
    record = CMP.removesuffix("-comparator")
    for name in ("Remark 3.2, p. 17", "Passage, p. 17"):
        paper = {"results": [dict(PAPER["results"][0], number=None, page="17",
                                   printed_kind=name.split()[0])]}
        records = {"res:a": (record, "none", "not_applicable")}
        links = [([175.0, HEAD_Y - 2.6, 260.0, HEAD_Y + 8.0], record)]

        def checked(heading: str | None) -> list[str]:
            headings = [(730.0, "Verification concordance")]
            if heading is not None:
                headings.append((HEAD_Y, heading))
            return check.check_paper(pdf(links, headings=headings,
                                         concordance_labels=("res:a",)),
                                     paper, {}, 1, records, {"res:a": name})

        require(checked(name) == [], f"a correctly named unmarked {name} row failed")
        for wrong in ("Result 3.2", name.replace("17", "18"), None):
            found = checked(wrong)
            require(any("wrong unmarked statement number" in p for p in found),
                    f"a missing or wrong unmarked {name} row passed: {wrong!r}: {found}")


def test_wrapped_unnumbered_name_requires_both_visible_lines() -> None:
    name = "Remark 3.2, p. 17"
    paper = {"results": [dict(PAPER["results"][0], number=None, page="17",
                               printed_kind="Remark")]}
    names = {"res:a": name}
    record = CMP.removesuffix("-comparator")
    first = (HEAD_Y, "Remark 3.2,")
    second = (HEAD_Y - check.HEADING_LINE_STEP, "p. 17")

    def checked(*, marked: bool, lines: list[tuple[float, str]]) -> list[str]:
        links = SOUND if marked else [([175.0, HEAD_Y - 2.6, 260.0, HEAD_Y + 8.0], record)]
        marks = MARKS if marked else {}
        records = None if marked else {"res:a": (record, "none", "not_applicable")}
        headings = [(730.0, "Verification concordance"), *lines]
        return check.check_paper(pdf(links, headings=headings,
                                     concordance_labels=("res:a",)),
                                 paper, marks, 1, records, names)

    for marked in (True, False):
        require(checked(marked=marked, lines=[first, second]) == [],
                f"a wrapped {'marked' if marked else 'unmarked'} remark name failed")
        for lines in ([first], [first, (second[0], "p. 18")]):
            found = checked(marked=marked, lines=lines)
            require(any(("heading" if marked else "wrong unmarked statement number") in p
                        for p in found),
                    f"a missing or wrong second name line passed: {marked}: {lines}: {found}")


def test_same_height_columns_share_targets_but_not_visible_names() -> None:
    second_pair = [([380.0, HEAD_Y - 2.6, 405.0, HEAD_Y + 8.0], LEAN),
                   ([420.0, HEAD_Y - 2.6, 470.0, HEAD_Y + 8.0], CMP)]
    links = SOUND + second_pair
    positions = {"res:a": (89.0, HEAD_Y), "res:b": (296.0, HEAD_Y)}
    marks = {"res:a": MARKS["res:a"], "res:b": MARKS["res:a"]}
    paper = {"results": [PAPER["results"][0],
                         {"label": "res:b", "page": "1", "number": "1.2",
                          "printed_kind": "Theorem"}]}
    names = {"res:a": "Theorem 1.1", "res:b": "Theorem 1.2"}

    def checked(headings: list[tuple[float, str] | tuple[float, float, str]],
                paper=paper, names=names) -> list[str]:
        return check.check_paper(pdf(links, headings=[(730.0, "Verification concordance"),
                                                     *headings], concordance_labels=positions),
                                 paper, marks, 1, names=names)

    sound = checked([(89.0, HEAD_Y, "Theorem 1.1"),
                     (296.0, HEAD_Y, "Theorem 1.2")])
    require(sound == [], f"same-height columns with shared evidence targets failed: {sound}")

    # Two unnumbered passages may legitimately have the same visible name.
    # Only the right column prints it here; the left row must still fail.
    passage_paper = {"results": [dict(row, printed_kind="Passage", number=None)
                                 for row in paper["results"]]}
    passage_names = {"res:a": "Passage, p. 1", "res:b": "Passage, p. 1"}
    missing_left = checked([(296.0, HEAD_Y, "Passage, p. 1")],
                           paper=passage_paper, names=passage_names)
    require(any("res:a: its inline Lean link is not level" in p for p in missing_left)
            and not any(p.startswith("res:b:") for p in missing_left),
            f"a right-column name satisfied the missing left row: {missing_left}")
    wrong_left = checked([(89.0, HEAD_Y, "Result 1.1"),
                          (296.0, HEAD_Y, "Passage, p. 1")],
                         paper=passage_paper, names=passage_names)
    require(any("res:a: its inline Lean link is not level" in p for p in wrong_left),
            f"a right-column name satisfied a wrongly named left row: {wrong_left}")


def test_unmarked_concordance_rows_are_complete_and_unique() -> None:
    record_a = CMP.removesuffix("-comparator")
    record_b = record_a.replace("#res-a", "#res-b")
    paper = {"results": [PAPER["results"][0],
                         {"label": "res:b", "page": "1", "number": "1.2", "printed_kind": "Remark"}]}
    records = {"res:a": (record_a, "none", "not_applicable"),
               "res:b": (record_b, "none", "not_applicable")}
    headings = [(730.0, "Verification concordance"),
                (HEAD_Y, "Result 1.1"), (HEAD_Y - 100, "Result 1.2")]
    links = [([175.0, HEAD_Y - 2.6, 260.0, HEAD_Y + 8.0], record_a),
             ([175.0, HEAD_Y - 102.6, 260.0, HEAD_Y - 92.0], record_b)]
    rows = {"res:a": HEAD_Y, "res:b": HEAD_Y - 100}

    def checked(links=links, rows=rows, headings=headings):
        return check.check_paper(pdf(links, headings=headings, concordance_labels=rows),
                                 paper, {}, 1, records)

    require(checked() == [], f"two unmarked result rows failed: {checked()}")
    require(any("res:b: missing verification row" in p
                for p in checked(rows={"res:a": HEAD_Y})),
            "an unmarked statement missing from the concordance passed")
    require(any("res:b: missing or duplicated partial-support record" in p
                for p in checked(links=links[:1])),
            "an unmarked row without its record link passed")
    duplicate = ([275.0, HEAD_Y - 102.6, 360.0, HEAD_Y - 92.0], record_b)
    require(any("res:b: missing or duplicated partial-support record" in p
                for p in checked(links=links + [duplicate])),
            "two record links on one unmarked row passed")
    wrong_number = headings[:-1] + [(HEAD_Y - 100, "Result 1.3")]
    require(any("res:b: wrong unmarked statement number" in p
                for p in checked(headings=wrong_number)),
            "an unmarked row with the wrong statement number passed")


def test_compared_status_without_comparator_url_fails() -> None:
    marks = {"res:a": ("Lean", LEAN, "")}
    records = {"res:a": (CMP.removesuffix("-comparator"), "exact", "compared")}
    headings = [(730.0, "Verification concordance"), (HEAD_Y, "Result 1.1")]
    found = check.check_paper(pdf(SOUND[:1], headings=headings,
                                  concordance_labels=("res:a",)),
                              PAPER, marks, 1, records)
    require(any("compared status has no Comparator target" in p for p in found),
            f"a compared row with no Comparator URL passed: {found}")


def test_duplicate_concordance_pair_away_from_first_row_fails() -> None:
    lower = [([r[0], r[1] - 100, r[2], r[3] - 100], u) for r, u in SOUND]
    for x, label in [(175.0, "Lean"), (210.0, "Comparator")]:
        headings = [(730.0, "Verification concordance"), (HEAD_Y, "Result 1.1"),
                    (x, HEAD_Y - 100, label)]
        found = check.check_paper(pdf(SOUND + lower, headings=headings,
                                      concordance_labels=("res:a",)),
                                  PAPER, MARKS, 1,
                                  {"res:a": (CMP.removesuffix("-comparator"), "exact", "compared")})
        require(any("duplicate evidence presentation outside its row" in p for p in found),
                f"a second {label} presentation away from the original row passed: {found}")


def test_pending_dagger_and_shared_targets_pass_in_concordance() -> None:
    heading = [(730.0, "Verification concordance"), (HEAD_Y, "Result 1.1")]
    record_a = CMP.removesuffix("-comparator")
    pending_marks = {"res:a": ("Lean", LEAN, "")}
    pending_records = {"res:a": (record_a, "exact", "pending")}
    pending = check.check_paper(pdf(SOUND, headings=heading,
                                    concordance_labels=("res:a",)),
                                PAPER, pending_marks, 1, pending_records)
    require(pending == [], f"a valid pending comparison in the concordance failed: {pending}")

    dagger_marks = {"res:a": (r"Lean\textsuperscript{\dag}", LEAN, CMP)}
    dagger_piece = ([199.0, HEAD_Y + 1.0, 205.0, HEAD_Y + 10.0], LEAN)
    compared_records = {"res:a": (record_a, "modulo_named_input", "compared")}
    dagger = check.check_paper(pdf([dagger_piece, SOUND[1], SOUND[0]], headings=heading,
                                   concordance_labels=("res:a",)),
                                PAPER, dagger_marks, 1, compared_records)
    require(dagger == [], f"a valid split dagger in the concordance failed: {dagger}")

    paper = {"results": PAPER["results"] +
             [{"label": "res:b", "page": "1", "number": "1.2", "printed_kind": "Theorem"}]}
    marks = {"res:a": MARKS["res:a"], "res:b": MARKS["res:a"]}
    records = {"res:a": (record_a, "exact", "compared"),
               "res:b": (record_a.replace("#res-a", "#res-b"), "exact", "compared")}
    both = SOUND + [([r[0], r[1] - 100, r[2], r[3] - 100], u) for r, u in SOUND]
    headings = heading + [(HEAD_Y - 100, "Result 1.2")]
    shared = check.check_paper(pdf(both, headings=headings,
                                   concordance_labels={"res:a": HEAD_Y,
                                                       "res:b": HEAD_Y - 100}),
                               paper, marks, 1, records)
    require(shared == [], f"two concordance rows sharing evidence targets failed: {shared}")


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
        test_concordance_rows_preserve_statement_and_target,
        test_typed_concordance_name_must_be_visible_on_marked_row,
        test_marked_unnumbered_remark_and_passage_names,
        test_unmarked_unnumbered_names_require_exact_visible_row,
        test_wrapped_unnumbered_name_requires_both_visible_lines,
        test_same_height_columns_share_targets_but_not_visible_names,
        test_unmarked_concordance_rows_are_complete_and_unique,
        test_compared_status_without_comparator_url_fails,
        test_duplicate_concordance_pair_away_from_first_row_fails,
        test_pending_dagger_and_shared_targets_pass_in_concordance,
    ]
    for test in tests:
        test()
    print(f"test_check_paper_evidence_pdfs: {len(tests)} fixtures; every misplaced, missing, "
          "stray or colliding mark, run link and overlong paper fails")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
