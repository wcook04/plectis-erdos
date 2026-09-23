#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial fixtures for the Lean-to-paper propagation check.

Each clause of ``check_lean_paper_propagation.py`` must fail on a crafted
fixture, pass once the fixture is repaired, and keep its baseline and
exemption lists honest.  A check that cannot fail proves nothing.
"""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any

import check_lean_paper_propagation as check

PIN = "a" * 40
LEAN_FILE = "lean/ErdosProblems/Synthetic/Result.lean"
OTHER_FILE = "lean/ErdosProblems/Synthetic/Other.lean"
LEAN_TEXT = """\
namespace ErdosProblems.Synthetic

/-- **`res:synthetic`.** Every synthetic statement holds. -/
theorem synthetic_result : True := trivial

/-- `res:helper` for one case only. -/
@[simp]
theorem helper_result : True := trivial

/-- Cites `res:synthetic` without leading with it. -/
theorem citing_result : True := trivial

theorem first_part : True := trivial
theorem second_part : True := trivial
theorem third_part : True := trivial
theorem fourth_part : True := trivial
theorem fifth_part : True := trivial
theorem sixth_part : True := trivial

end ErdosProblems.Synthetic
"""
OTHER_TEXT = """\
namespace ErdosProblems.Synthetic.Other

theorem synthetic_result : True := trivial

end ErdosProblems.Synthetic.Other
"""
FULL = "ErdosProblems.Synthetic.synthetic_result"
SHORT_PAPER = "paper/99/synthetic.tex"
LONG_PART = "paper/reasoning-parts/synthetic/core.tex"
PREAMBLE = "\\newtheorem{theorem}{Theorem}\n\n"
STATEMENT = (
    "\\begin{theorem}\\label{res:synthetic}\n"
    "Every synthetic statement holds.\n"
    "\\end{theorem}\n"
)
NOTE = "\\leannote{Lean: \\lproof{ErdosProblems/Synthetic/Result.lean}{4}{synthetic_result}.}\n"


def require(condition: bool, message: str) -> None:
    """Keep the contract active when Python runs with -O."""
    if not condition:
        raise AssertionError(message)


class FakeSources(check.LeanSources):
    """Tracked Lean sources held in memory."""

    def __init__(self, files: dict[str, str] | None = None) -> None:
        super().__init__()
        self.files = dict(files if files is not None else {LEAN_FILE: LEAN_TEXT, OTHER_FILE: OTHER_TEXT})

    def tracked(self) -> set[str]:
        return set(self.files)

    def text(self, relative: str) -> str | None:
        return self.files.get(relative)


def declaration(name: str = FULL, file_name: str = LEAN_FILE) -> dict[str, str]:
    return {"name": name, "file": file_name}


def row_for(
    paper_text: str,
    path: str = SHORT_PAPER,
    label: str = "res:synthetic",
    declarations: list[dict[str, str]] | None = None,
    status: str = "exact",
    comparator: dict[str, Any] | None = None,
    paper_id: str = "synthetic-short",
) -> dict[str, Any]:
    """One ledger row bound to the environment carrying ``label`` in ``paper_text``."""
    statement = next(
        found for found in check.inventory([(path, paper_text)], [])
        if label in found["labels"]
    )
    exact = status in check.EXACT
    return {
        "id": f"{paper_id}#{label}",
        "problem": 99,
        "paper_id": paper_id,
        "side": "short" if path == SHORT_PAPER else "long",
        "label": label,
        "environment": statement["environment"],
        "kind": "theorem",
        "statement_sha256": statement["statement_sha256"],
        "source": f"{path}:{statement['line']}",
        "lean": {
            "status": status,
            "declarations": [declaration()] if declarations is None else declarations,
            **({"named_inputs": ["ErdosProblems.Synthetic.Input"]} if status == "modulo_named_input" else {}),
        },
        "comparator": comparator if comparator is not None else (
            {"status": "compared", "entries": ["Corpus/E99"], "run_ids": ["1"],
             "corpus_commits": ["b" * 40]} if exact else {"status": "not_applicable"}
        ),
        "palomar": {"status": "prepared" if exact else "not_applicable"},
    }


def seal(rows: list[dict[str, Any]], sources: dict[str, list[str]]) -> dict[str, Any]:
    ledger = {
        "schema": check.LEDGER_SCHEMA,
        "lean_pin": PIN,
        "content_digest": "",
        "papers": [
            {"paper_id": paper_id, "problem": 99, "side": "short", "sources": paths}
            for paper_id, paths in sources.items()
        ],
        "rows": rows,
    }
    ledger["content_digest"] = check.content_digest(ledger)
    return ledger


def short_ledger(paper_text: str, **row_options: Any) -> dict[str, Any]:
    return seal([row_for(paper_text, **row_options)], {"synthetic-short": [SHORT_PAPER]})


def empty_baseline() -> dict[str, Any]:
    return {"schema": check.BASELINE_SCHEMA, "entries": []}


def empty_exemptions() -> dict[str, Any]:
    return {"schema": check.EXEMPTION_SCHEMA, "exemptions": []}


HELPER_EXEMPTION = {
    "declaration": "ErdosProblems.Synthetic.helper_result",
    "file": LEAN_FILE,
    "label": "res:helper",
    "reason": "Special case of the synthetic result; the ledger binds the general theorem.",
}


def evaluate(
    ledger: dict[str, Any],
    texts: dict[str, str],
    *,
    baseline: dict[str, Any] | None = None,
    exemptions: dict[str, Any] | None = None,
    sources: FakeSources | None = None,
    introduced: frozenset[tuple[str, str, str]] = frozenset(),
) -> check.Report:
    if exemptions is None:
        exemptions = {"schema": check.EXEMPTION_SCHEMA, "exemptions": [HELPER_EXEMPTION]}
    return check.evaluate(
        ledger,
        baseline or empty_baseline(),
        exemptions,
        lambda path: texts[path],
        sources or FakeSources(),
        introduced,
    )


def paper(*parts: str) -> str:
    return PREAMBLE + "".join(parts)


SIDECAR = "paper/evidence/synthetic-short.tex"


def evidence_texts(label: str = "res:synthetic", declarations: list[dict[str, str]] | None = None,
                   declared: bool = True) -> dict[str, str]:
    """The generated margin-mark file and evidence map for the synthetic short paper."""
    names = declarations if declarations is not None else [{"name": FULL, "path": LEAN_FILE}]
    evidence = {"papers": [{"paper_id": "synthetic-short", "results": [
        {"id": f"synthetic-short#{label}", "label": label, "lean": {"declarations": names}},
    ]}]}
    sidecar = (f"\\DeclareResultEvidence{{{label}}}{{Lean}}{{https://example.invalid/x}}{{}}\n"
               if declared else "")
    return {check.EVIDENCE_MAP: json.dumps(evidence), SIDECAR: sidecar}


def test_repaired_fixture_passes() -> None:
    text = paper(STATEMENT)
    report = evaluate(short_ledger(text), {SHORT_PAPER: text, **evidence_texts()})
    require(not report.failed(), f"a linked, current fixture failed: {check.summary_line(report)}")
    require(report.docstrings.total == 2, "both label-leading docstrings must be found")
    require(report.docstrings.bound == 1 and report.docstrings.exempt == 1, "docstring tally drifted")


def test_margin_marks_link_only_what_the_paper_declares() -> None:
    text = paper(STATEMENT)
    report = evaluate(short_ledger(text), {SHORT_PAPER: text, **evidence_texts(declared=False)})
    require([f["names"] for f in report.b_new] == [[FULL]],
            "(b) counted evidence for a result whose paper places no mark")
    report = evaluate(short_ledger(text), {SHORT_PAPER: text, **evidence_texts(declarations=[])})
    require(report.b_new, "(b) counted a mark whose evidence names none of the row's declarations")
    extra = [{"name": FULL, "path": LEAN_FILE},
             {"name": "ErdosProblems.Synthetic.helper_result", "path": LEAN_FILE}]
    report = evaluate(short_ledger(text), {SHORT_PAPER: text, **evidence_texts(declarations=extra)})
    require(not report.b_new and report.c_new,
            "(c) missed evidence naming a declaration the row does not bind")


def test_retired_notes_and_concordances_fail() -> None:
    for retired in (NOTE, "% BEGIN GENERATED CONCORDANCE\n\\par\\noindent x\n% END GENERATED CONCORDANCE\n"):
        text = paper(STATEMENT, retired)
        report = evaluate(short_ledger(text), {SHORT_PAPER: text, **evidence_texts()})
        require(report.retired and report.failed(),
                f"a retired generated block was accepted: {retired[:30]!r}")


def test_clause_a_missing_renamed_alias_and_untracked_declarations_fail() -> None:
    text = paper(STATEMENT, NOTE)
    cases = {
        "renamed": declaration("ErdosProblems.Synthetic.renamed_result"),
        "alias": declaration("synthetic_result"),
        "untracked": declaration(FULL, "lean/ErdosProblems/Synthetic/Untracked.lean"),
    }
    for case, bad in cases.items():
        ledger = short_ledger(text, declarations=[declaration(), bad])
        report = evaluate(ledger, {SHORT_PAPER: text})
        require(len(report.a) == 1, f"(a) did not fail for the {case} declaration: {report.a}")
    duplicated = LEAN_TEXT.replace("theorem citing_result", "theorem synthetic_result", 1)
    report = evaluate(short_ledger(text), {SHORT_PAPER: text},
                      sources=FakeSources({LEAN_FILE: duplicated, OTHER_FILE: OTHER_TEXT}))
    require(any("2 times" in failure["detail"] for failure in report.a),
            "(a) accepted a declaration name declared twice")


def test_clause_b_fails_until_every_declaration_is_rendered() -> None:
    unlinked = paper(STATEMENT)
    report = evaluate(short_ledger(unlinked), {SHORT_PAPER: unlinked})
    require([f["names"] for f in report.b_new] == [[FULL]], "(b) passed an environment with no link")

    other_file = paper(STATEMENT, NOTE.replace("Synthetic/Result.lean", "Synthetic/Other.lean"))
    report = evaluate(short_ledger(other_file), {SHORT_PAPER: other_file})
    require(report.b_new, "(b) accepted a link to a same-named declaration in another file")

    hidden = paper(STATEMENT, "\\iffalse\n", NOTE, "\\fi\n")
    report = evaluate(short_ledger(hidden), {SHORT_PAPER: hidden})
    require(report.b_new, "(b) counted a note that TeX never prints")

    hidden_inline = paper(STATEMENT.replace(
        "holds.\n",
        "holds. \\iffalse \\lword{Synthetic/Result.lean}{4}{synthetic_result}{hidden} \\fi\n",
    ))
    report = evaluate(short_ledger(hidden_inline), {SHORT_PAPER: hidden_inline})
    require(report.b_new, "(b) counted an inline link inside \\iffalse, which TeX never prints")

    commented = paper(STATEMENT, "% " + NOTE)
    report = evaluate(short_ledger(commented), {SHORT_PAPER: commented})
    require(report.b_new, "(b) counted a commented-out link")

    inline_forms = (
        "\\lean{ErdosProblems.Synthetic.synthetic\\_result}"
        "{lean/ErdosProblems/Synthetic/Result.lean:4}",
        "\\href{https://github.com/wcook04/plectis-erdos/blob/" + PIN
        + "/lean/ErdosProblems/Synthetic/Result.lean\\#L4}{\\texttt{synthetic\\_result}}",
        "\\lword{Synthetic/Result.lean}{4}{synthetic_result}{the synthetic theorem}",
    )
    for form in inline_forms:
        linked = paper(STATEMENT.replace("holds.\n", "holds. " + form + "\n"))
        report = evaluate(short_ledger(linked), {SHORT_PAPER: linked})
        require(not report.b_new and not report.c_new, f"(b) rejected the rendered link {form}")


def test_clause_b_note_count_covers_the_rest_only_when_exact() -> None:
    names = ["first_part", "second_part", "third_part", "fourth_part", "fifth_part"]
    declarations = [declaration(f"ErdosProblems.Synthetic.{name}") for name in names]
    shown = ", ".join(
        f"\\lproof{{ErdosProblems/Synthetic/Result.lean}}{{1}}{{{name}}}" for name in names[:4]
    )
    note = f"\\leannote{{Lean: {shown}, and 1 further declaration in the coverage section.}}\n"
    text = paper(STATEMENT, note)
    report = evaluate(short_ledger(text, declarations=declarations), {SHORT_PAPER: text})
    require(not report.b_new and report.linked_by_count == 1, "(b) ignored an exact note count")

    grown = [*declarations, declaration("ErdosProblems.Synthetic.sixth_part")]
    report = evaluate(short_ledger(text, declarations=grown), {SHORT_PAPER: text})
    require(len(report.b_new) == 1 and len(report.b_new[0]["names"]) == 2,
            "(b) let a stale note count cover a declaration added after it")


def test_clause_b_reads_the_concordance_of_a_long_record() -> None:
    label = "long99:res:synthetic"
    statement = STATEMENT.replace("res:synthetic", label)
    concordance = (
        "\n% BEGIN GENERATED CONCORDANCE (generated; do not edit by hand)\n"
        "\\begingroup\\small\\raggedright\n"
        f"\\par\\noindent\\hangindent=1.5em Theorem~\\ref{{{label}}}: "
        "\\href{https://github.com/wcook04/plectis-erdos/blob/" + PIN
        + "/lean/ErdosProblems/Synthetic/Result.lean\\#L4}{\\nolinkurl{synthetic_result}}.\n"
        "\\par\\endgroup\n% END GENERATED CONCORDANCE\n"
    )
    text = paper(statement, concordance)
    rows = [row_for(text, path=LONG_PART, label=label, paper_id="synthetic-long")]
    ledger = seal(rows, {"synthetic-long": [LONG_PART]})
    report = evaluate(ledger, {LONG_PART: text})
    require(not report.b_new, "(b) ignored the concordance entry of a colon-bearing label")

    stale = text.replace("synthetic_result}}", "helper_result}}")
    rows = [row_for(stale, path=LONG_PART, label=label, paper_id="synthetic-long")]
    report = evaluate(seal(rows, {"synthetic-long": [LONG_PART]}), {LONG_PART: stale})
    require(report.b_new and report.c_new, "a concordance naming another declaration passed")


def test_clause_c_flags_stale_generated_links_and_spares_author_citations() -> None:
    stale_note = paper(STATEMENT, NOTE.replace("{synthetic_result}", "{synthetic_result}, "
                       "\\lproof{ErdosProblems/Synthetic/Result.lean}{6}{helper_result}"))
    report = evaluate(short_ledger(stale_note), {SHORT_PAPER: stale_note})
    require([f["names"] for f in report.c_new]
            == [["ErdosProblems/Synthetic/Result.lean::helper_result"]],
            "(c) missed a generated note naming an unbound declaration")

    citation = STATEMENT.replace(
        "holds.\n", "holds, using \\lword{Synthetic/Result.lean}{9}{citing_result}{a lemma}.\n")
    authored = paper(citation, NOTE)
    report = evaluate(short_ledger(authored), {SHORT_PAPER: authored})
    require(not report.c_new, "(c) treated an author's supporting citation as an orphan")


def test_clause_d_label_docstrings_need_a_row_or_a_reasoned_exemption() -> None:
    text = paper(STATEMENT, NOTE)
    report = evaluate(short_ledger(text), {SHORT_PAPER: text}, exemptions=empty_exemptions())
    # The helper's docstring is followed by an attribute line; the head is line 8.
    require([f["source"] for f in report.docstrings.failures] == [f"{LEAN_FILE}:8"],
            f"(d) missed the unrecorded helper docstring: {report.docstrings.failures}")

    hits = check.leading_label_declarations(LEAN_FILE, LEAN_TEXT)
    require({hit["declaration"] for hit in hits}
            == {FULL, "ErdosProblems.Synthetic.helper_result"},
            "only docstrings that lead with a label, bold or plain, are paper statements")

    bad_entries = {
        "short reason": {**HELPER_EXEMPTION, "reason": "helper"},
        "pattern": {**HELPER_EXEMPTION, "declaration": "ErdosProblems.Synthetic.*"},
        "wrong label": {**HELPER_EXEMPTION, "label": "res:other"},
    }
    for case, entry in bad_entries.items():
        exemptions = {"schema": check.EXEMPTION_SCHEMA, "exemptions": [entry]}
        report = evaluate(short_ledger(text), {SHORT_PAPER: text}, exemptions=exemptions)
        require(report.failed(), f"(d) accepted an exemption with a {case}")

    stale_bound = {**HELPER_EXEMPTION, "declaration": FULL, "label": "res:synthetic"}
    exemptions = {"schema": check.EXEMPTION_SCHEMA, "exemptions": [HELPER_EXEMPTION, stale_bound]}
    report = evaluate(short_ledger(text), {SHORT_PAPER: text}, exemptions=exemptions)
    require(any("binds it now" in problem for problem in report.docstrings.problems),
            "(d) kept an exemption for a declaration the ledger binds")

    no_label = {**HELPER_EXEMPTION, "declaration": "ErdosProblems.Synthetic.citing_result",
                "label": "res:synthetic"}
    exemptions = {"schema": check.EXEMPTION_SCHEMA, "exemptions": [HELPER_EXEMPTION, no_label]}
    report = evaluate(short_ledger(text), {SHORT_PAPER: text}, exemptions=exemptions)
    require(any("is stale" in problem for problem in report.docstrings.problems),
            "(d) kept an exemption for a docstring that no longer leads with a label")


def test_clause_e_pending_exact_rows_need_a_queue_date() -> None:
    text = paper(STATEMENT, NOTE)
    pending = {"status": "pending"}
    ledger = short_ledger(text, comparator=pending)
    ledger["rows"][0]["palomar"] = {"status": "pending"}
    ledger["content_digest"] = check.content_digest(ledger)
    report = evaluate(ledger, {SHORT_PAPER: text})
    require(len(report.e) == 1 and not report.queued, "(e) accepted a pending row with no date")

    for date, accepted in (("2026-09-23", True), ("2026-13-40", False), ("soon", False)):
        dated = copy.deepcopy(ledger)
        dated["rows"][0]["comparator"]["queued_at"] = date
        dated["content_digest"] = check.content_digest(dated)
        report = evaluate(dated, {SHORT_PAPER: text})
        require((not report.e and len(report.queued) == 1) == accepted,
                f"(e) mishandled queued_at {date!r}")


def test_integrity_rejects_unstamped_edits_and_invalid_statuses() -> None:
    text = paper(STATEMENT, NOTE)
    ledger = short_ledger(text)
    edited = copy.deepcopy(ledger)
    edited["rows"][0]["lean"]["status"] = "exact_or_stronger"
    require(any("content_digest" in failure for failure in check.ledger_integrity_failures(edited)),
            "an edit without restamping passed")

    invalid = {
        "modulo row queued": ("modulo_named_input", {"status": "pending", "queued_at": "2026-09-23"}),
        "exact row not applicable": ("exact", {"status": "not_applicable"}),
        "compared without receipts": ("exact", {"status": "compared"}),
    }
    for case, (status, comparator) in invalid.items():
        bad = short_ledger(text, status=status, comparator=comparator)
        require(check.ledger_integrity_failures(bad), f"integrity accepted a {case}")
    prepared = short_ledger(text, comparator={"status": "pending", "queued_at": "2026-09-23"})
    require(any("prepared requires" in failure for failure in check.ledger_integrity_failures(prepared)),
            "integrity accepted Palomar prepared for a row Comparator has not compared")
    none_with_names = short_ledger(text, status="none")
    require(check.ledger_integrity_failures(none_with_names), "a none row may not name declarations")


def test_currency_detects_changed_moved_and_unrecorded_statements() -> None:
    text = paper(STATEMENT)
    ledger = short_ledger(text)

    changed = text.replace("Every synthetic", "Every altered synthetic")
    report = evaluate(ledger, {SHORT_PAPER: changed, **evidence_texts()})
    require(any("no longer in" in failure for failure in report.currency),
            "a changed statement kept its row")

    moved = "\n\n" + text
    report = evaluate(ledger, {SHORT_PAPER: moved, **evidence_texts()})
    require(report.drift and report.failed(), "a moved statement kept its recorded line")
    currency, _texts = check.locate_rows(ledger, lambda path: moved)
    report = evaluate(check.restamped(ledger, currency.drift), {SHORT_PAPER: moved, **evidence_texts()})
    require(not report.failed(), f"--restamp did not repair a moved line: {check.summary_line(report)}")

    added = text + "\\begin{theorem}\\label{res:new}\nA new statement.\n\\end{theorem}\n"
    report = evaluate(ledger, {SHORT_PAPER: added})
    require(any("without a ledger row" in failure for failure in report.currency),
            "a new asserting environment passed without a row")


def test_baseline_only_shrinks() -> None:
    unlinked = paper(STATEMENT)
    ledger = short_ledger(unlinked)
    key = ("synthetic-short#res:synthetic", "b", FULL)
    entry = {"row": key[0], "clause": "b", "names": [FULL],
             "reason": "Proved before the note was regenerated from the ledger."}
    baseline = {"schema": check.BASELINE_SCHEMA, "entries": [entry]}

    report = evaluate(ledger, {SHORT_PAPER: unlinked}, baseline=baseline, introduced=frozenset({key}))
    require(not report.failed() and len(report.b_held) == 1, "a baselined failure was not held")

    report = evaluate(ledger, {SHORT_PAPER: unlinked}, baseline=baseline)
    require(any("not failing when the check was introduced" in p for p in report.baseline_problems),
            "the baseline accepted an entry outside the introduced debt")

    linked = paper(STATEMENT, NOTE)
    report = evaluate(short_ledger(linked), {SHORT_PAPER: linked}, baseline=baseline,
                      introduced=frozenset({key}))
    require(any("is stale" in p for p in report.baseline_problems),
            "a repaired row kept its baseline entry")

    for case, bad in (("clause a", {**entry, "clause": "a"}), ("short reason", {**entry, "reason": "x"})):
        report = evaluate(ledger, {SHORT_PAPER: unlinked}, introduced=frozenset({key}),
                          baseline={"schema": check.BASELINE_SCHEMA, "entries": [bad]})
        require(report.failed(), f"the baseline accepted an entry with a {case}")


def test_introduced_debt_matches_the_committed_baseline() -> None:
    baseline = check.read_json(check.BASELINE)
    listed = {
        (entry["row"], entry["clause"], name)
        for entry in baseline["entries"] for name in entry["names"]
    }
    require(listed <= check.INTRODUCED_DEBT, "the committed baseline lists debt it was not introduced with")


def test_clause_a_reads_only_tracked_lean_files_of_a_separately_built_library() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        library = root / "verification" / "Cert"
        (library / "Sub").mkdir(parents=True)
        for relative in ("verification/Cert/Sub/Tracked.lean", "verification/Cert/Sub/Untracked.lean",
                         "verification/Other.lean", "verification/Cert/notes.md"):
            (root / relative).write_text("theorem t : True := trivial\n", encoding="utf-8")
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        subprocess.run(["git", "-C", str(root), "add", "verification/Cert/Sub/Tracked.lean",
                        "verification/Other.lean", "verification/Cert/notes.md"], check=True)
        found = check.checked_library_sources(root, ("verification/Cert",))
        require(found == {"verification/Cert/Sub/Tracked.lean"},
                f"only tracked Lean files of the library may count: {sorted(found)}")
    # The #251 large certificate is such a library; its theorem resolves in this checkout.
    problem = check.LeanSources().declaration_problem(
        "verification/Erdos251LargeCertificate/ErdosProblems/Erdos251/PaperLargeCertificateR7.lean",
        "ErdosProblems.Erdos251.PaperR7.LargeCertificate.denominator_floor_both",
    )
    require(problem is None, f"the #251 certificate theorem does not resolve: {problem}")


def main() -> int:
    tests = [
        test_repaired_fixture_passes,
        test_clause_a_missing_renamed_alias_and_untracked_declarations_fail,
        test_clause_b_fails_until_every_declaration_is_rendered,
        test_margin_marks_link_only_what_the_paper_declares,
        test_retired_notes_and_concordances_fail,
        test_clause_b_note_count_covers_the_rest_only_when_exact,
        test_clause_b_reads_the_concordance_of_a_long_record,
        test_clause_c_flags_stale_generated_links_and_spares_author_citations,
        test_clause_d_label_docstrings_need_a_row_or_a_reasoned_exemption,
        test_clause_e_pending_exact_rows_need_a_queue_date,
        test_integrity_rejects_unstamped_edits_and_invalid_statuses,
        test_currency_detects_changed_moved_and_unrecorded_statements,
        test_baseline_only_shrinks,
        test_introduced_debt_matches_the_committed_baseline,
        test_clause_a_reads_only_tracked_lean_files_of_a_separately_built_library,
    ]
    for test in tests:
        test()
    print(
        f"test_check_lean_paper_propagation: {len(tests)} fixtures; clauses (a) to (e), ledger "
        "integrity, currency and the shrink-only baseline each fail when broken"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
