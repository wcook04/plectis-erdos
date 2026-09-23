#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Require every Lean proof of a paper statement to reach its papers and the Comparator queue.

``docs/paper_lean_coverage.json`` has one row per asserting environment of the
sixteen problem papers, short and long counted separately.  A row names the
Lean declarations that state the environment (``lean``), and how far the row
has travelled toward an independent Comparator replay (``comparator``) and a
prepare-only Palomar entry (``palomar``).  This program fails when a Lean
result has not propagated:

  (a) a row names a declaration that its Git-tracked file in this checkout
      does not declare, exactly once, under that full name.  The file is a
      corpus source under ``lean/`` or a source of one of the separately built
      libraries in ``CHECKED_LIBRARY_DIRS``;
  (b) a row with Lean declarations whose environment carries no rendered link
      naming each of them.  Rendered links are the ``\\leannote`` printed after
      the environment, the row's entry in the generated concordance of a long
      record, and links inside the environment (``\\lean``, ``\\lproof``,
      ``\\lref``, ``\\lrefx``, ``\\lword``, ``\\mref``, ``\\mword`` and pinned
      ``\\href`` links to a Lean file).  A note that lists some declarations
      and counts the rest ("and N further declarations") covers the counted
      ones only while its count is exact;
  (c) a generated link (the note after an environment, or the environment's
      concordance entry) names a declaration the ledger does not bind to that
      environment: a stale or orphaned link after a rename or a new proof.
      Links an author writes inside a statement may cite supporting
      declarations; ``check_problem_note_sources.py`` verifies those at their
      pins;
  (d) a Lean declaration whose docstring leads with a paper label in
      backticks, optionally bold (the convention for "this declaration states
      that paper result"), is neither in the ledger nor exempted, with a
      reason, in ``docs/paper_lean_docstring_exemptions.json``;
  (e) a row with exact Lean evidence still pending Comparator has no
      ``queued_at`` date.  Those rows are printed as the Comparator and
      Palomar worklist.

It also fails when the ledger no longer describes the papers: a content digest
that does not match, an invalid status, a row whose statement is no longer in
its paper, a row recorded at the wrong line, or an asserting environment
without a row.

Known debt present when the check was introduced is listed row by row in
``docs/paper_lean_propagation_baseline.json``.  A (b) or (c) failure outside
that list fails, a listed failure that has been repaired fails until its entry
is removed, and an entry outside the set this program was introduced with is
refused, so the list only shrinks.

Run from the repository root:

    python3 scripts/check_lean_paper_propagation.py
    python3 scripts/check_lean_paper_propagation.py --json
    python3 scripts/check_lean_paper_propagation.py --restamp

``--restamp`` rewrites the recorded source line of every row whose statement
moved within its file, then the content digest; run it after a deliberate row
edit.  It never changes a status or a declaration.  Stdlib only.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Iterable

from check_problem_note_sources import (
    LINK_RE,
    LPROOF_RE,
    UnsafeSourceInput,
    safe_worktree_text,
    strip_comments,
    strip_unrendered,
)
from lean_source import (
    LIBRARY_ROOTS,
    LeanDeclarationError,
    declaration_line,
    library_identity_path,
    library_source_paths,
    qualified_declaration_lines,
)

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "docs" / "paper_lean_coverage.json"
BASELINE = ROOT / "docs" / "paper_lean_propagation_baseline.json"
EXEMPTIONS = ROOT / "docs" / "paper_lean_docstring_exemptions.json"

LEDGER_SCHEMA = "plectis-paper-lean-coverage/1"
BASELINE_SCHEMA = "plectis-paper-lean-propagation-baseline/1"
EXEMPTION_SCHEMA = "plectis-paper-lean-docstring-exemptions/1"

# Lean libraries outside the two corpus roots whose declarations a row may
# bind.  Each is a Lake library of its own that CI builds and kernel-checks by
# name (lakefile.toml); the #251 large certificate is kept out of the default
# build this way.
CHECKED_LIBRARY_DIRS = ("verification/Erdos251LargeCertificate",)

EXACT = ("exact", "exact_or_stronger")
LEAN_STATUSES = (*EXACT, "modulo_named_input", "none")
COMPARATOR_STATUSES = ("compared", "pending", "not_applicable")
PALOMAR_STATUSES = ("prepared", "pending", "not_applicable")
SIDES = ("short", "long")
BASELINE_CLAUSES = ("b", "c")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
MIN_REASON_WORDS = 6

# The (row, clause, name) failures present when this check was introduced on
# 23 September 2026.  The baseline may list only these, so it can shrink and
# never grow: a new failure is repaired in the change that causes it.
INTRODUCED_DEBT = frozenset({
    ("erdos-1041-lemniscate-newton-flow#res:one-root-gamma-false", "b",
     "ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false_unconditional"),
    ("erdos1049-rational-base-lambert-reasoning-surface#long1049:res:nomahler", "b",
     "ErdosProblems.Erdos1049.PaperCompleteR21.no_finite_simultaneous_two_three_system_unconditional"),
    ("erdos249-totient-reasoning-surface#prop:dickman", "b",
     "ErdosProblems.Erdos249.PaperCompleteR21.prop_dickman"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-i16", "b",
     "ErdosProblems.Erdos257.PaperCompleteR21.paper_reverse_carry_word"),
    ("erdos-1041-lemniscate-newton-flow#res:one-root-gamma-false", "c",
     "ErdosProblems/Erdos1041/PaperCompleteR21/LobeAndArity.lean::lobe_nhd_of_closed_disc"),
    ("erdos-1041-lemniscate-newton-flow#res:one-root-gamma-false", "c",
     "ErdosProblems/Erdos1041/PaperCompleteR21/LobeAndArity.lean::lobe_perimeter_gt"),
    ("erdos-1041-lemniscate-newton-flow#res:one-root-gamma-false", "c",
     "ErdosProblems/Erdos1041/PaperCompleteR21/LobeAndArity.lean::lobe_unique_zero"),
    ("erdos-1041-lemniscate-newton-flow#res:one-root-gamma-false", "c",
     "ErdosProblems/Erdos1041/PaperCompleteR21/LobeAndArity.lean::one_root_gamma_false"),
    ("erdos1041-lemniscate-reasoning-surface#res:ani-degree-seven-counterexample-long", "c",
     "ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean::erdos1041_ani_degree_seven"),
    ("erdos1049-rational-base-lambert-reasoning-surface#long1049:res:nomahler", "c",
     "ErdosProblems/Erdos1049/PaperCompleteR21/SimultaneousMahlerSystem.lean::divisorLambert_subs_not_rational"),
    ("erdos1049-rational-base-lambert-reasoning-surface#long1049:res:nomahler", "c",
     "ErdosProblems/Erdos1049/PaperCompleteR21/SimultaneousMahlerSystem.lean::isMahler_subs"),
    ("erdos1049-rational-base-lambert-reasoning-surface#long1049:res:nomahler", "c",
     "ErdosProblems/Erdos1049/PaperCompleteR21/SimultaneousMahlerSystem.lean::mahler_of_stable"),
    ("erdos1049-rational-base-lambert-reasoning-surface#long1049:res:nomahler", "c",
     "ErdosProblems/Erdos1049/PaperCompleteR21/SimultaneousMahlerSystem.lean::no_finite_simultaneous_two_three_system"),
    ("erdos249-totient-reasoning-surface#prop:SEP-03", "c",
     "ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean::prescribedOddIndex"),
    ("erdos257-mersenne-reasoning-surface#prop:local-void", "c",
     "Erdos249257/TropicalCurvatureCarry.lean::fixedPrecisionTropicalNoGo"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-c1", "c",
     "Erdos249257/BooleanMobiusCofinalExactRows.lean::CofinalExactLocalMersenneHalfRows"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-c14", "c",
     "Erdos249257/HalfCylinderFullShellSeamBridge.lean::HalfGreedySkippedFullShellNonnegative"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-c14", "c",
     "Erdos249257/HalfCylinderFullShellSeamBridge.lean::HalfGreedySkippedSeamAlignmentZero"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-c2", "c",
     "Erdos249257/BooleanMobiusSkipRowCofinal.lean::CofinalPositiveHalfGreedySkips"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-c4", "c",
     "Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean::SkippedCoreCriticalQuotientSupply"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-c6", "c",
     "Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean::HalfGreedySkippedCriticalQuotientSupply"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-i-cross2", "c",
     "Erdos249257/BooleanMobiusExactRowCrossing.lean::localMersenneCrossingRanks"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-i-t7", "c",
     "Erdos249257/GenericTailOrbitRigidity.lean::IsTemperedBinaryOrbit"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-i-t7", "c",
     "Erdos249257/GenericTailOrbitRigidity.lean::binaryCoeffSeries"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-i12", "c",
     "Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean::localMersenneGeometricQuotient"),
    ("erdos257-mersenne-reasoning-surface#record:257bm-i16", "c",
     "Erdos249257/HalfTrappingReturnCarry.lean::ReverseCarryWord"),
    ("erdos257-mersenne-reasoning-surface#record:257rig-c18", "c",
     "Erdos249257/CofinalStripReturn.lean::GreedyHalfCarryCofinalStripReturn"),
    ("erdos257-mersenne-reasoning-surface#record:257rig-i4b", "c",
     "Erdos249257/SublogDivisorCoverage.lean::divisorSubpowerConst"),
    ("erdos257-mersenne-reasoning-surface#thm:one-sided", "c",
     "ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean::computablePred_halfFatalCertificateCode"),
    ("erdos257-mersenne-reasoning-surface#thm:one-sided", "c",
     "ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean::finite_depth_survival_not_sufficient"),
    ("erdos257-mersenne-reasoning-surface#thm:one-sided", "c",
     "ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean::half_mem_iff_forall_not_halfFatalCertificateCode"),
    ("erdos257-mersenne-reasoning-surface#thm:one-sided", "c",
     "ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean::half_not_mem_iff_exists_halfFatalCertificateCode"),
    ("erdos269-running-lcm-reasoning-surface#long269:res:dyadic-alphabet", "c",
     "ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean::dyadicBlockBase235"),
})

# --- The statement inventory ------------------------------------------------
# The ledger's digests are the maintainer count's digests, so the inventory is
# reproduced exactly: TeX comments are removed with this pattern (lines are
# kept), and a statement is the text between its opening \begin{...}[title]
# and the matching \end{...}.
COUNTER_COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")
BEGIN_RE = re.compile(r"\\begin\{([^{}]+)\}(?:\[([^\]]*)\])?")
NEWTHEOREM_RE = re.compile(r"\\newtheorem\*?\{([^{}]+)\}(?:\[[^\]]*\])?\{([^{}]+)\}")
LABEL_RE = re.compile(r"\\(?:label|leanlabel)\{([^{}]+)\}")
BASE_KINDS = {
    **{name: name for name in (
        "theorem", "lemma", "proposition", "corollary", "claim", "fact",
        "conjecture", "problem", "question",
    )},
    "thm": "theorem", "lem": "lemma", "prop": "proposition", "cor": "corollary",
}
QUESTION_KINDS = {"problem", "question", "conjecture"}

# --- Rendered links -----------------------------------------------------------
LEAN_MACRO_RE = re.compile(r"\\lean\{(?P<name>[^{}]+)\}\{(?P<coord>[^{}]+)\}")
PINNED_NAME_RE = re.compile(
    r"\\href\{https://github\.com/wcook04/plectis-erdos/blob/[0-9a-f]{40}/"
    r"(?P<path>[^\s{}#\\]+\.lean)\\?#L[0-9]+(?:-L?[0-9]+)?\}"
    r"\{\\(?:texttt|nolinkurl|mathtt|leanlabel)\{(?P<name>[^{}]+)\}\}"
)
NOTE_OPEN = "\\leannote{"
OVERFLOW_RE = re.compile(r"and (\d+) further declarations?")
CONCORDANCE_BEGIN = "% BEGIN GENERATED CONCORDANCE"
CONCORDANCE_END = "% END GENERATED CONCORDANCE"
CONCORDANCE_REF_RE = re.compile(r"\\ref\{([^{}]+)\}")
PX_DEF_RE = re.compile(r"\\(re)?newcommand\{\\PX\}\{([^{}]+)\}")
PK_DEF_RE = re.compile(r"\\(?:re)?newcommand\{\\PK\}\{([^{}]+)\}")

# --- Docstrings ---------------------------------------------------------------
LABEL_SHAPE = r"(?:long\d+:)?[a-z]+:[A-Za-z0-9_.:+\-]+"
LEADING_LABEL_RE = re.compile(r"/--\s*(?:\*\*)?\s*`\s*(" + LABEL_SHAPE + r")\s*`")


class LedgerFormatError(ValueError):
    """The ledger, baseline or exemption file is not in its registered shape."""


# =============================================================================
# Small readers
# =============================================================================


def read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(safe_worktree_text(path))
    except (UnsafeSourceInput, json.JSONDecodeError) as error:
        raise LedgerFormatError(f"{path.relative_to(ROOT)}: {error}") from error
    if not isinstance(value, dict):
        raise LedgerFormatError(f"{path.relative_to(ROOT)}: not a JSON object")
    return value


def read_repository_text(relative: str) -> str:
    return safe_worktree_text(ROOT / relative)


def canonical(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")


def content_digest(document: dict[str, Any]) -> str:
    """sha256 of the canonical ledger with its own digest field removed."""
    body = {key: value for key, value in document.items() if key != "content_digest"}
    return "sha256:" + hashlib.sha256(canonical(body)).hexdigest()


def split_source(source: str) -> tuple[str, int]:
    path, _, line = source.rpartition(":")
    if not path or not line.isdigit():
        raise LedgerFormatError(f"source {source!r} is not path:line")
    return path, int(line)


def row_label(row: dict[str, Any]) -> str:
    return f"{row.get('id')} ({row.get('source')})"


def declarations_of(row: dict[str, Any]) -> list[dict[str, Any]]:
    return (row.get("lean") or {}).get("declarations") or []


# =============================================================================
# Ledger integrity
# =============================================================================


def ledger_integrity_failures(ledger: dict[str, Any]) -> list[str]:
    """Structural failures: schema, digest, statuses and their combinations."""
    failures: list[str] = []
    if ledger.get("schema") != LEDGER_SCHEMA:
        failures.append(f"ledger schema is {ledger.get('schema')!r}, expected {LEDGER_SCHEMA!r}")
    if not COMMIT_RE.match(str(ledger.get("lean_pin", ""))):
        failures.append("ledger lean_pin is not a 40-hex commit")
    if ledger.get("content_digest") != content_digest(ledger):
        failures.append(
            "ledger content_digest does not match its content: it was edited without "
            "restamping (run --restamp after a deliberate edit, or regenerate it)"
        )
    papers = ledger.get("papers")
    rows = ledger.get("rows")
    if not isinstance(papers, list) or not isinstance(rows, list):
        return failures + ["ledger papers and rows must be lists"]
    paper_ids = set()
    for paper in papers:
        if not isinstance(paper, dict) or not isinstance(paper.get("sources"), list):
            failures.append(f"ledger paper entry {paper!r} has no sources list")
            continue
        paper_ids.add(paper.get("paper_id"))
    seen: set[str] = set()
    for row in rows:
        if not isinstance(row, dict):
            failures.append(f"ledger row {row!r} is not an object")
            continue
        failures.extend(row_integrity_failures(row, paper_ids, seen))
    return failures


def row_integrity_failures(
    row: dict[str, Any], paper_ids: set[Any], seen: set[str]
) -> list[str]:
    failures: list[str] = []
    name = row_label(row)
    row_id = row.get("id")
    if not isinstance(row_id, str) or not row_id:
        return [f"ledger row {row!r} has no id"]
    if row_id in seen:
        failures.append(f"ledger row id {row_id} is repeated")
    seen.add(row_id)
    if row.get("paper_id") not in paper_ids:
        failures.append(f"{name}: paper {row.get('paper_id')!r} is not in the ledger's papers")
    if row.get("side") not in SIDES:
        failures.append(f"{name}: side {row.get('side')!r} is not short or long")
    if not re.fullmatch(r"sha256:[0-9a-f]{64}", str(row.get("statement_sha256", ""))):
        failures.append(f"{name}: statement_sha256 is not a sha256 digest")
    try:
        path, _line = split_source(str(row.get("source", "")))
        if not path.startswith("paper/"):
            failures.append(f"{name}: source is not a paper file")
    except LedgerFormatError as error:
        failures.append(f"{name}: {error}")
    lean = row.get("lean")
    comparator = row.get("comparator")
    palomar = row.get("palomar")
    if not all(isinstance(block, dict) for block in (lean, comparator, palomar)):
        return failures + [f"{name}: lean, comparator and palomar must be objects"]
    status = lean.get("status")
    if status not in LEAN_STATUSES:
        return failures + [f"{name}: lean status {status!r} is not one of {LEAN_STATUSES}"]
    if comparator.get("status") not in COMPARATOR_STATUSES:
        failures.append(f"{name}: comparator status {comparator.get('status')!r} is invalid")
    if palomar.get("status") not in PALOMAR_STATUSES:
        failures.append(f"{name}: palomar status {palomar.get('status')!r} is invalid")
    declarations = lean.get("declarations")
    if not isinstance(declarations, list):
        return failures + [f"{name}: lean declarations must be a list"]
    for declaration in declarations:
        if not (
            isinstance(declaration, dict)
            and isinstance(declaration.get("name"), str)
            and isinstance(declaration.get("file"), str)
            and declaration["file"].endswith(".lean")
        ):
            failures.append(f"{name}: declaration {declaration!r} needs a name and a .lean file")
    if status == "none" and declarations:
        failures.append(f"{name}: lean status none names declarations")
    if status != "none" and not declarations:
        failures.append(f"{name}: lean status {status} names no declaration")
    if status == "modulo_named_input" and not isinstance(lean.get("named_inputs"), list):
        failures.append(f"{name}: a modulo_named_input row needs a named_inputs list")
    if status in EXACT:
        if comparator.get("status") not in ("compared", "pending"):
            failures.append(f"{name}: exact Lean evidence needs comparator compared or pending")
        if comparator.get("status") == "compared":
            for key in ("entries", "run_ids", "corpus_commits"):
                if not comparator.get(key):
                    failures.append(f"{name}: a compared row needs comparator {key}")
            for commit in comparator.get("corpus_commits") or []:
                if not COMMIT_RE.match(str(commit)):
                    failures.append(f"{name}: corpus commit {commit!r} is not 40-hex")
        if palomar.get("status") == "prepared" and comparator.get("status") != "compared":
            failures.append(f"{name}: palomar prepared requires comparator compared")
        if comparator.get("status") == "pending" and palomar.get("status") != "pending":
            failures.append(f"{name}: a row pending Comparator is pending Palomar too")
    else:
        if comparator.get("status") != "not_applicable":
            failures.append(f"{name}: comparator must be not_applicable without exact Lean evidence")
        if palomar.get("status") != "not_applicable":
            failures.append(f"{name}: palomar must be not_applicable without exact Lean evidence")
    return failures


# =============================================================================
# Statement inventory and row location
# =============================================================================


def counter_view(text: str) -> str:
    return COUNTER_COMMENT_RE.sub("", text)


def theorem_kinds(texts: Iterable[str]) -> dict[str, str]:
    kinds = dict(BASE_KINDS)
    for name, title in NEWTHEOREM_RE.findall("\n".join(texts)):
        kind = title.strip().lower()
        if kind in kinds:
            kinds[name] = kinds[kind]
    return kinds


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def inventory(
    sources: list[tuple[str, str]], spans: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    """Every closed asserting environment and registered claim span of one paper.

    ``sources`` are (path, raw text) pairs; ``spans`` name a labelled claim span
    by its label and its opening and closing phrases.
    """
    views = [(path, counter_view(text)) for path, text in sources]
    kinds = theorem_kinds(view for _path, view in views)
    found: list[dict[str, Any]] = []
    for path, text in views:
        for start in BEGIN_RE.finditer(text):
            environment = start.group(1)
            kind = kinds.get(environment.rstrip("*"))
            if kind is None or kind in QUESTION_KINDS:
                continue
            end = text.find("\\end{" + environment + "}", start.end())
            if end < 0:
                continue
            body = text[start.end():end]
            found.append({
                "path": path,
                "line": line_of(text, start.start()),
                "end_line": line_of(text, end),
                "environment": environment,
                "labels": LABEL_RE.findall(body),
                "statement_sha256": "sha256:" + hashlib.sha256(body.encode()).hexdigest(),
            })
        for span in spans:
            label, opening, closing = span["label"], span["start"], span["end"]
            at = text.find("\\label{" + label + "}")
            if at < 0 or not opening or not closing:
                continue
            start = text.find(opening, at)
            finish = text.find(closing, start if start >= 0 else at)
            if start < 0 or finish < start:
                continue
            body = text[start:finish + len(closing)]
            found.append({
                "path": path,
                "line": line_of(text, start),
                "end_line": line_of(text, finish + len(closing)),
                "environment": None,
                "labels": [label],
                "statement_sha256": "sha256:" + hashlib.sha256(body.encode()).hexdigest(),
            })
    return found


@dataclass
class Located:
    row: dict[str, Any]
    path: str
    line: int
    end_line: int


@dataclass
class Currency:
    located: dict[str, Located] = field(default_factory=dict)
    missing: list[str] = field(default_factory=list)
    drift: list[tuple[str, str, int]] = field(default_factory=list)
    unrowed: list[str] = field(default_factory=list)


def span_specs(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    specs = []
    for row in rows:
        span = row.get("span")
        if row.get("environment") is None and isinstance(span, dict) and row.get("label"):
            specs.append({"label": row["label"], "start": span.get("start") or "",
                          "end": span.get("end") or ""})
    return specs


def locate_rows(
    ledger: dict[str, Any], read: Callable[[str], str]
) -> tuple[Currency, dict[str, str]]:
    """Find every row's statement in its paper, and every statement's row."""
    currency = Currency()
    texts: dict[str, str] = {}
    rows_by_paper: dict[Any, list[dict[str, Any]]] = {}
    for row in ledger.get("rows", []):
        rows_by_paper.setdefault(row.get("paper_id"), []).append(row)
    for paper in ledger.get("papers", []):
        paper_rows = rows_by_paper.get(paper.get("paper_id"), [])
        sources: list[tuple[str, str]] = []
        for path in paper.get("sources", []):
            try:
                texts[path] = read(path)
            except (OSError, UnsafeSourceInput) as error:
                currency.missing.append(f"{paper.get('paper_id')}: source {path} unreadable: {error}")
                continue
            sources.append((path, texts[path]))
        found = inventory(sources, span_specs(paper_rows))
        by_key: dict[tuple[str, str], list[dict[str, Any]]] = {}
        for statement in found:
            by_key.setdefault((statement["path"], statement["statement_sha256"]), []).append(statement)
        claimed: set[tuple[str, int]] = set()
        for row in paper_rows:
            try:
                path, line = split_source(str(row.get("source", "")))
            except LedgerFormatError:
                continue
            candidates = by_key.get((path, row.get("statement_sha256")), [])
            match = next((s for s in candidates if s["line"] == line), None)
            if match is None and len(candidates) == 1:
                match = candidates[0]
                currency.drift.append((row["id"], row["source"], match["line"]))
            if match is None:
                currency.missing.append(
                    f"{row_label(row)}: the statement with this digest is no longer in {path}; "
                    "the paper changed after the ledger was written (recount, then regenerate)"
                )
                continue
            claimed.add((match["path"], match["line"]))
            currency.located[row["id"]] = Located(row, match["path"], match["line"], match["end_line"])
        for statement in found:
            if (statement["path"], statement["line"]) not in claimed:
                label = (statement["labels"] or ["unlabelled"])[0]
                currency.unrowed.append(
                    f"{statement['path']}:{statement['line']} {label}: asserting environment "
                    "without a ledger row (regenerate the ledger)"
                )
    return currency, texts


# =============================================================================
# Rendered links
# =============================================================================


@dataclass(frozen=True)
class Link:
    name: str
    path: str | None
    origin: str  # inline | note | concordance


def normalise_name(raw: str) -> str:
    name = raw.replace("\\allowbreak", "").replace("\\-", "").replace("{}", "")
    name = name.replace("\\_", "_")
    return re.sub(r"\s+", "", name)


def identity(path: str | None) -> str | None:
    if not path:
        return None
    return library_identity_path(path.strip().lstrip("/"))


def prefix_definitions(texts: Iterable[str]) -> tuple[str, str | None]:
    """The \\PX and \\PK prefixes one paper's sources establish."""
    px, renewed, pk = "ErdosProblems", False, None
    for text in texts:
        view = strip_comments(text)
        for renew, value in PX_DEF_RE.findall(view):
            if renew or not renewed:
                px, renewed = value, renewed or bool(renew)
        for value in PK_DEF_RE.findall(view):
            pk = value
    return px, pk


def lean_coordinate(coord: str, pk: str | None) -> str | None:
    """The file a \\lean{name}{file:line} coordinate links to, as its macro does."""
    cleaned = re.sub(r"\\allowbreak|\s+", "", coord)
    match = re.match(r"(.*?\.lean)", cleaned)
    if match is None:
        return None
    path = match.group(1)
    if path.startswith("lean/") or path.split("/", 1)[0] in LIBRARY_ROOTS:
        return path
    return f"{pk or 'Erdos249257'}/{path}"


def named_links(text: str, origin: str, px: str, pk: str | None) -> list[Link]:
    """Every declaration that a rendered stretch of TeX names in a link."""
    view = strip_unrendered(strip_comments(text))
    found: list[Link] = []
    for match in LINK_RE.finditer(view):
        if match.group("word_file"):
            file_name, name = match.group("word_file"), match.group("word_decl")
        elif match.group("ref_file"):
            file_name, name = match.group("ref_file"), match.group("ref_decl")
        else:
            continue  # \lloc and \mloc print only a location
        macro = view[match.start():match.start() + 6]
        if macro.startswith("\\lrefx"):
            path = f"{pk}/{file_name}" if pk else None
        elif macro.startswith(("\\mword", "\\mref")):
            path = file_name
        else:
            path = f"{px}/{file_name}"
        found.append(Link(normalise_name(name), identity(path), origin))
    for match in LPROOF_RE.finditer(view):
        found.append(Link(normalise_name(match.group("decl")), identity(match.group("file")), origin))
    for match in LEAN_MACRO_RE.finditer(view):
        found.append(Link(
            normalise_name(match.group("name")),
            identity(lean_coordinate(match.group("coord"), pk)),
            origin,
        ))
    for match in PINNED_NAME_RE.finditer(view):
        found.append(Link(normalise_name(match.group("name")), identity(match.group("path")), origin))
    return found


def balanced_argument(text: str, opening: int) -> int:
    """Offset just past the brace that closes the group opened at ``opening``."""
    depth = 0
    index = opening
    while index < len(text):
        character = text[index]
        if character == "\\":
            index += 2
            continue
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    return len(text)


def note_after(lines: list[str], end_line: int) -> str | None:
    """The \\leannote printed immediately after the line that closes a statement."""
    index = end_line  # the 0-based index of the line after ``end_line``
    while index < len(lines) and not lines[index].strip():
        index += 1
    if index >= len(lines) or not lines[index].lstrip().startswith(NOTE_OPEN):
        return None
    rest = "\n".join(lines[index:index + 40])
    start = rest.find(NOTE_OPEN) + len(NOTE_OPEN) - 1
    return rest[: balanced_argument(rest, start)]


def concordance_entries(text: str, px: str, pk: str | None) -> dict[str, list[Link]]:
    """Label -> links of every entry of the generated concordance blocks in one file."""
    entries: dict[str, list[Link]] = {}
    position = 0
    while True:
        begin = text.find(CONCORDANCE_BEGIN, position)
        if begin < 0:
            return entries
        end = text.find(CONCORDANCE_END, begin)
        if end < 0:
            end = len(text)
        for chunk in text[begin:end].split("\\par\\noindent")[1:]:
            # An entry opens with the result's \ref; its links follow.
            first_link = chunk.find("\\href")
            head = chunk if first_link < 0 else chunk[:first_link]
            references = CONCORDANCE_REF_RE.findall(head)
            if references:
                entries.setdefault(references[0], []).extend(
                    named_links(chunk, "concordance", px, pk)
                )
        position = end + len(CONCORDANCE_END)


def matches(link: Link, declaration: dict[str, Any]) -> bool:
    """A link names a ledger declaration when its file and final name agree.

    A link that prints a file pins the location, and the final component of
    the written name picks the declaration there; the namespace an author
    writes in a ``\\lean`` annotation is never typeset, and is sometimes wrong.
    A link without a file must name the declaration or a suffix of its name.
    """
    full = declaration["name"]
    if link.path is not None:
        return (
            link.path == identity(declaration["file"])
            and link.name.rsplit(".", 1)[-1] == full.rsplit(".", 1)[-1]
        )
    return link.name == full or full.endswith("." + link.name)


@dataclass
class RowLinks:
    inline: list[Link]
    note: list[Link]
    note_text: str | None
    concordance: list[Link]


def row_links(
    located: Located,
    lines: list[str],
    concordance: dict[str, list[Link]],
    px: str,
    pk: str | None,
) -> RowLinks:
    body = "\n".join(lines[located.line - 1:located.end_line])
    note = note_after(lines, located.end_line)
    concorded: list[Link] = []
    for label in (located.row.get("label"), *located.row.get("other_labels", [])):
        if label:
            concorded.extend(concordance.get(label, []))
    return RowLinks(
        inline=named_links(body, "inline", px, pk),
        note=named_links(note, "note", px, pk) if note else [],
        note_text=note,
        concordance=concorded,
    )


def counted_by_note(row: dict[str, Any], links: RowLinks) -> bool:
    """True when the note names some declarations and counts exactly the rest.

    A generated note prints at most four names and then "and N further
    declarations"; the count is exact for the row it was generated from, so it
    covers the row only while the row still has that many declarations.
    """
    if not links.note_text:
        return False
    counted = OVERFLOW_RE.search(links.note_text)
    if counted is None:
        return False
    declarations = declarations_of(row)
    named = sum(
        1 for declaration in declarations
        if any(matches(link, declaration) for link in links.note)
    )
    return named + int(counted.group(1)) == len(declarations)


def unlinked_declarations(row: dict[str, Any], links: RowLinks) -> list[str]:
    """Clause (b): declarations no rendered link names and no exact note count covers."""
    if counted_by_note(row, links):
        return []
    rendered = [*links.inline, *links.note, *links.concordance]
    return [
        declaration["name"]
        for declaration in declarations_of(row)
        if not any(matches(link, declaration) for link in rendered)
    ]


def orphan_links(row: dict[str, Any], links: RowLinks) -> list[str]:
    """Clause (c): generated links naming declarations the row does not bind."""
    orphans: list[str] = []
    for link in [*links.note, *links.concordance]:
        if not any(matches(link, declaration) for declaration in declarations_of(row)):
            rendered = f"{link.path}::{link.name}" if link.path else link.name
            if rendered not in orphans:
                orphans.append(rendered)
    return orphans


def describe(clause: str, names: list[str]) -> str:
    if clause == "b":
        return "no rendered link names " + ", ".join(names)
    return "a generated link names a declaration this row does not bind: " + ", ".join(names)


def propagation_failures(
    ledger: dict[str, Any], currency: Currency, texts: dict[str, str]
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], int]:
    """Clauses (b) and (c) over every located row, and the rows a note count covers."""
    b: list[dict[str, Any]] = []
    c: list[dict[str, Any]] = []
    by_count = 0
    prefixes: dict[Any, tuple[str, str | None]] = {}
    concordances: dict[Any, dict[str, list[Link]]] = {}
    for paper in ledger.get("papers", []):
        sources = paper.get("sources", [])
        px, pk = prefix_definitions(texts.get(path, "") for path in sources)
        prefixes[paper.get("paper_id")] = (px, pk)
        merged: dict[str, list[Link]] = {}
        for path in sources:
            for label, links in concordance_entries(texts.get(path, ""), px, pk).items():
                merged.setdefault(label, []).extend(links)
        concordances[paper.get("paper_id")] = merged
    lines_of: dict[str, list[str]] = {}
    for row_id, located in currency.located.items():
        row = located.row
        if located.path not in lines_of:
            lines_of[located.path] = counter_view(texts.get(located.path, "")).splitlines()
        px, pk = prefixes.get(row.get("paper_id"), ("ErdosProblems", None))
        links = row_links(located, lines_of[located.path], concordances.get(row.get("paper_id"), {}),
                          px, pk)
        where = f"{located.path}:{located.line}"
        if declarations_of(row):
            if counted_by_note(row, links):
                by_count += 1
            missing = unlinked_declarations(row, links)
            if missing:
                b.append({"clause": "b", "row": row_id, "source": where, "names": missing,
                          "detail": describe("b", missing)})
        orphans = orphan_links(row, links)
        if orphans:
            c.append({"clause": "c", "row": row_id, "source": where, "names": orphans,
                      "detail": describe("c", orphans)})
    return b, c, by_count


# =============================================================================
# Clause (a): declarations exist under their full names
# =============================================================================


def checked_library_sources(
    root: Path, directories: Iterable[str] = CHECKED_LIBRARY_DIRS
) -> set[str]:
    """Git-tracked ``.lean`` files of the separately built libraries a row may bind.

    Outside a Git worktree (a tarball or a test root) every ``.lean`` file on
    disk counts, as it does for the corpus roots.
    """
    found: set[str] = set()
    for directory in directories:
        base = root / directory
        if not base.is_dir():
            continue
        try:
            completed = subprocess.run(
                ["git", "-C", str(root), "ls-files", "-z", "--", directory],
                capture_output=True,
                check=False,
                timeout=60,
            )
        except FileNotFoundError:
            completed = None
        if completed is not None and completed.returncode == 0:
            found.update(
                name
                for name in completed.stdout.decode("utf-8").split("\0")
                if name.endswith(".lean")
            )
        else:
            found.update(path.relative_to(root).as_posix() for path in base.rglob("*.lean"))
    return found


class LeanSources:
    """Git-tracked Lean sources of this checkout, read on demand."""

    def __init__(self, root: Path = ROOT) -> None:
        self.root = root
        self._tracked: set[str] | None = None
        self._lines: dict[str, dict[str, list[int]] | None] = {}
        self._text: dict[str, str | None] = {}

    def tracked(self) -> set[str]:
        if self._tracked is None:
            self._tracked = {
                path.relative_to(self.root).as_posix() for path in library_source_paths(self.root)
            } | checked_library_sources(self.root)
        return self._tracked

    def text(self, relative: str) -> str | None:
        if relative not in self._text:
            self._text[relative] = None
            if relative in self.tracked():
                try:
                    self._text[relative] = safe_worktree_text(self.root / relative)
                except UnsafeSourceInput:
                    pass
        return self._text[relative]

    def qualified(self, relative: str) -> dict[str, list[int]] | None:
        if relative not in self._lines:
            text = self.text(relative)
            self._lines[relative] = None if text is None else qualified_declaration_lines(text)
        return self._lines[relative]

    def declaration_problem(self, relative: str, name: str) -> str | None:
        """None when ``relative`` declares ``name`` exactly once under that full name."""
        index = self.qualified(relative)
        if index is None:
            return f"{relative} is not a Git-tracked Lean library file in this checkout"
        lines = index.get(name)
        if lines is None:
            try:
                line = declaration_line(self.text(relative) or "", name)
            except LeanDeclarationError:
                return f"{name} is not declared in {relative}"
            full = next(key for key, found in index.items() if line in found)
            return f"{name} is not a full declaration name in {relative}; it is declared as {full}"
        if len(lines) != 1:
            return f"{name} is declared {len(lines)} times in {relative}"
        return None


def missing_declarations(
    ledger: dict[str, Any], problem: Callable[[str, str], str | None]
) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    for row in ledger.get("rows", []):
        for declaration in declarations_of(row):
            reason = problem(declaration["file"], declaration["name"])
            if reason:
                failures.append({"clause": "a", "row": row["id"], "source": row["source"],
                                 "detail": reason})
    return failures


# =============================================================================
# Clause (d): label-leading docstrings
# =============================================================================


def leading_label_declarations(relative: str, text: str) -> list[dict[str, Any]]:
    """Declarations whose docstring opens with a backticked paper label."""
    if "/--" not in text:
        return []
    hits = list(LEADING_LABEL_RE.finditer(text))
    if not hits:
        return []
    by_line: dict[int, str] = {}
    for name, lines in qualified_declaration_lines(text).items():
        for line in lines:
            by_line[line] = name
    source_lines = text.splitlines()
    found = []
    for hit in hits:
        close = text.find("-/", hit.end())
        if close < 0:
            continue
        # The documented declaration opens on the docstring's closing line or
        # after it, past blank lines and attribute lines; anything else means
        # the docstring documents no declaration.
        first = line_of(text, close + 2)
        line, name = first, None
        while line <= len(source_lines):
            name = by_line.get(line)
            if name is not None:
                break
            following = source_lines[line - 1].strip() if line > first else ""
            if following and not following.startswith("@["):
                break
            line += 1
        if name is not None:
            found.append({"declaration": name, "file": relative, "line": line,
                          "label": hit.group(1)})
    return found


def scan_docstrings(sources: LeanSources) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for relative in sorted(sources.tracked()):
        text = sources.text(relative)
        if text:
            hits.extend(leading_label_declarations(relative, text))
    return hits


def exemption_index(
    exemptions: dict[str, Any],
) -> tuple[dict[tuple[str, str], dict[str, Any]], list[str]]:
    problems: list[str] = []
    if exemptions.get("schema") != EXEMPTION_SCHEMA:
        problems.append(f"exemption schema is {exemptions.get('schema')!r}, expected {EXEMPTION_SCHEMA!r}")
    listed: dict[tuple[str, str], dict[str, Any]] = {}
    for entry in exemptions.get("exemptions", []):
        if not isinstance(entry, dict):
            problems.append(f"exemption {entry!r} is not an object")
            continue
        name, file_name = entry.get("declaration"), entry.get("file")
        if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z_][\w'.]*", name):
            problems.append(f"exemption {entry!r} must name one exact declaration (no patterns)")
            continue
        if not isinstance(file_name, str) or not file_name.endswith(".lean"):
            problems.append(f"exemption for {name} must name its .lean file")
            continue
        if not isinstance(entry.get("label"), str) or not re.fullmatch(LABEL_SHAPE, entry["label"]):
            problems.append(f"exemption for {name} must name the paper label its docstring leads with")
        reason = entry.get("reason")
        if not isinstance(reason, str) or len(reason.split()) < MIN_REASON_WORDS:
            problems.append(f"exemption for {name} needs a reason of at least {MIN_REASON_WORDS} words")
        if (name, file_name) in listed:
            problems.append(f"exemption for {name} is repeated")
        listed[(name, file_name)] = entry
    return listed, problems


@dataclass
class DocstringResult:
    failures: list[dict[str, Any]]
    problems: list[str]
    total: int
    bound: int
    exempt: int


def docstring_failures(
    hits: list[dict[str, Any]], ledger: dict[str, Any], exemptions: dict[str, Any]
) -> DocstringResult:
    bound = {
        (declaration["name"], declaration["file"])
        for row in ledger.get("rows", [])
        for declaration in declarations_of(row)
    }
    listed, problems = exemption_index(exemptions)
    current = {(hit["declaration"], hit["file"]): hit for hit in hits}
    result = DocstringResult([], problems, len(current), 0, 0)
    for key, hit in sorted(current.items()):
        if key in bound:
            result.bound += 1
        elif key in listed:
            result.exempt += 1
            if listed[key].get("label") != hit["label"]:
                problems.append(
                    f"exemption for {key[0]} names label {listed[key].get('label')} while the "
                    f"docstring now leads with {hit['label']}; update or remove it"
                )
        else:
            result.failures.append({
                "clause": "d", "row": None, "source": f"{hit['file']}:{hit['line']}",
                "detail": (f"{hit['declaration']} leads its docstring with `{hit['label']}` and is "
                           "in no ledger row and no exemption"),
            })
    for key in sorted(listed):
        if key in bound:
            problems.append(f"exemption for {key[0]} is stale: the ledger binds it now; remove it")
        elif key not in current:
            problems.append(
                f"exemption for {key[0]} is stale: {key[1]} declares no such declaration leading "
                "its docstring with a paper label; remove it"
            )
    return result


# =============================================================================
# Clause (e): the Comparator worklist
# =============================================================================


def worklist(ledger: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    queued: list[dict[str, Any]] = []
    failures: list[dict[str, Any]] = []
    for row in ledger.get("rows", []):
        lean, comparator = row.get("lean") or {}, row.get("comparator") or {}
        if lean.get("status") not in EXACT or comparator.get("status") != "pending":
            continue
        date = comparator.get("queued_at")
        valid = isinstance(date, str) and bool(DATE_RE.match(date))
        if valid:
            try:
                datetime.date.fromisoformat(date)
            except ValueError:
                valid = False
        if not valid:
            failures.append({"clause": "e", "row": row["id"], "source": row["source"],
                             "detail": "exact Lean evidence pending Comparator without a queued_at date"})
            continue
        queued.append({"row": row["id"], "source": row["source"], "queued_at": date,
                       "declarations": [d["name"] for d in declarations_of(row)]})
    return queued, failures


# =============================================================================
# The baseline ratchet
# =============================================================================


def apply_baseline(
    failures: list[dict[str, Any]],
    baseline: dict[str, Any],
    introduced: frozenset[tuple[str, str, str]] = INTRODUCED_DEBT,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[str]]:
    """Split (b) and (c) failures into new and baselined; name every problem entry."""
    problems: list[str] = []
    if baseline.get("schema") != BASELINE_SCHEMA:
        problems.append(f"baseline schema is {baseline.get('schema')!r}, expected {BASELINE_SCHEMA!r}")
    index: dict[tuple[str, str], set[str]] = {}
    for entry in baseline.get("entries", []):
        if not isinstance(entry, dict):
            problems.append(f"baseline entry {entry!r} is not an object")
            continue
        row, clause, names = entry.get("row"), entry.get("clause"), entry.get("names")
        if clause not in BASELINE_CLAUSES:
            problems.append(f"baseline entry for {row} has clause {clause!r}; only (b) and (c) "
                            "may be baselined")
            continue
        if not isinstance(names, list) or not names or not all(isinstance(n, str) for n in names):
            problems.append(f"baseline entry for {row} clause {clause} must list the failing names")
            continue
        reason = entry.get("reason")
        if not isinstance(reason, str) or len(reason.split()) < MIN_REASON_WORDS:
            problems.append(f"baseline entry for {row} clause {clause} needs a reason of at least "
                            f"{MIN_REASON_WORDS} words")
        if (row, clause) in index:
            problems.append(f"baseline entry for {row} clause {clause} is repeated")
        foreign = sorted(name for name in names if (row, clause, name) not in introduced)
        if foreign:
            problems.append(
                f"baseline entry for {row} clause {clause} lists {', '.join(foreign)}, which was "
                "not failing when the check was introduced; repair the link instead"
            )
        index[(row, clause)] = set(names)
    new: list[dict[str, Any]] = []
    held: list[dict[str, Any]] = []
    for failure in failures:
        key = (failure["row"], failure["clause"])
        listed = index.get(key, set())
        fresh = [name for name in failure["names"] if name not in listed]
        kept = [name for name in failure["names"] if name in listed]
        if fresh:
            new.append({**failure, "names": fresh, "detail": describe(failure["clause"], fresh)})
        if kept:
            held.append({**failure, "names": kept, "detail": describe(failure["clause"], kept)})
    failing = {(f["row"], f["clause"]): set(f["names"]) for f in failures}
    for key, listed in sorted(index.items(), key=lambda item: (str(item[0][0]), str(item[0][1]))):
        repaired = sorted(listed - failing.get(key, set()))
        if repaired:
            problems.append(
                f"baseline entry for {key[0]} clause {key[1]} is stale: {', '.join(repaired)} now "
                "pass; delete them from docs/paper_lean_propagation_baseline.json"
            )
    return new, held, problems


# =============================================================================
# Orchestration
# =============================================================================


@dataclass
class Report:
    rows: int = 0
    lean_counts: dict[str, int] = field(default_factory=dict)
    uncounted: int = 0
    integrity: list[str] = field(default_factory=list)
    currency: list[str] = field(default_factory=list)
    drift: list[tuple[str, str, int]] = field(default_factory=list)
    a: list[dict[str, Any]] = field(default_factory=list)
    b_new: list[dict[str, Any]] = field(default_factory=list)
    b_held: list[dict[str, Any]] = field(default_factory=list)
    c_new: list[dict[str, Any]] = field(default_factory=list)
    c_held: list[dict[str, Any]] = field(default_factory=list)
    baseline_problems: list[str] = field(default_factory=list)
    docstrings: DocstringResult = field(default_factory=lambda: DocstringResult([], [], 0, 0, 0))
    e: list[dict[str, Any]] = field(default_factory=list)
    queued: list[dict[str, Any]] = field(default_factory=list)
    linked_by_count: int = 0

    def failed(self) -> bool:
        return any((
            self.integrity, self.currency, self.drift, self.a, self.b_new, self.c_new,
            self.baseline_problems, self.docstrings.failures, self.docstrings.problems, self.e,
        ))


def evaluate(
    ledger: dict[str, Any],
    baseline: dict[str, Any],
    exemptions: dict[str, Any],
    read: Callable[[str], str],
    sources: LeanSources,
    introduced: frozenset[tuple[str, str, str]] = INTRODUCED_DEBT,
) -> Report:
    rows = ledger.get("rows", [])
    report = Report(rows=len(rows))
    for row in rows:
        lean = row.get("lean") if isinstance(row, dict) else None
        if isinstance(lean, dict):
            status = str(lean.get("status"))
            report.lean_counts[status] = report.lean_counts.get(status, 0) + 1
            report.uncounted += lean.get("counted") is False
    report.integrity = ledger_integrity_failures(ledger)
    if report.integrity and not isinstance(rows, list):
        return report
    currency, texts = locate_rows(ledger, read)
    report.currency = currency.missing + currency.unrowed
    report.drift = currency.drift
    report.a = missing_declarations(ledger, sources.declaration_problem)
    b, c, report.linked_by_count = propagation_failures(ledger, currency, texts)
    report.b_new, report.b_held, problems_b = apply_baseline(b, _clause(baseline, "b"), introduced)
    report.c_new, report.c_held, problems_c = apply_baseline(c, _clause(baseline, "c"), introduced)
    report.baseline_problems = sorted(set(problems_b + problems_c))
    report.docstrings = docstring_failures(scan_docstrings(sources), ledger, exemptions)
    report.queued, report.e = worklist(ledger)
    return report


def _clause(baseline: dict[str, Any], clause: str) -> dict[str, Any]:
    return {
        **baseline,
        "entries": [entry for entry in baseline.get("entries", [])
                    if not isinstance(entry, dict) or entry.get("clause") == clause],
    }


def summary_line(report: Report) -> str:
    verdict = "FAIL" if report.failed() else "PASS"
    exact = sum(report.lean_counts.get(status, 0) for status in EXACT)
    held_b = sum(len(item["names"]) for item in report.b_held)
    held_c = sum(len(item["names"]) for item in report.c_held)
    d = report.docstrings
    return (
        f"check_lean_paper_propagation: {verdict}; {report.rows} rows "
        f"({exact} exact, {report.lean_counts.get('modulo_named_input', 0)} modulo a named input, "
        f"{report.lean_counts.get('none', 0)} none, {report.uncounted} of them not yet counted); "
        f"(a) {len(report.a)} missing declaration(s); "
        f"(b) {len(report.b_new)} new unlinked row(s), {len(report.b_held)} baselined "
        f"({held_b} declaration(s)); "
        f"(c) {len(report.c_new)} new orphan-link row(s), {len(report.c_held)} baselined "
        f"({held_c} link(s)); "
        f"(d) {d.total} label docstring(s): {d.bound} in the ledger, {d.exempt} exempt, "
        f"{len(d.failures)} unrecorded; "
        f"(e) {len(report.queued)} queued for Comparator, {len(report.e)} unacknowledged; "
        f"currency {len(report.currency) + len(report.drift)}; "
        f"baseline/exemption problems {len(report.baseline_problems) + len(d.problems)}"
    )


def print_report(report: Report) -> None:
    for problem in report.integrity:
        print(f"  FAIL ledger: {problem}")
    for problem in report.currency:
        print(f"  FAIL currency: {problem}")
    for row_id, old, new in report.drift:
        print(f"  FAIL currency: {row_id} is recorded at {old} but opens at line {new} "
              "(run --restamp)")
    for failure in [*report.a, *report.b_new, *report.c_new, *report.docstrings.failures, *report.e]:
        row = f"{failure['row']} " if failure.get("row") else ""
        print(f"  FAIL ({failure['clause']}) {row}{failure['source']}: {failure['detail']}")
    for problem in report.baseline_problems:
        print(f"  FAIL baseline: {problem}")
    for problem in report.docstrings.problems:
        print(f"  FAIL exemptions: {problem}")
    if report.queued:
        print(f"  Comparator and Palomar worklist: {len(report.queued)} row(s) with exact Lean "
              "evidence awaiting replay")
        for item in report.queued:
            print(f"    queued {item['queued_at']}  {item['row']}  "
                  f"({len(item['declarations'])} declaration(s))")


def restamped(ledger: dict[str, Any], drift: list[tuple[str, str, int]]) -> dict[str, Any]:
    moved = {row_id: line for row_id, _old, line in drift}
    rows = []
    for row in ledger["rows"]:
        if row["id"] in moved:
            path, _line = split_source(row["source"])
            row = {**row, "source": f"{path}:{moved[row['id']]}"}
        rows.append(row)
    refreshed = {**ledger, "rows": rows}
    refreshed["content_digest"] = content_digest(refreshed)
    return refreshed


def report_json(report: Report) -> dict[str, Any]:
    return {
        "verdict": "fail" if report.failed() else "pass",
        "rows": report.rows,
        "lean": report.lean_counts,
        "not_yet_counted": report.uncounted,
        "integrity": report.integrity,
        "currency": report.currency,
        "drift": [{"row": r, "recorded": o, "line": n} for r, o, n in report.drift],
        "a": report.a,
        "b": report.b_new, "b_baselined": report.b_held,
        "c": report.c_new, "c_baselined": report.c_held,
        "baseline_problems": report.baseline_problems,
        "d": report.docstrings.failures,
        "d_counts": {"label_docstrings": report.docstrings.total,
                     "in_ledger": report.docstrings.bound, "exempt": report.docstrings.exempt},
        "exemption_problems": report.docstrings.problems,
        "e": report.e,
        "worklist": report.queued,
        "linked_by_exact_note_count": report.linked_by_count,
    }


def matching_rows(ledger: dict[str, Any], query: str) -> list[dict[str, Any]]:
    """Rows whose id, labels or declaration names contain ``query``."""
    found = []
    for row in ledger.get("rows", []):
        haystack = [str(row.get("id")), str(row.get("label")), *row.get("other_labels", [])]
        haystack.extend(declaration["name"] for declaration in declarations_of(row))
        if any(query in value for value in haystack):
            found.append(row)
    return found


def print_rows(rows: list[dict[str, Any]]) -> None:
    for row in rows:
        lean, comparator = row["lean"], row["comparator"]
        print(f"{row['id']}  {row['side']}  {row['source']}")
        print(f"  lean {lean['status']}; comparator {comparator['status']}"
              + (f" (queued {comparator['queued_at']})" if comparator.get("queued_at") else "")
              + f"; palomar {row['palomar']['status']}")
        for declaration in declarations_of(row):
            print(f"    {declaration['name']}  {declaration['file']}")
    print(f"{len(rows)} row(s)")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--json", action="store_true", help="print the full result as JSON")
    parser.add_argument("--restamp", action="store_true",
                        help="rewrite moved source lines and the content digest, then check")
    parser.add_argument("--rows", metavar="TEXT",
                        help="list the ledger rows whose id, label or declaration names contain TEXT")
    args = parser.parse_args(argv)
    try:
        ledger = read_json(LEDGER)
        baseline = read_json(BASELINE)
        exemptions = read_json(EXEMPTIONS)
    except LedgerFormatError as error:
        print(f"check_lean_paper_propagation: FAIL; {error}")
        return 1
    if args.rows is not None:
        print_rows(matching_rows(ledger, args.rows))
        return 0
    if args.restamp:
        currency, _texts = locate_rows(ledger, read_repository_text)
        ledger = restamped(ledger, currency.drift)
        LEDGER.write_text(json.dumps(ledger, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"check_lean_paper_propagation: restamped the digest; "
              f"{len(currency.drift)} source line(s) moved")
    report = evaluate(ledger, baseline, exemptions, read_repository_text, LeanSources())
    if args.json:
        print(json.dumps(report_json(report), indent=2, ensure_ascii=False))
    else:
        print_report(report)
        print(summary_line(report))
    return 1 if report.failed() else 0


if __name__ == "__main__":
    raise SystemExit(main())
