#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for ``contrast_ledger.py``: the ledger shape, the evidence check over
spans, declarations and relation ids, and trigger matching for packets and
return gates. Fixtures are small repositories in temporary directories; one
class also commits a fixture with git to test binding at ``HEAD``."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import contextlib
import io
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import contrast_ledger as cl  # noqa: E402

LEAN = """import Mathlib

/-! Module doc. -/

namespace Demo

/-- A redundant positivity hypothesis. -/
theorem keep_hn {k n : Nat} (hk : k < n) (hn : 0 < n) : 0 < n := by
  exact hn

@[simp]
theorem other_fact : True := trivial

def helper (n : Nat) : Nat :=
  n + 1

theorem long_proof : True := by
  trivial

end Demo
"""

NOTES = "line one\nthe bound is exactly 2 at every degree\nline three\nline four\n"


def write(root: Path, rel: str, text: str) -> None:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def atlas(rows: list[dict]) -> str:
    return json.dumps({"schema": "erdos249257-declaration-atlas/1",
                       "source_fingerprint": "sha256:fixture", "declarations": rows})


def row(row_id: str = "c-demo", **overrides) -> dict:
    base = {
        "id": row_id,
        "title": "Demo distinction",
        "distinction": "A hypothesis redundant inside a telescope can fail on its own.",
        "wrong_reading": "The hypothesis was dropped everywhere.",
        "right_reading": "The hypothesis is redundant only inside its telescope.",
        "evidence": [
            {"kind": "source_span", "path": "notes/NOTES.md", "start_line": 2, "end_line": 2,
             "must_contain": ["exactly 2 at every degree"]},
            {"kind": "declaration", "name": "keep_hn", "module": "lean/Demo.lean"},
            {"kind": "relation", "id": "rel-demo"},
        ],
        "provenance": [{"kind": "note", "ref": "fixture", "detail": "Made for the test."}],
        "triggers": {"problems": [251], "declarations": ["keep_hn"],
                     "phrases": ["slot replacement"]},
        "uses": {"packet_obligation": True, "return_gate": "Name the telescope.",
                 "regression": None, "experiment": None},
    }
    base.update(overrides)
    return base


class Fixture:
    def __init__(self, test: unittest.TestCase, rows: list[dict] | None = None,
                 relations: list[str] | None = ("rel-demo",), with_atlas: bool = True) -> None:
        self.tmp = tempfile.mkdtemp(prefix="contrast-ledger-")
        test.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp)
        write(self.root, "lean/Demo.lean", LEAN)
        write(self.root, "notes/NOTES.md", NOTES)
        if with_atlas:
            write(self.root, cl.ATLAS_PATH, atlas([
                {"name": "keep_hn", "module": "lean/Demo.lean", "line": 8, "kind": "theorem",
                 "claim_ids": ["demo_claim"]},
                {"name": "other_fact", "module": "lean/Demo.lean", "line": 12, "kind": "theorem"},
            ]))
        if relations is not None:
            write(self.root, cl.RELATIONS_PATH, json.dumps(
                {"schema": "plectis-relation-registry/1", "rows": [{"id": r} for r in relations]}))
        self.set_rows(rows if rows is not None else [row()])

    def set_rows(self, rows: list[dict]) -> None:
        write(self.root, cl.LEDGER_PATH, json.dumps({"schema": cl.SCHEMA, "rows": rows}))

    def check(self, **kwargs) -> dict:
        kwargs.setdefault("ref", None)
        return cl.check(self.root, **kwargs)


def git(root: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(root), "-c", "user.name=fixture",
                    "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false",
                    *args], check=True, capture_output=True)


class ShapeTests(unittest.TestCase):
    def test_valid_row_has_no_shape_errors(self) -> None:
        self.assertEqual(cl.shape_errors({"schema": cl.SCHEMA, "rows": [row()]}), [])

    def test_duplicate_ids_are_rejected(self) -> None:
        errors = cl.shape_errors({"schema": cl.SCHEMA, "rows": [row(), row()]})
        self.assertTrue(any("duplicate row id" in e for e in errors))

    def test_empty_triggers_are_rejected(self) -> None:
        bad = row(triggers={"problems": [], "declarations": [], "phrases": []})
        errors = cl.shape_errors({"schema": cl.SCHEMA, "rows": [bad]})
        self.assertTrue(any("at least one problem" in e for e in errors))

    def test_unknown_fields_kinds_and_uses_are_rejected(self) -> None:
        bad = row(extra=1, provenance=[{"kind": "rumour", "ref": "x", "detail": "y"}],
                  uses={"packet_obligation": "yes", "return_gate": "", "regression": None,
                        "experiment": None})
        bad["evidence"] = [{"kind": "claim", "id": "x"}]
        errors = cl.shape_errors({"schema": cl.SCHEMA, "rows": [bad]})
        joined = " | ".join(errors)
        for fragment in ("unknown fields", "provenance[0]", "packet_obligation",
                         "return_gate", "evidence[0].kind"):
            self.assertIn(fragment, joined)

    def test_wrong_schema_is_rejected(self) -> None:
        self.assertTrue(cl.shape_errors({"schema": "other", "rows": [row()]}))

    def test_seed_ledger_has_valid_shape_and_unique_ids(self) -> None:
        document = cl.load_ledger(ROOT / cl.LEDGER_PATH)
        self.assertEqual(cl.shape_errors(document), [])
        ids = [r["id"] for r in document["rows"]]
        self.assertEqual(len(ids), len(set(ids)))


class CheckTests(unittest.TestCase):
    def test_valid_fixture_passes_with_evidence_classes(self) -> None:
        report = Fixture(self).check()
        self.assertTrue(report["ok"], report["errors"])
        classes = [e.get("evidence_class") for e in report["rows"][0]["evidence"]]
        self.assertEqual(classes, ["source_span_bound_to_file_hash", "declaration_atlas_at_pin",
                                   "recorded_relation"])
        self.assertIn("Kernel acceptance", report["evidence_boundary"])
        # Atlas listing is a navigation projection; it never stands for compilation.
        self.assertIn("navigation projection", report["evidence_boundary"])
        self.assertIn("does not show that any CI job compiled", report["evidence_boundary"])

    def test_declaration_found_only_in_lean_source_is_the_weaker_class(self) -> None:
        fixture = Fixture(self, rows=[row(evidence=[
            {"kind": "declaration", "name": "helper", "module": "lean/Demo.lean"}])])
        report = fixture.check()
        self.assertTrue(report["ok"], report["errors"])
        self.assertEqual(report["rows"][0]["evidence"][0]["evidence_class"], "lean_source_worktree")
        self.assertEqual(report["rows"][0]["evidence"][0]["line"], 14)

    def test_missing_declaration_fails(self) -> None:
        fixture = Fixture(self, rows=[row(evidence=[
            {"kind": "declaration", "name": "no_such_thing", "module": "lean/Demo.lean"}])])
        report = fixture.check()
        self.assertFalse(report["ok"])
        self.assertTrue(any("no_such_thing" in e for e in report["errors"]))

    def test_declaration_listed_under_another_module_fails(self) -> None:
        fixture = Fixture(self, rows=[row(evidence=[
            {"kind": "declaration", "name": "other_fact", "module": "lean/Missing.lean"}])])
        report = fixture.check()
        self.assertFalse(report["ok"])
        self.assertTrue(any("lean/Demo.lean" in e for e in report["errors"]))

    def test_literal_outside_the_span_fails(self) -> None:
        # The literal exists in the file, one line away from the cited span.
        fixture = Fixture(self, rows=[row(evidence=[
            {"kind": "source_span", "path": "notes/NOTES.md", "start_line": 3, "end_line": 4,
             "must_contain": ["exactly 2 at every degree"]}])])
        report = fixture.check()
        self.assertFalse(report["ok"])
        self.assertTrue(any("literals outside the span" in e for e in report["errors"]))

    def test_out_of_range_span_fails(self) -> None:
        fixture = Fixture(self, rows=[row(evidence=[
            {"kind": "source_span", "path": "notes/NOTES.md", "start_line": 4, "end_line": 9,
             "must_contain": ["line"]}])])
        report = fixture.check()
        self.assertFalse(report["ok"])
        self.assertTrue(any("invalid line range" in e for e in report["errors"]))

    def test_escaping_path_fails(self) -> None:
        fixture = Fixture(self, rows=[row(evidence=[
            {"kind": "source_span", "path": "../outside.md", "start_line": 1, "end_line": 1,
             "must_contain": ["x"]}])])
        self.assertFalse(fixture.check()["ok"])

    def test_unknown_relation_fails_when_record_exists(self) -> None:
        fixture = Fixture(self, relations=["something-else"])
        report = fixture.check()
        self.assertFalse(report["ok"])
        self.assertTrue(any("rel-demo" in e for e in report["errors"]))

    def test_absent_relation_record_is_a_warning(self) -> None:
        report = Fixture(self, relations=None).check()
        self.assertTrue(report["ok"], report["errors"])
        self.assertTrue(any("absent" in w for w in report["warnings"]))
        self.assertEqual(report["rows"][0]["evidence"][2]["evidence_class"], "relation_unchecked")

    def test_missing_atlas_falls_back_to_source(self) -> None:
        report = Fixture(self, with_atlas=False).check()
        self.assertTrue(report["ok"], report["errors"])
        self.assertFalse(report["atlas"]["present"])
        self.assertEqual(report["rows"][0]["evidence"][1]["evidence_class"], "lean_source_worktree")

    def test_cli_check_exit_codes(self) -> None:
        fixture = Fixture(self)
        with contextlib.redirect_stdout(io.StringIO()) as out:
            code = cl.main(["--root", str(fixture.root), "check", "--worktree"])
        self.assertEqual(code, 0)
        self.assertTrue(json.loads(out.getvalue())["ok"])
        fixture.set_rows([row(), row()])
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cl.main(["--root", str(fixture.root), "check", "--worktree"]), 1)


@unittest.skipUnless(shutil.which("git"), "git is unavailable")
class GitRefTests(unittest.TestCase):
    def committed(self) -> Fixture:
        fixture = Fixture(self)
        git(fixture.root, "init", "-q")
        git(fixture.root, "add", "-A")
        git(fixture.root, "commit", "-q", "-m", "fixture")
        return fixture

    def test_spans_are_read_at_head(self) -> None:
        fixture = self.committed()
        # A working-tree edit that removes the literal does not change HEAD.
        write(fixture.root, "notes/NOTES.md", "changed\n" * 4)
        report = fixture.check(ref="HEAD")
        self.assertTrue(report["ok"], report["errors"])
        self.assertEqual(report["rows"][0]["evidence"][0]["binding"], "git_ref")
        self.assertEqual(len(report["source"]["commit"]), 40)

    def test_uncommitted_span_fails_and_uncommitted_declaration_warns(self) -> None:
        fixture = self.committed()
        write(fixture.root, "notes/NEW.md", "fresh text\n")
        write(fixture.root, "lean/New.lean", "theorem fresh_fact : True := trivial\n")
        fixture.set_rows([row(evidence=[
            {"kind": "source_span", "path": "notes/NEW.md", "start_line": 1, "end_line": 1,
             "must_contain": ["fresh"]},
            {"kind": "declaration", "name": "fresh_fact", "module": "lean/New.lean"}])])
        report = fixture.check(ref="HEAD")
        self.assertFalse(report["ok"])
        self.assertTrue(any("NEW.md is absent at git ref HEAD" in e for e in report["errors"]))
        declaration = report["rows"][0]["evidence"][1]
        self.assertEqual(declaration["status"], "ok")
        self.assertEqual(declaration["evidence_class"], "lean_source_worktree_uncommitted")
        allowed = fixture.check(ref="HEAD", allow_uncommitted=True)
        self.assertTrue(allowed["ok"], allowed["errors"])
        self.assertTrue(any("not committed" in w for w in allowed["warnings"]))


class SpanTests(unittest.TestCase):
    def test_declaration_span_takes_docstring_and_stops_at_next_item(self) -> None:
        lines = LEAN.splitlines(keepends=True)
        start, end, capped = cl.declaration_span(lines, 8)
        self.assertEqual((start, end, capped), (7, 9, False))
        start, end, capped = cl.declaration_span(lines, 12)
        self.assertEqual((start, end), (11, 12))
        start, end, capped = cl.declaration_span(lines, 14, max_lines=1)
        self.assertEqual((start, end, capped), (14, 14, True))

    def test_declaration_lines_accept_namespace_prefixes(self) -> None:
        lines = LEAN.splitlines(keepends=True)
        self.assertEqual(cl.declaration_lines(lines, "Demo.keep_hn"), [8])
        self.assertEqual(cl.declaration_lines(lines, "keep_hn"), [8])
        self.assertEqual(cl.declaration_lines(lines, "keep"), [])


class TriggerTests(unittest.TestCase):
    rows = [row("c-a"), row("c-b", triggers={"problems": [1041], "declarations": [],
                                             "phrases": ["exactly 2 at every degree"]})]

    def ids(self, matches: list[dict]) -> list[str]:
        return [m["id"] for m in matches]

    def test_problem_declaration_and_phrase_triggers(self) -> None:
        self.assertEqual(self.ids(cl.triggered(self.rows, problem=251)), ["c-a"])
        self.assertEqual(self.ids(cl.triggered(self.rows, declarations=["Demo.keep_hn"])), ["c-a"])
        text = "The   bound is EXACTLY 2 at every\ndegree here."
        self.assertEqual(self.ids(cl.triggered(self.rows, text=text)), ["c-b"])

    def test_declaration_mentioned_in_text_triggers_as_a_whole_token(self) -> None:
        self.assertEqual(self.ids(cl.triggered(self.rows, text="uses Demo.keep_hn twice")), ["c-a"])
        self.assertEqual(cl.triggered(self.rows, text="uses keep_hnx and xkeep_hn"), [])

    def test_nothing_supplied_matches_nothing(self) -> None:
        self.assertEqual(cl.triggered(self.rows), [])

    def test_gate_flags_without_a_verdict(self) -> None:
        result = cl.gate(self.rows, "a slot replacement for hn", problems=[1041])
        self.assertIsNone(result["verdict"])
        self.assertEqual(result["evidence_class"], "authored_review")
        self.assertEqual([f["id"] for f in result["flags"]], ["c-a", "c-b"])
        self.assertEqual(result["flags"][0]["must_address"], "Name the telescope.")
        self.assertEqual(result["flags"][1]["matched_on"], [{"on": "problem", "value": 1041}])

    def test_seed_ledger_triggers(self) -> None:
        rows = cl.load_ledger(ROOT / cl.LEDGER_PATH)["rows"]
        self.assertIn("c-251-equivalence-no-supply",
                      self.ids(cl.triggered(rows, problem=251)))
        self.assertIn("c-1041-false-target",
                      self.ids(cl.triggered(rows, declarations=["erdos1041_counterexample_hausdorff"])))
        flagged = cl.gate(rows, "We propose a slot replacement for hn.", problems=[])
        self.assertIn("c-telescope-redundancy", [f["id"] for f in flagged["flags"]])

    def test_cli_triggered_reports_return_gates(self) -> None:
        fixture = Fixture(self)
        with contextlib.redirect_stdout(io.StringIO()) as out:
            code = cl.main(["--root", str(fixture.root), "triggered", "--problem", "251"])
        self.assertEqual(code, 0)
        payload = json.loads(out.getvalue())
        self.assertIsNone(payload["verdict"])
        self.assertEqual(payload["matches"][0]["return_gate"], "Name the telescope.")


if __name__ == "__main__":
    unittest.main()
