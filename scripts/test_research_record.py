#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for ``research_record.py``: the hash-chained journal (canonical lines,
torn tails, tampering, CI refusal), each event kind's schema and references,
review invalidation of consumer dispositions, milestones computed from a
fixture checkout (atlas, paper coverage, claims, Comparator configurations,
git ancestry), and the status projection. One class reads the real checkout
and checks that the stranded #249 endpoint's milestones are reported as the
committed files show them; it is skipped when those files are absent."""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
import shutil
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import research_record as rec  # noqa: E402

T0 = "2026-09-28T10:00:00Z"
DECL = "Toy.Paper.main_theorem"
MODULE = "lean/Toy/Paper.lean"
LEAN = """\
namespace Toy.Paper
theorem main_theorem : True := trivial
theorem helper : True := trivial
theorem orphan_lemma : True := trivial
end Toy.Paper
"""


def write_json(root: Path, relative: str, value) -> None:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value), encoding="utf-8")


COVERAGE_WORKFLOW = """\
jobs:
  coverage:
    steps:
      - name: Memory-bounded coverage build
        id: coverage-build
        run: >-
          python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness
          ErdosProblems.CoverageAgg

      - name: Save
"""


def write_build(root: Path, root_imports=("Toy.Paper",), coverage_imports=()) -> None:
    """The module graph and coverage workflow ``compiled_modules`` reads."""
    root_file = root / "lean/ErdosProblems.lean"
    root_file.parent.mkdir(parents=True, exist_ok=True)
    root_file.write_text("".join(f"import {m}\n" for m in root_imports), encoding="utf-8")
    nodes = [{"id": "Toy.Paper", "path": MODULE, "imports": []},
             {"id": "Toy.Other", "path": "lean/Toy/Other.lean", "imports": []},
             {"id": "ErdosProblems.CoverageAgg", "path": "lean/ErdosProblems/CoverageAgg.lean",
              "imports": list(coverage_imports)}]
    claims_path = root / "docs/claims.json"
    claims = json.loads(claims_path.read_text(encoding="utf-8")) if claims_path.is_file() else {}
    claims["machine_readable_paper"] = {"module_graph": {
        "root": "lean/ErdosProblems.lean", "additional_roots": [], "auxiliary_roots": [], "nodes": nodes}}
    write_json(root, "docs/claims.json", claims)
    workflow = root / rec.COVERAGE_WORKFLOW_PATH
    workflow.parent.mkdir(parents=True, exist_ok=True)
    workflow.write_text(COVERAGE_WORKFLOW, encoding="utf-8")


def make_checkout(root: Path) -> None:
    """A tiny checkout: main_theorem is on main, in the short paper, registered and
    Comparator-listed through a wrapper; helper is on main only. Toy.Paper is
    compiled through the default root; Toy.Other is listed in the atlas and
    compiled by nothing."""
    (root / MODULE).parent.mkdir(parents=True, exist_ok=True)
    (root / MODULE).write_text(LEAN, encoding="utf-8")
    write_json(root, "docs/declaration_atlas.json", {
        "source_fingerprint": "sha256:" + "b" * 64,
        "declarations": [
            {"id": f"{MODULE}:2:main_theorem", "name": "main_theorem", "module": MODULE, "line": 2,
             "signature": "theorem main_theorem : True"},
            {"id": f"{MODULE}:3:helper", "name": "helper", "module": MODULE, "line": 3,
             "signature": "theorem helper : True"},
            {"id": "lean/Toy/Other.lean:1:main_theorem", "name": "main_theorem", "module": "lean/Toy/Other.lean",
             "line": 1, "signature": "theorem main_theorem : False"}]})
    write_json(root, "docs/paper_lean_coverage.json", {
        "lean_pin": "c" * 40,
        "papers": [{"paper_id": "toy-short", "side": "short"}, {"paper_id": "toy-long", "side": "long"}],
        "rows": [{"id": "toy-short#thm", "paper_id": "toy-short", "side": "short",
                  "lean": {"declarations": [{"name": DECL, "file": MODULE}]}},
                 {"id": "toy-long#thm", "paper_id": "toy-long", "side": "long",
                  "lean": {"declarations": [{"name": "Toy.Paper.helper", "file": MODULE}]}}]})
    write_json(root, "docs/claims.json", {
        "claims": [{"id": "toy_claim", "declarations": [{"name": "main_theorem", "module": "Toy/Paper.lean",
                                                          "line": 2}]}],
        "external_verification_packet": {"main_results": [
            {"id": "toy_main", "original_declaration": DECL,
             "wrapper_declaration": "Wrap.main_theorem"}]}})
    write_json(root, "verification/comparator.json", {"theorem_names": ["Wrap.main_theorem"]})
    write_json(root, "verification/comparator-negative-mismatch.json", {"theorem_names": ["Toy.Paper.helper"]})
    write_build(root)


def round_detail(rid="r1", consumers=("lean", "papers"), expected=2):
    return {"round_id": rid, "packet_id": "pkt-" + rid, "packet_manifest_sha256": "a" * 64,
            "source_commit": "f18ed012", "ask": "close the gap", "consumers": list(consumers),
            "expected_returns": expected}


def return_detail(rid="A", round_id="r1", public_copy=None, data=b"return bytes"):
    return {"return_id": rid, "round_id": round_id, "sha256": hashlib.sha256(data).hexdigest(),
            "bytes": len(data), "media_type": "application/zip",
            "custody": {"store": "type_b_return_intake", "batch_id": "batch_1", "return_id": rid},
            "public_copy": public_copy}


def review(rid="A", disposition="admitted_for_integration"):
    return {"return_id": rid, "disposition": disposition, "rationale": "read in full", "reviewer": "maintainer"}


def output(oid="out1", declaration=DECL, required=("lean_on_main", "short_paper_linked", "long_record_linked",
                                                     "claim_registered", "comparator_listed"),
           produced_by=("A",), **locator_extra):
    locator = {"declaration": declaration}
    locator.update(locator_extra)
    return {"output_id": oid, "kind": "lean_declaration", "locator": locator, "problem": 249,
            "produced_by": list(produced_by), "required": list(required)}


def consumer(subject="A", name="lean", status="updated", evidence=("scripts/x.py",), reentry=None):
    d = {"subject_id": subject, "consumer": name, "status": status, "reason": "handled",
         "evidence": list(evidence)}
    if reentry is not None:
        d["reentry"] = reentry
    return d


class Base(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        patcher = mock.patch.dict(os.environ)
        patcher.start()
        self.addCleanup(patcher.stop)
        os.environ.pop("CI", None)
        self.clock = 0

    def add(self, kind: str, detail: dict, subject: str | None = None):
        subject_field = rec.KINDS[kind][0]
        self.clock += 1
        stamp = f"2026-09-28T10:{self.clock // 60:02d}:{self.clock % 60:02d}Z"
        return rec.append(self.root, kind, subject or detail[subject_field], detail, recorded_at=stamp)

    def journal(self) -> Path:
        return self.root / rec.JOURNAL_PATH

    def lifecycle(self) -> None:
        self.add("round_opened", round_detail())
        self.add("return_received", return_detail("A"))
        self.add("return_received", return_detail("B", data=b"other"))
        self.add("review_recorded", review("A"))
        self.add("component_disposed", {"return_id": "A", "component": "contracts", "decision": "taken",
                                        "reason": "sound", "landed_as": ["lean/Toy/Paper.lean"]})
        self.add("component_disposed", {"return_id": "A", "component": "optimiser", "decision": "deferred",
                                        "reason": "needs the packet compiler", "landed_as": [],
                                        "reentry": {"owner": "record lane", "trigger": "packet compiler lands"}})
        self.add("output_declared", output())
        self.add("consumer_disposed", consumer("A", "lean"))
        self.add("consumer_disposed", consumer("A", "papers", "deferred", (),
                                               {"owner": "papers pass", "trigger": "endpoint in the long record"}))
        self.add("review_recorded", review("B", "rejected_retained"))


class Journal(Base):
    def test_append_and_verify_chain(self) -> None:
        first = self.add("round_opened", round_detail())
        second = self.add("round_sealed", {"round_id": "r1"})
        self.assertEqual(first["sequence"], 0)
        self.assertEqual(first["previous"], rec.ZERO)
        self.assertEqual(second["previous"], first["event_sha"])
        body = {k: v for k, v in second.items() if k != "event_sha"}
        self.assertEqual(second["event_sha"], hashlib.sha256(rec.canonical(body).encode()).hexdigest())
        lines = self.journal().read_text(encoding="utf-8").splitlines()
        self.assertEqual(lines[1], rec.canonical(second))
        self.assertEqual(self.journal().stat().st_mode & 0o777, 0o644)
        report = rec.verify(self.root)
        self.assertTrue(report["ok"], report["errors"])
        self.assertEqual(report["events"], 2)
        self.assertEqual(report["head"], second["event_sha"])

    def test_absent_and_empty_journal_verify(self) -> None:
        self.assertTrue(rec.verify(self.root)["ok"])
        self.journal().parent.mkdir(parents=True)
        self.journal().write_bytes(b"")
        self.assertEqual(rec.verify(self.root)["events"], 0)

    def test_torn_final_line_is_an_explicit_error(self) -> None:
        self.add("round_opened", round_detail())
        with self.journal().open("ab") as stream:
            stream.write(b'{"sequence":1')
        report = rec.verify(self.root)
        self.assertFalse(report["ok"])
        self.assertIn("torn final line", report["errors"][0])
        with self.assertRaises(rec.RecordError):
            self.add("round_sealed", {"round_id": "r1"})

    def test_tampering_is_detected(self) -> None:
        self.add("round_opened", round_detail())
        self.add("round_sealed", {"round_id": "r1"})
        lines = self.journal().read_text(encoding="utf-8").splitlines()
        cases = {
            "detail edited": lines[0].replace("close the gap", "close the gaps") + "\n" + lines[1] + "\n",
            "reordered": lines[1] + "\n" + lines[0] + "\n",
            "dropped first": lines[1] + "\n",
            "non-canonical": json.dumps(json.loads(lines[0]), indent=1).replace("\n", "") + "\n" + lines[1] + "\n",
            "blank line": lines[0] + "\n\n" + lines[1] + "\n",
        }
        for label, text in cases.items():
            with self.subTest(label):
                self.journal().write_text(text, encoding="utf-8")
                self.assertFalse(rec.verify(self.root)["ok"])

    def test_append_refused_under_ci(self) -> None:
        os.environ["CI"] = "true"
        with self.assertRaises(rec.RecordError):
            self.add("round_opened", round_detail())
        self.assertFalse(self.journal().exists())
        os.environ["CI"] = ""
        with self.assertRaises(rec.RecordError):
            self.add("round_opened", round_detail())

    def test_time_must_not_go_backwards(self) -> None:
        rec.append(self.root, "round_opened", "r1", round_detail(), recorded_at="2026-09-28T11:00:00Z")
        with self.assertRaises(rec.RecordError):
            rec.append(self.root, "round_sealed", "r1", {"round_id": "r1"}, recorded_at="2026-09-28T10:00:00Z")
        for bad in ("2026-09-28 12:00:00", "2026-09-28T12:00:00+00:00", "2026-13-28T12:00:00Z"):
            with self.subTest(bad):
                with self.assertRaises(rec.RecordError):
                    rec.append(self.root, "round_sealed", "r1", {"round_id": "r1"}, recorded_at=bad)

    def test_nothing_is_written_when_an_append_is_refused(self) -> None:
        self.add("round_opened", round_detail())
        before = self.journal().read_bytes()
        with self.assertRaises(rec.RecordError):
            self.add("review_recorded", review("missing"))
        self.assertEqual(self.journal().read_bytes(), before)
        self.assertEqual(sorted(p.name for p in self.journal().parent.iterdir()), ["journal.jsonl"])


class Schemas(Base):
    def test_kind_schemas(self) -> None:
        good = round_detail()
        cases = {
            "unknown kind": ("round_closed", good, "r1"),
            "missing field": ("round_opened", {k: v for k, v in good.items() if k != "ask"}, "r1"),
            "extra field": ("round_opened", dict(good, verdict="proved"), "r1"),
            "subject mismatch": ("round_opened", good, "r2"),
            "empty consumers": ("round_opened", dict(good, consumers=[]), "r1"),
            "bad manifest hash": ("round_opened", dict(good, packet_manifest_sha256="abc"), "r1"),
            "bad commit": ("round_opened", dict(good, source_commit="main"), "r1"),
            "private path": ("round_opened", dict(good, ask="see /Users/someone/file"), "r1"),
            "negative count": ("round_opened", dict(good, expected_returns=-1), "r1"),
        }
        for label, (kind, detail, subject) in cases.items():
            with self.subTest(label):
                with self.assertRaises(rec.RecordError):
                    rec.append(self.root, kind, subject, detail, recorded_at=T0)
        self.assertFalse(self.journal().exists())

    def test_return_and_review_schemas(self) -> None:
        self.add("round_opened", round_detail())
        bad_custody = return_detail()
        bad_custody["custody"] = {"store": "elsewhere", "batch_id": "b", "return_id": "A"}
        for label, detail in {"custody store": bad_custody,
                              "absolute copy": return_detail(public_copy="/etc/passwd"),
                              "parent copy": return_detail(public_copy="../x")}.items():
            with self.subTest(label):
                with self.assertRaises(rec.RecordError):
                    self.add("return_received", detail)
        self.add("return_received", return_detail())
        with self.assertRaises(rec.RecordError):
            self.add("review_recorded", review("A", "accepted"))

    def test_component_and_consumer_rules(self) -> None:
        self.add("round_opened", round_detail())
        self.add("return_received", return_detail())
        component = {"return_id": "A", "component": "c", "decision": "taken", "reason": "r", "landed_as": ["x"]}
        with self.assertRaises(rec.RecordError):
            self.add("component_disposed", component)  # before review
        with self.assertRaises(rec.RecordError):
            self.add("consumer_disposed", consumer())  # before review
        self.add("review_recorded", review())
        deferral = dict(component, decision="deferred", landed_as=[])
        for label, detail in {
                "taken without landing": dict(component, landed_as=[]),
                "rejected with landing": dict(component, decision="rejected"),
                "new deferral without reentry": deferral,
                "reentry on a taken component": dict(component, reentry={"owner": "o", "trigger": "t"}),
                "empty reentry trigger": dict(deferral, reentry={"owner": "o", "trigger": ""})}.items():
            with self.subTest(label):
                with self.assertRaises(rec.RecordError):
                    self.add("component_disposed", detail)
        self.add("component_disposed", dict(deferral, reentry={"owner": "o", "trigger": "t"}))
        for label, detail in {
                "undeclared consumer": consumer(name="stranger"),
                "updated without evidence": consumer(evidence=()),
                "deferred without reentry": consumer(status="deferred", evidence=()),
                "reentry on non-deferral": consumer(reentry={"owner": "o", "trigger": "t"}),
                "empty reentry owner": consumer(status="deferred", evidence=(), reentry={"owner": "", "trigger": "t"}),
                "unknown subject": consumer(subject="nobody")}.items():
            with self.subTest(label):
                with self.assertRaises(rec.RecordError):
                    self.add("consumer_disposed", detail)
        self.add("consumer_disposed", consumer(status="not_applicable", evidence=()))

    def test_output_and_milestone_rules(self) -> None:
        self.add("round_opened", round_detail())
        self.add("return_received", return_detail())
        for label, detail in {
                "unknown producer": output(produced_by=("ghost",)),
                "declaration milestone without declaration": dict(output(), locator={"path": "docs/x.md"}),
                "pr_merged without commit": output(required=("pr_merged",)),
                "unknown locator field": output(proof="yes"),
                "bad milestone name": output(required=("Lean On Main",))}.items():
            with self.subTest(label):
                with self.assertRaises(rec.RecordError):
                    self.add("output_declared", detail)
        self.add("output_declared", output(required=("lean_on_main", "specialist_review")))
        with self.assertRaises(rec.RecordError):
            self.add("output_declared", output())  # re-declaration
        report = {"output_id": "out1", "milestone": "specialist_review", "evidence": "letter of 28 Sep",
                  "evidence_class": "authored_review"}
        for label, detail in {
                "computed milestone": dict(report, milestone="lean_on_main"),
                "undeclared milestone": dict(report, milestone="palomar_prepared"),
                "atlas class claimed": dict(report, evidence_class="declaration_atlas_at_pin"),
                "retired class claimed": dict(report, evidence_class="kernel_declaration_at_pin")}.items():
            with self.subTest(label):
                with self.assertRaises(rec.RecordError):
                    self.add("milestone_reported", detail)
        self.add("milestone_reported", report)

    def test_sealed_round_takes_no_returns(self) -> None:
        self.add("round_opened", round_detail())
        self.add("round_sealed", {"round_id": "r1"})
        with self.assertRaises(rec.RecordError):
            self.add("return_received", return_detail())
        with self.assertRaises(rec.RecordError):
            self.add("round_sealed", {"round_id": "r1"})
        with self.assertRaises(rec.RecordError):
            self.add("round_opened", round_detail())

    def test_public_copy_is_checked(self) -> None:
        self.add("round_opened", round_detail())
        copy = self.root / "docs/research-commons/record/objects/A.bin"
        copy.parent.mkdir(parents=True)
        copy.write_bytes(b"return bytes")
        self.add("return_received", return_detail(public_copy="docs/research-commons/record/objects/A.bin"))
        self.assertTrue(rec.verify(self.root)["ok"])
        copy.write_bytes(b"altered")
        self.assertFalse(rec.verify(self.root)["ok"])
        copy.unlink()
        self.assertIn("missing", rec.verify(self.root)["errors"][0])

    def test_verify_catches_a_hand_written_computed_milestone(self) -> None:
        self.add("round_opened", round_detail())
        self.add("return_received", return_detail())
        self.add("output_declared", output(required=("lean_on_main",)))
        events = rec.read_events(self.journal())
        body = {"sequence": 3, "previous": events[-1]["event_sha"], "kind": "milestone_reported",
                "subject": "out1", "detail": {"output_id": "out1", "milestone": "lean_on_main",
                                              "evidence": "trust me", "evidence_class": "reported"},
                "recorded_at": "2026-09-28T12:00:00Z"}
        forged = dict(body, event_sha=rec.event_hash(body))
        with self.journal().open("a", encoding="utf-8") as stream:
            stream.write(rec.canonical(forged) + "\n")
        report = rec.verify(self.root)
        self.assertFalse(report["ok"])
        self.assertIn("computed", report["errors"][0])


class Milestones(Base):
    def setUp(self) -> None:
        super().setUp()
        make_checkout(self.root)
        self.checkout = rec.Checkout(self.root)

    def states(self, declaration, module=None):
        result = self.checkout.declaration_milestones(declaration, module)
        return {k: v["state"] for k, v in result["milestones"].items()}, result

    def test_fully_linked_declaration(self) -> None:
        states, result = self.states(DECL)
        self.assertEqual(states, {"lean_on_main": "done", "short_paper_linked": "done",
                                  "long_record_linked": "missing", "claim_registered": "done",
                                  "comparator_listed": "done"})
        self.assertEqual(result["declaration"]["module"], MODULE)
        comparator = result["milestones"]["comparator_listed"]["evidence"]["entries"]
        self.assertEqual(comparator, [{"config": "verification/comparator.json", "name": "Wrap.main_theorem",
                                       "via_wrapper": True}])
        self.assertEqual(result["milestones"]["lean_on_main"]["evidence_class"], "declaration_atlas_at_pin")
        self.assertIs(result["milestones"]["lean_on_main"]["evidence"]["compiled_target"], True)

    def test_compiled_modules_follow_roots_and_coverage_targets(self) -> None:
        self.assertEqual(rec.compiled_modules(self.root),
                         frozenset({"ErdosProblems", "Toy.Paper", "ErdosProblems.CoverageAgg"}))
        write_build(self.root, root_imports=(), coverage_imports=("Toy.Other",))
        self.assertEqual(rec.compiled_modules(self.root),
                         frozenset({"ErdosProblems", "ErdosProblems.CoverageAgg", "Toy.Other"}))
        (self.root / rec.COVERAGE_WORKFLOW_PATH).unlink()
        self.assertIsNone(rec.compiled_modules(self.root))

    def test_listed_but_not_compiled_is_not_on_main(self) -> None:
        # The atlas lists Toy.Other.main_theorem, but no build root or coverage target reaches Toy.Other.
        states, result = self.states("main_theorem", "lean/Toy/Other.lean")
        self.assertEqual(result["declaration"]["atlas_state"], "found")
        lean = result["milestones"]["lean_on_main"]
        self.assertEqual(lean["state"], "missing")
        self.assertIs(lean["evidence"]["compiled_target"], False)
        self.assertIn("listed in the declaration atlas", lean["evidence"]["reason"])
        write_build(self.root, coverage_imports=("Toy.Other",))
        self.checkout = rec.Checkout(self.root)
        states, _ = self.states("main_theorem", "lean/Toy/Other.lean")
        self.assertEqual(states["lean_on_main"], "done")

    def test_unreadable_build_inputs_leave_lean_on_main_unknown(self) -> None:
        (self.root / rec.COVERAGE_WORKFLOW_PATH).unlink()
        self.checkout = rec.Checkout(self.root)
        states, result = self.states(DECL)
        self.assertEqual(states["lean_on_main"], "unknown")
        self.assertIsNone(result["milestones"]["lean_on_main"]["evidence"]["compiled_target"])

    def test_short_name_with_module_and_negative_configs(self) -> None:
        states, result = self.states("helper", "Toy.Paper")
        self.assertEqual(result["declaration"]["full_name"], "Toy.Paper.helper")
        self.assertEqual(states["lean_on_main"], "done")
        self.assertEqual(states["long_record_linked"], "done")
        self.assertEqual(states["claim_registered"], "missing")
        # Listed only in a negative-mismatch configuration: nothing is queued.
        self.assertEqual(states["comparator_listed"], "missing")

    def test_namespace_disambiguates_same_short_name(self) -> None:
        # Another module also has a main_theorem; the full name selects this one.
        states, result = self.states(DECL)
        self.assertEqual(result["declaration"]["atlas_state"], "found")
        states, result = self.states("main_theorem")
        self.assertEqual(states["lean_on_main"], "unknown")  # ambiguous without a module

    def test_absent_declaration_and_absent_files(self) -> None:
        states, _ = self.states("Toy.Paper.orphan_lemma", MODULE)
        self.assertEqual(states["lean_on_main"], "missing")
        self.assertEqual(states["short_paper_linked"], "missing")
        for relative in ("docs/declaration_atlas.json", "docs/paper_lean_coverage.json", "docs/claims.json"):
            (self.root / relative).unlink()
        shutil.rmtree(self.root / "verification")
        self.checkout = rec.Checkout(self.root)
        states, _ = self.states(DECL)
        self.assertEqual(set(states.values()), {"unknown"})


@unittest.skipUnless(shutil.which("git"), "git unavailable")
class PullRequestMerged(Base):
    def git(self, *args: str) -> str:
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@example.invalid",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@example.invalid", GIT_CONFIG_GLOBAL="/dev/null",
                   GIT_CONFIG_SYSTEM="/dev/null")
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True,
                              text=True, env=env).stdout.strip()

    def test_ancestry(self) -> None:
        self.git("init", "-q", "-b", "main")
        self.git("commit", "-q", "--allow-empty", "-m", "base")
        merged = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "-b", "side")
        self.git("commit", "-q", "--allow-empty", "-m", "side")
        side = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "main")
        checkout = rec.Checkout(self.root)
        self.assertEqual(checkout.pr_merged({"merge_commit": merged})["state"], "done")
        self.assertEqual(checkout.pr_merged({"merge_commit": side})["state"], "missing")
        self.assertEqual(checkout.pr_merged({"merge_commit": "d" * 40})["state"], "unknown")
        self.assertEqual(checkout.pr_merged({"merge_commit": "--help"})["state"], "unknown")


class Status(Base):
    def setUp(self) -> None:
        super().setUp()
        make_checkout(self.root)

    def test_projection(self) -> None:
        self.lifecycle()
        report = rec.status(self.root)
        self.assertEqual(report["journal"]["errors"], [])
        out = report["outputs"]["out1"]
        self.assertEqual(out["missing"], ["long_record_linked"])
        self.assertFalse(out["complete"])
        a = report["returns"]["A"]
        self.assertEqual(a["phase"], "outputs_incomplete")
        self.assertEqual(a["missing_consumers"], [])
        self.assertIn("output_incomplete:out1", a["outstanding"])
        self.assertEqual(a["component_decisions"], {"deferred": 1, "taken": 1})
        self.assertEqual(report["returns"]["B"]["phase"], "closed_without_integration")
        self.assertEqual(report["returns"]["B"]["outstanding"], [])
        r1 = report["rounds"]["r1"]
        self.assertIn("unsealed", r1["outstanding"])
        self.assertIn("return:A", r1["outstanding"])
        self.assertNotIn("arrivals:2_of_2", r1["outstanding"])
        deferred = {(d["subject_id"], d.get("consumer") or d.get("component")): d for d in report["deferred"]}
        self.assertEqual(deferred[("A", "papers")]["owner"], "papers pass")
        self.assertEqual((deferred[("A", "optimiser")]["owner"], deferred[("A", "optimiser")]["trigger"]),
                         ("record lane", "packet compiler lands"))

    def test_later_review_invalidates_consumer_dispositions(self) -> None:
        self.lifecycle()
        self.add("review_recorded", review("A", "repair_required"))
        a = rec.status(self.root)["returns"]["A"]
        self.assertEqual(a["consumers"], {})
        self.assertEqual(a["dispositions_invalidated_by_later_review"], ["lean", "papers"])
        self.assertEqual(a["phase"], "repair_required")
        self.add("review_recorded", review("A"))
        a = rec.status(self.root)["returns"]["A"]
        self.assertEqual(a["missing_consumers"], ["lean", "papers"])
        self.assertEqual(a["phase"], "dispositions_incomplete")

    def test_reported_milestones_and_orphans(self) -> None:
        self.add("round_opened", round_detail("r2", expected=1))
        self.add("return_received", return_detail("C", "r2"))
        self.add("review_recorded", review("C"))
        self.add("output_declared", output("tool1", required=("specialist_review",), produced_by=()))
        report = rec.status(self.root)
        self.assertEqual(report["outputs"]["tool1"]["missing"], ["specialist_review"])
        self.assertEqual(report["orphans"]["outputs_without_producer"], ["tool1"])
        self.assertEqual(report["orphans"]["admitted_returns_without_landing"], ["C"])
        self.add("milestone_reported", {"output_id": "tool1", "milestone": "specialist_review",
                                        "evidence": "review of 28 Sep", "evidence_class": "authored_review"})
        tool = rec.status(self.root)["outputs"]["tool1"]
        self.assertTrue(tool["complete"])
        self.assertEqual(tool["milestones"]["specialist_review"]["source"], "reported")

    def test_round_filter_markdown_and_determinism(self) -> None:
        self.lifecycle()
        self.add("round_opened", round_detail("r2", expected=None))
        first = rec.canonical(rec.status(self.root))
        self.assertEqual(first, rec.canonical(rec.status(self.root)))
        only = rec.status(self.root, "r2")
        self.assertEqual(list(only["rounds"]), ["r2"])
        self.assertEqual(only["outputs"], {})
        with self.assertRaises(rec.RecordError):
            rec.status(self.root, "r9")
        text = rec.render_markdown(rec.status(self.root))
        self.assertIn("`out1`", text)
        self.assertIn("Still missing: long_record_linked.", text)
        self.assertNotIn(chr(0x2014), text)

    def test_cli(self) -> None:
        self.lifecycle()
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(rec.main(["--root", str(self.root), "verify"]), 0)
        self.assertTrue(json.loads(out.getvalue())["ok"])
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(rec.main(["--root", str(self.root), "status", "--format", "md"]), 0)
        self.assertIn("# Research record status", out.getvalue())
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = rec.main(["--root", str(self.root), "append", "round_sealed", "--subject", "r1",
                             "--detail-json", '{"round_id": "r1"}', "--recorded-at", "2026-09-29T00:00:00Z"])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out.getvalue())["kind"], "round_sealed")
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertEqual(rec.main(["--root", str(self.root), "append", "round_sealed", "--subject", "r1",
                                       "--detail-json", "{"]), 1)


REAL_FILES = ("docs/declaration_atlas.json", "docs/paper_lean_coverage.json", "docs/claims.json",
              "verification/comparator.json", ".github/workflows/lean-coverage-build.yml",
              "lean/Erdos249257.lean", "lean/ErdosProblems.lean")
ENDPOINT_MODULE = "ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint"


def independent_compiled_modules() -> set[str]:
    """The compiled set by a walk over the Lean source's own import lines.

    It reads ``lean/<Module>.lean`` files directly, never the module graph in
    ``docs/claims.json``, so it checks the helper instead of repeating it.
    """
    import coverage_build_targets

    pattern = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
    seen: set[str] = set()
    frontier = ["Erdos249257", "ErdosProblems", *coverage_build_targets.targets()]
    while frontier:
        module = frontier.pop()
        path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
        if module in seen or not path.is_file():
            continue
        seen.add(module)
        frontier.extend(pattern.findall(path.read_text(encoding="utf-8")))
    return seen
STRANDED = "ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap"
STRANDED_SHORT = "irrational_totient_series_of_goodBase_gap"


@unittest.skipUnless(all((ROOT / f).is_file() for f in REAL_FILES), "checkout files absent")
class StrandedEndpointOnRealCheckout(Base):
    """The stranded #249 endpoint, declared as an output in a scratch journal and
    projected against the committed files. An independent reading of the same
    files is the oracle, so the test stays correct after the debt is paid."""

    def oracle(self) -> dict[str, str]:
        atlas = json.loads((ROOT / "docs/declaration_atlas.json").read_text(encoding="utf-8"))
        compiled = independent_compiled_modules()
        on_main = ENDPOINT_MODULE in compiled and any(
            d.get("name") == STRANDED_SHORT and "Erdos249Endpoint" in d.get("module", "")
            for d in atlas["declarations"])
        coverage = json.loads((ROOT / "docs/paper_lean_coverage.json").read_text(encoding="utf-8"))
        sides = {p["paper_id"]: p["side"] for p in coverage["papers"]}
        linked = {"short": False, "long": False}
        for row in coverage["rows"]:
            names = [d.get("name") for d in (row.get("lean") or {}).get("declarations", [])]
            if STRANDED in names:
                linked[sides[row["paper_id"]]] = True
        claims_text = (ROOT / "docs/claims.json").read_text(encoding="utf-8")
        comparator = False
        for path in (ROOT / "verification").glob("*.json"):
            if "negative" in path.name:
                continue
            if STRANDED_SHORT in path.read_text(encoding="utf-8"):
                comparator = True

        def state(flag: bool) -> str:
            return "done" if flag else "missing"
        return {"lean_on_main": state(on_main), "short_paper_linked": state(linked["short"]),
                "long_record_linked": state(linked["long"]), "claim_registered": state(STRANDED_SHORT in claims_text),
                "comparator_listed": state(comparator)}

    def test_projection_matches_the_committed_files(self) -> None:
        for relative in REAL_FILES:
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            os.symlink(ROOT / relative, target)
        for path in (ROOT / "verification").glob("*.json"):
            target = self.root / "verification" / path.name
            if not target.exists():
                os.symlink(path, target)
        lean = ROOT / "lean/ErdosProblems/ArgumentGraph/Results/Erdos249Endpoint.lean"
        if lean.is_file():
            (self.root / "lean/ErdosProblems/ArgumentGraph/Results").mkdir(parents=True)
            os.symlink(lean, self.root / "lean/ErdosProblems/ArgumentGraph/Results/Erdos249Endpoint.lean")
        self.add("round_opened", round_detail("round5", consumers=("papers",), expected=1))
        self.add("return_received", return_detail("r5A", "round5"))
        self.add("review_recorded", review("r5A"))
        self.add("output_declared", output("endpoint249", STRANDED, produced_by=("r5A",)))
        out = rec.status(self.root)["outputs"]["endpoint249"]
        computed = {k: v["state"] for k, v in out["milestones"].items()}
        self.assertEqual(computed, self.oracle())
        self.assertEqual(computed["lean_on_main"], "done")
        self.assertEqual(out["missing"], [m for m in out["required"] if computed[m] == "missing"])
        self.assertEqual(out["unknown"], [])
        self.assertIs(out["milestones"]["lean_on_main"]["evidence"]["compiled_target"], True)

    def test_compiled_modules_agree_with_the_build_planner(self) -> None:
        compiled = rec.compiled_modules(ROOT)
        independent = independent_compiled_modules()
        self.assertIsNotNone(compiled)
        graph = json.loads((ROOT / "docs/claims.json").read_text(encoding="utf-8"))
        nodes = {n["id"] for n in graph["machine_readable_paper"]["module_graph"]["nodes"]}
        self.assertEqual(sorted(compiled & nodes), sorted(independent & nodes))
        self.assertIn(ENDPOINT_MODULE, compiled)


if __name__ == "__main__":
    unittest.main()
