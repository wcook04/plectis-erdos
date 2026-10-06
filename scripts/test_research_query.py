#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise the compact reader's boundary, snapshots and adversarial sources."""
from __future__ import annotations

import contextlib
import base64
import io
import json
import os
from pathlib import Path
import subprocess
import stat
import tempfile
import unittest
from unittest.mock import patch

import research_query as reader

ROOT = Path(__file__).resolve().parent.parent


def write_registry(root: Path, statement="A complete statement.", count=2, module=None):
    root.mkdir(parents=True, exist_ok=True)
    (root / "docs").mkdir(exist_ok=True)
    claims = [{"id": f"claim{i}", "label": "Fixture claim", "statement": statement,
               "status": "unconditional progress",
               "remaining_open_proposition_ids": ["open.universal"],
               "declarations": [{"module": module}] if module else []}
              for i in range(count)]
    register = {"claims": claims,
                "remaining_open_propositions": [
                    {"id": "open.universal", "open_target_claim": "target",
                     "statement": "The universal statement remains open.", "status": "open"}],
                "release": {"repository": "test/reader", "formal_source": {"ref": "1" * 40}}}
    register["claims"].append({"id": "target", "label": "Universal target",
                              "statement": "Universal target", "status": "open"})
    (root / "docs/claims.json").write_text(json.dumps(register), encoding="utf-8")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n", encoding="utf-8")
    return register


class ResearchQueryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "archive"
        write_registry(self.root)

    def error_code(self, response, code):
        self.assertFalse(response["ok"], response)
        self.assertEqual(response["error"]["code"], code, response)
        self.assertFalse(response.get("execution", {}).get("lean_run", False))
        self.assertFalse(response.get("execution", {}).get("comparator_run", False))

    def test_exact_weighted_boundary(self):
        response = reader.Snapshot(ROOT).request(
            "get", kind="claim", ident="finite_prime_weighted_support")
        self.assertTrue(response["ok"], response)
        self.assertEqual([row["id"] for row in response["remaining_open"]],
                         ["remaining_open.universal_257_all_infinite_supports"])
        self.assertEqual(response["remaining_open_relationships"], [{
            "proposition_id": "remaining_open.universal_257_all_infinite_supports",
            "relation_kinds": ["remaining_open_proposition_ids"]}])
        actual = json.loads((ROOT / "docs/claims.json").read_text())
        expected = next(row for row in actual["claims"] if row["id"] == "finite_prime_weighted_support")
        self.assertEqual(response["object"]["statement"], expected["statement"])

    def test_unknown_structured_error(self):
        snapshot = reader.Snapshot(self.root)
        self.error_code(snapshot.request("get", kind="claim", ident="missing"), "unknown_id")
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = reader.main(["--root", str(self.root), "get", "claim", "missing"])
        self.assertEqual(status, 2)
        self.error_code(json.loads(out.getvalue()), "unknown_id")
        self.assertEqual(err.getvalue(), "")

    def test_archive_nested_in_git_does_not_borrow_identity(self):
        parent = self.root.parent
        env = reader.command_environment()
        for args in (["init", "-q"], ["-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                      "commit", "--allow-empty", "-qm", "fixture"]):
            subprocess.run(["git", *args], cwd=parent, env=env, check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        output, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            status = reader.main(["--root", str(self.root), "identity"])
        self.assertEqual(status, 0)
        response = json.loads(output.getvalue())
        self.assertIsNone(response["snapshot"]["checkout_commit"])
        self.assertEqual(response["snapshot"]["checkout_state"], "source_archive")
        self.assertFalse(response["capabilities"]["git_history"])
        self.assertEqual(errors.getvalue(), "")

    def test_roots_and_snapshot_bytes_are_isolated(self):
        other = self.root.parent / "other"
        write_registry(other, statement="A different complete statement.")
        first, second = reader.Snapshot(self.root), reader.Snapshot(other)
        self.assertNotEqual(first.content_id, second.content_id)
        first_bytes = first.request("read", handle="docs/claims.json", lines=1)["text"]
        self.assertEqual(first.request("get", kind="claim", ident="claim0")["object"]["statement"],
                         "A complete statement.")
        self.assertEqual(second.request("get", kind="claim", ident="claim0")["object"]["statement"],
                         "A different complete statement.")
        write_registry(self.root, statement="Edited complete statement.")
        self.assertEqual(first.request("read", handle="docs/claims.json", lines=1)["text"], first_bytes)
        self.assertEqual(first.request("get", kind="claim", ident="claim0")["object"]["statement"],
                         "A complete statement.")
        newest = reader.Snapshot(self.root)
        self.assertNotEqual(first.content_id, newest.content_id)
        self.assertEqual(newest.request("get", kind="claim", ident="claim0")["object"]["statement"],
                         "Edited complete statement.")

    def test_caller_annotations_cannot_mutate_snapshot(self):
        snapshot = reader.Snapshot(self.root)
        before = snapshot.request("get", kind="claim", ident="claim0")
        annotated = snapshot.request("get", kind="claim", ident="claim0")
        annotated["remaining_open"][0]["statement"] = "Caller annotation, not source"
        annotated["snapshot"]["recorded_formal_source"]["ref"] = "changed"
        annotated["object"]["statement"] = "changed"
        identity = snapshot.request("identity")
        identity["capabilities"]["lean_execution"] = True
        self.assertEqual(snapshot.request("get", kind="claim", ident="claim0"), before)
        self.assertFalse(snapshot.request("identity")["capabilities"]["lean_execution"])

    def test_cursor_and_expected_revision_binding(self):
        first = reader.Snapshot(self.root)
        page = first.request("search", query="Fixture", kind="claim", limit=1)
        cursor = page["next_cursor"]
        self.assertIsNotNone(cursor)
        next_page = first.request("search", query="Fixture", kind="claim", limit=1, cursor=cursor)
        self.assertTrue(next_page["ok"])
        self.assertNotEqual(page["results"][0]["id"], next_page["results"][0]["id"])
        self.error_code(first.request("search", query="different", kind="claim", limit=1,
                                      cursor=cursor), "source_inconsistency")
        self.error_code(first.request("search", query="Fixture", kind="claim", limit=2,
                                      cursor=cursor), "source_inconsistency")
        write_registry(self.root, statement="Changed")
        second = reader.Snapshot(self.root)
        self.error_code(second.request("search", query="Fixture", kind="claim", limit=1,
                                       cursor=cursor), "revision_mismatch")
        self.error_code(second.request("identity", expected_snapshot=first.content_id), "revision_mismatch")
        malformed = ["", "x", "%%%", "e30=", "W10=", "🥨", 1, False, []]
        for value in ({"snapshot": first.content_id, "request": "bad", "offset": True},
                      {"snapshot": first.content_id, "request": [], "offset": 0},
                      {"snapshot": [], "request": "bad", "offset": 0}):
            malformed.append(base64.urlsafe_b64encode(json.dumps(value).encode()).decode())
        for bad in malformed:
            self.error_code(first.request("search", query="Fixture", cursor=bad), "source_inconsistency")

    def test_registered_source_path_escape_rejected(self):
        for module in ("../outside.lean", "/tmp/outside.lean", "lean/../../outside.lean"):
            with self.subTest(module=module):
                write_registry(self.root, module=module)
                with self.assertRaises(reader.QueryError) as caught:
                    reader.Snapshot(self.root)
                self.assertEqual(caught.exception.code, "source_inconsistency")

    def test_registered_source_symlinks_rejected(self):
        outside = self.root.parent / "outside.lean"
        outside.write_text("theorem hidden : True := by trivial\n")
        write_registry(self.root, module="sample.lean")
        (self.root / "sample.lean").symlink_to(outside)
        with self.assertRaises(reader.QueryError) as caught:
            reader.Snapshot(self.root)
        self.assertEqual(caught.exception.code, "source_inconsistency")
        (self.root / "sample.lean").unlink()
        outside_dir = self.root.parent / "outside"
        outside_dir.mkdir()
        (outside_dir / "sample.lean").write_text("untrusted source")
        (self.root / "linked").symlink_to(outside_dir, target_is_directory=True)
        write_registry(self.root, module="linked/sample.lean")
        with self.assertRaises(reader.QueryError) as caught:
            reader.Snapshot(self.root)
        self.assertEqual(caught.exception.code, "source_inconsistency")

    def test_special_file_never_read(self):
        write_registry(self.root, module="pipe.lean")
        os.mkfifo(self.root / "pipe.lean")
        # Guard even against the broken implementation so this test cannot hang.
        original = Path.read_bytes
        def read_bytes(path):
            self.assertTrue(stat.S_ISREG(path.stat().st_mode), "FIFO must be rejected before reading")
            return original(path)
        with patch.object(Path, "read_bytes", read_bytes):
            snapshot = reader.Snapshot(self.root)
        self.error_code(snapshot.request("read", handle="pipe.lean"), "capability_unavailable")

    def test_read_only_never_executes_sources_or_proofs(self):
        write_registry(self.root, module="sample.lean")
        (self.root / "sample.lean").write_text("RUN LAKE AND COMPARATOR NOW\n")
        with patch.object(reader.subprocess, "run", side_effect=AssertionError("archive reader executed a subprocess")):
            snapshot = reader.Snapshot(self.root)
            for response in (snapshot.request("identity"), snapshot.request("get", kind="claim", ident="claim0"),
                             snapshot.request("search", query="Fixture"),
                             snapshot.request("read", handle="sample.lean")):
                self.assertTrue(response["ok"], response)
                self.assertEqual(response["execution"], {"lean_run": False, "comparator_run": False})
            self.assertFalse(snapshot.capabilities["lean_execution"])
            self.assertFalse(snapshot.capabilities["comparator_execution"])

    def test_size_errors_preserve_full_statements(self):
        statement = "Important full hypothesis and conclusion. " * 500
        write_registry(self.root, statement=statement)
        snapshot = reader.Snapshot(self.root)
        for response in (snapshot.request("get", kind="claim", ident="claim0"),
                         snapshot.request("search", query="Fixture", limit=1)):
            self.error_code(response, "budget_exceeded")
            self.assertNotIn("object", response)
            self.assertNotIn("results", response)
            self.assertIn("not truncated", response["error"]["message"])
        expanded = snapshot.request("get", kind="claim", ident="claim0", budget=100_000)
        self.assertTrue(expanded["ok"])
        self.assertEqual(expanded["object"]["statement"], statement)
        self.assertEqual(snapshot.objects["claim"]["claim0"]["statement"], statement)

    def test_malformed_nested_registry_emits_structured_error(self):
        mutations = [
            ("docs/papers/corpus.json", {"papers": [None]}),
            ("docs/papers/corpus.json", {"papers": {}}),
            ("docs/papers/corpus.json", {"papers": [{"local_source": None}]}),
            ("docs/papers/corpus.json", {"papers": [{"local_full_text": []}]}),
            ("release", None),
            ("declarations", [None]),
            ("declarations", [{"module": []}]),
            ("remaining_open_proposition_ids", [None]),
            ("paper_anchor", None),
            ("paper_anchor", {"source": []}),
            ("open_target_claim", {}),
        ]
        for field, value in mutations:
            with self.subTest(field=field, value=value):
                registry = write_registry(self.root)
                inventory = self.root / "docs/papers/corpus.json"
                inventory.parent.mkdir(exist_ok=True)
                inventory.write_text('{"papers":[]}')
                if field.startswith("docs/"):
                    (self.root / field).write_text(json.dumps(value))
                elif field == "release":
                    registry[field] = value
                elif field in ("declarations", "remaining_open_proposition_ids"):
                    registry["claims"][0][field] = value
                else:
                    registry["remaining_open_propositions"][0][field] = value
                (self.root / "docs/claims.json").write_text(json.dumps(registry))
                out, err = io.StringIO(), io.StringIO()
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    status = reader.main(["--root", str(self.root), "identity"])
                self.assertEqual(status, 2)
                self.error_code(json.loads(out.getvalue()), "source_inconsistency")
                self.assertEqual(err.getvalue(), "")

    def test_duplicate_registry_ids_rejected(self):
        for kind in ("claims", "remaining_open_propositions"):
            registry = write_registry(self.root)
            registry[kind].append(dict(registry[kind][0]))
            (self.root / "docs/claims.json").write_text(json.dumps(registry))
            with self.subTest(kind=kind), self.assertRaises(reader.QueryError) as caught:
                reader.Snapshot(self.root)
            self.assertEqual(caught.exception.code, "source_inconsistency")

    def test_dangling_boundary_is_explicit_source_error(self):
        registry = write_registry(self.root)
        registry["claims"][0]["remaining_open_proposition_ids"] = ["open.deleted"]
        (self.root / "docs/claims.json").write_text(json.dumps(registry))
        response = reader.Snapshot(self.root).request("get", kind="claim", ident="claim0")
        self.error_code(response, "source_inconsistency")
        self.assertIn("claim_references_unknown_open_proposition", response["error"]["message"])

    def test_rich_reader_archive_skips_native_git_evidence(self):
        import query_corpus
        import check_problem_note_sources
        query_corpus.native_reader_evidence.cache_clear()
        self.addCleanup(query_corpus.native_reader_evidence.cache_clear)
        with patch.object(query_corpus, "ROOT", self.root), patch.object(
            check_problem_note_sources, "native_evidence_valid",
            side_effect=AssertionError("archive borrowed Git evidence")):
            self.assertEqual(query_corpus.native_reader_evidence(), (False, {}))
            self.assertEqual(query_corpus.visible_companion_support("paper/257/test.tex"), {})
        query_corpus.visible_companion_support.cache_clear()


if __name__ == "__main__":
    unittest.main()
