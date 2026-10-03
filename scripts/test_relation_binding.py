#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
import contextlib
import copy
import io
import json
import os
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import relation_binding as b
import relation_registry as registry
import research_decision as d
import research_decision_test_support as f

ROW = {"id": "test", "relation": "endpoint_route", "problem": 249,
       "context": "fun _ : Unit => True", "left": "False", "right": "True",
       "certificate": {"module": "lean/Toy.lean", "declaration": "Toy.route", "signature_sha256": "a" * 64},
       "sources": [], "note": "synthetic generator fixture"}


class BindingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name); f.fixture(self.root)

    def emit(self, row=None):
        with mock.patch.object(registry, "check", return_value={"ok": True}), \
             mock.patch.object(registry, "load_registry", return_value={"rows": [row or ROW]}):
            return b.emit(self.root)

    def test_full_arguments_not_only_head(self):
        source, manifest = self.emit()
        self.assertIn("EndpointRoute (fun _ : Unit => True) (fun _ => False) (fun _ => True)", source)
        self.assertIn("Toy.route", source)
        self.assertEqual(manifest["state"], "generated_not_compiled")

    def test_mutating_endpoint_changes_obligation(self):
        row = copy.deepcopy(ROW); row["left"] = "True"
        s1, m1 = self.emit(); s2, m2 = self.emit(row)
        self.assertNotEqual(s1, s2); self.assertNotEqual(m1["source_sha256"], m2["source_sha256"])

    def test_mutating_scope_changes_obligation(self):
        row = copy.deepcopy(ROW); row["context"] = "fun _ : Unit => False"
        self.assertNotEqual(self.emit()[0], self.emit(row)[0])

    def test_annotated_context_is_expanded(self):
        row = copy.deepcopy(ROW); row["context"] = "Toy.Scope: fun n : Nat => 1 < n"
        row["left"] = "n > 0"
        source, _ = self.emit(row)
        self.assertIn("fun n : Nat => 1 < n", source)
        self.assertNotIn("(Toy.Scope)", source)

    def test_unsupported_context_refuses_not_guesses(self):
        row = copy.deepcopy(ROW); row["context"] = "the usual assumptions"
        with self.assertRaises(d.DecisionError): self.emit(row)

    def test_injected_multiline_refused(self):
        row = copy.deepcopy(ROW); row["left"] = "True\naxiom fake : False"
        with self.assertRaises(d.DecisionError): self.emit(row)

    def test_accept_bit_is_insufficient(self):
        source, manifest = self.emit()
        out = b.checked_result(self.root, source, manifest,
                               {"accepted": True, "source_sha256": manifest["source_sha256"], "axioms_printed": {}})
        self.assertEqual(out["state"], "rejected")

    def test_scoped_result_is_not_release(self):
        source, manifest = self.emit()
        out = b.checked_result(self.root, source, manifest, {"accepted": True,
            "source_sha256": manifest["source_sha256"], "axioms_printed": {"PlectisRelationBinding.binding_0": []}})
        self.assertEqual(out["state"], "binding_in_invoked_environment")
        self.assertFalse(out["release_authorization"])
        self.assertFalse(out["environment_replayed"])

    def test_new_source_after_emit_refuses_result(self):
        source, manifest = self.emit()
        result = {"accepted": True, "source_sha256": manifest["source_sha256"],
                  "axioms_printed": {"PlectisRelationBinding.binding_0": []}}
        for relative in ("lean/NewModule.lean", "scripts/new_adapter.py"):
            with self.subTest(relative=relative):
                path = self.root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("-- newly supplied input\n", encoding="utf-8")
                # Listed hashes still agree; inventory membership is the defect.
                d.verify_snapshot(self.root, manifest["snapshot"])
                with self.assertRaisesRegex(d.DecisionError, "binding source inventory changed"):
                    b.checked_result(self.root, source, manifest, result)
                path.unlink()

    def test_nonstandard_and_stale_probe_rejected(self):
        source, manifest = self.emit()
        out = b.checked_result(self.root, source, manifest, {"accepted": True,
            "source_sha256": "0" * 64, "axioms_printed": {"PlectisRelationBinding.binding_0": ["fake"]}})
        self.assertEqual(len(out["errors"]), 2)

    def test_global_registry_error_is_not_usable(self):
        with mock.patch.object(registry, "check", return_value={"ok": False, "errors": ["inconsistent"], "rows": [ROW]}):
            with self.assertRaises(registry.RegistryError): registry.usable_rows(self.root)

    def test_known_open_target_new_proof_not_discarded(self):
        c = d.build(self.root, 249, f.COMMIT)
        out = b.return_gate(self.root, c, {"statement": "Target is open.", "contribution": "new_proof"})
        self.assertEqual(out["disposition"], "proof_of_registered_statement_requires_verification")
        self.assertFalse(out["publication_admitted"])

    def test_unknown_is_not_novel(self):
        c = d.build(self.root, 249, f.COMMIT)
        out = b.return_gate(self.root, c, {"statement": "Unseen.", "contribution": "new_statement"})
        self.assertEqual(out["novelty"], "not_established")

    def test_registered_text_not_new_statement(self):
        c = d.build(self.root, 249, f.COMMIT)
        out = b.return_gate(self.root, c, {"statement": "Target is open.", "contribution": "new_statement"})
        self.assertEqual(out["disposition"], "registered_text_not_a_new_statement")

    def test_representation_gain_separate(self):
        c = d.build(self.root, 249, f.COMMIT)
        out = b.return_gate(self.root, c, {"statement": "A useful view.", "contribution": "representation_gain"})
        self.assertEqual(out["disposition"], "requires_fixed_baseline_and_consumer_test")


class EmitOutputTests(unittest.TestCase):
    def test_known_output_collisions_preserve_all_bytes_before_generation(self):
        with tempfile.TemporaryDirectory(prefix="plectis-binding-output-") as temporary:
            directory = Path(temporary)
            source_root = directory / "metadata root"
            source_root.mkdir()
            fixture_row = copy.deepcopy(ROW)
            fixture_row["sources"] = [{"declaration": "Toy.route", "module": "lean/Toy.lean"}]
            f.write(source_root, registry.REGISTRY_PATH, {
                "schema": registry.SCHEMA, "boundary": "synthetic output fixture only", "rows": [fixture_row],
            })
            f.write(source_root, registry.ATLAS_PATH, {"declarations": []})
            toy = source_root / "lean/Toy.lean"
            toy.parent.mkdir()
            toy.write_text("namespace Toy\ntheorem route : True := by trivial\nend Toy\n", encoding="utf-8")
            source_before = {path.relative_to(source_root): path.read_bytes()
                             for path in source_root.rglob("*") if path.is_file()}
            cli = [sys.executable]
            if sys.flags.optimize:
                cli.append("-O")
            cli.append(b.__file__)
            kinds = ["directory", "symlink", "broken symlink"]
            if hasattr(os, "mkfifo"):
                kinds.append("fifo")
            for filename in ("RelationBindings.lean", "manifest.json"):
                for kind in kinds:
                    with self.subTest(filename=filename, kind=kind):
                        out = directory / f"output {filename} {kind} with 'quotes"
                        out.mkdir()
                        other = out / ("manifest.json" if filename == "RelationBindings.lean" else "RelationBindings.lean")
                        other_bytes = b"prior contributor output\n"
                        other.write_bytes(other_bytes)
                        notes = out / "notes.txt"
                        notes.write_bytes(b"unrelated contributor notes\n")
                        external = directory / "outside contributor material.json"
                        external.write_bytes(b"outside contributor material\n")
                        collision = out / filename
                        nested_notes = None
                        if kind == "directory":
                            collision.mkdir()
                            nested_notes = collision / "foreign.txt"
                            nested_notes.write_bytes(b"nested foreign material\n")
                        elif kind == "symlink":
                            collision.symlink_to(external)
                        elif kind == "broken symlink":
                            collision.symlink_to(directory / "absent external target")
                        else:
                            os.mkfifo(collision)
                        mode_before = collision.lstat().st_mode
                        link_before = collision.readlink() if collision.is_symlink() else None
                        arguments = ["--root", str(source_root), "emit", "--out", str(out)]
                        stdout, stderr = io.StringIO(), io.StringIO()
                        with mock.patch.object(sys, "argv", [b.__file__, *arguments]), \
                                mock.patch.object(b, "emit", side_effect=AssertionError("invalid output started generation")), \
                                mock.patch.object(Path, "write_text", side_effect=AssertionError("invalid output wrote artifact")), \
                                mock.patch.object(Path, "mkdir", side_effect=AssertionError("invalid output made directory")), \
                                contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                            self.assertEqual(b.main(), 2)
                        self.assertEqual(stdout.getvalue(), "")
                        self.assertIn("refuse symlink or nonregular output", stderr.getvalue())
                        result = subprocess.run([*cli, *arguments], cwd=source_root,
                                                capture_output=True, text=True, check=False)
                        self.assertEqual(result.returncode, 2, result.stderr)
                        self.assertEqual(result.stdout, "")
                        self.assertIn("refuse symlink or nonregular output", result.stderr)
                        self.assertNotIn("Traceback", result.stderr)
                        self.assertEqual(other.read_bytes(), other_bytes)
                        self.assertEqual(notes.read_bytes(), b"unrelated contributor notes\n")
                        self.assertEqual(external.read_bytes(), b"outside contributor material\n")
                        self.assertEqual(collision.lstat().st_mode, mode_before)
                        if link_before is not None:
                            self.assertEqual(collision.readlink(), link_before)
                        if nested_notes is not None:
                            self.assertEqual(nested_notes.read_bytes(), b"nested foreign material\n")
                        self.assertEqual(set(path.name for path in out.iterdir()),
                                         {"RelationBindings.lean", "manifest.json", "notes.txt"})
                        self.assertFalse((directory / "absent external target").exists())
            # Normal generation remains supported, including regular-file refresh
            # without touching unrelated content in the selected directory.
            out = directory / "clean output with spaces and 'quotes"
            arguments = ["--root", str(source_root), "emit", "--out", str(out)]
            result = subprocess.run([*cli, *arguments], cwd=source_root,
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)["state"], "generated_not_compiled")
            original = {name: (out / name).read_bytes() for name in ("RelationBindings.lean", "manifest.json")}
            notes = out / "notes.txt"
            notes.write_bytes(b"keep notes on regeneration\n")
            for name in original:
                (out / name).write_bytes(b"old regular generated artifact\n")
            result = subprocess.run([*cli, *arguments], cwd=source_root,
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual({name: (out / name).read_bytes() for name in original}, original)
            self.assertEqual(notes.read_bytes(), b"keep notes on regeneration\n")
            self.assertEqual({path.relative_to(source_root): path.read_bytes()
                              for path in source_root.rglob("*") if path.is_file()}, source_before)


if __name__ == "__main__": unittest.main()
