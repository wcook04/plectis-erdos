#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
import contextlib
import copy
import hashlib
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
    def test_hardlinked_selected_pair_refuses_before_generation(self):
        with tempfile.TemporaryDirectory(prefix="plectis-binding-alias-") as temporary:
            directory = Path(temporary)
            cli = [sys.executable, *(["-O"] if sys.flags.optimize else []), b.__file__]
            for original in ("RelationBindings.lean", "manifest.json"):
                with self.subTest(original=original):
                    out = directory / f"output {original} with spaces and 'quotes"
                    out.mkdir()
                    first = out / original
                    second = out / ("manifest.json" if original == "RelationBindings.lean" else "RelationBindings.lean")
                    first.write_bytes(b"prior shared selected output\n")
                    os.link(first, second)
                    notes = out / "notes.txt"
                    notes.write_bytes(b"unrelated notes\n")
                    before = {path: (path.read_bytes(), path.stat()) for path in (first, second, notes)}
                    arguments = ["--root", str(directory / "absent metadata root"), "emit", "--out", str(out)]
                    stdout, stderr = io.StringIO(), io.StringIO()
                    with mock.patch.object(sys, "argv", [b.__file__, *arguments]), \
                            mock.patch.object(b, "emit", side_effect=AssertionError("aliased pair started generation")), \
                            mock.patch.object(b.probes, "run_probe", side_effect=AssertionError("emit ran Lean")), \
                            contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                        self.assertEqual(b.main(), 2)
                    self.assertEqual(stdout.getvalue(), "")
                    self.assertIn("refuse aliased selected outputs", stderr.getvalue())
                    result = subprocess.run([*cli, *arguments], capture_output=True, text=True,
                                            env={**os.environ, "PATH": str(directory / "no tools")})
                    self.assertEqual(result.returncode, 2, result.stderr)
                    self.assertEqual(result.stdout, "")
                    self.assertIn("refuse aliased selected outputs", result.stderr)
                    self.assertNotIn("Traceback", result.stderr)
                    for path, (content, info) in before.items():
                        self.assertEqual(path.read_bytes(), content)
                        current = path.stat()
                        self.assertEqual((current.st_dev, current.st_ino, current.st_mode),
                                         (info.st_dev, info.st_ino, info.st_mode))
                    self.assertTrue(first.samefile(second))
                    self.assertEqual({path.name for path in out.iterdir()},
                                     {"RelationBindings.lean", "manifest.json", "notes.txt"})

    def test_acquired_handles_refuse_alias_introduced_after_path_preflight(self):
        with tempfile.TemporaryDirectory(prefix="plectis-binding-alias-race-") as temporary:
            first, second = (Path(temporary) / name for name in ("RelationBindings.lean", "manifest.json"))
            first.write_bytes(b"prior source\n")
            second.write_bytes(b"prior manifest\n")
            original = first.stat()
            real_open = os.open

            def replace_second(path, flags, *args, **kwargs):
                if Path(path) == second:
                    second.unlink()
                    os.link(first, second)
                return real_open(path, flags, *args, **kwargs)

            with mock.patch.object(b.os, "open", side_effect=replace_second):
                with self.assertRaisesRegex(d.DecisionError, "refuse aliased selected outputs"):
                    b._write_outputs({first: "new source", second: "new manifest"})
            self.assertEqual(first.read_bytes(), b"prior source\n")
            self.assertEqual(second.read_bytes(), b"prior source\n")
            self.assertTrue(first.samefile(second))
            self.assertEqual((first.stat().st_dev, first.stat().st_ino), (original.st_dev, original.st_ino))

    def test_readonly_regular_outputs_refuse_before_changing_the_pair(self):
        if hasattr(os, "geteuid") and os.geteuid() == 0:
            self.skipTest("root bypasses ordinary readonly file permissions")
        with tempfile.TemporaryDirectory(prefix="plectis-binding-readonly-") as temporary:
            directory = Path(temporary)
            root = directory / "metadata root with spaces and 'quotes"
            root.mkdir()
            row = copy.deepcopy(ROW)
            row["sources"] = [{"declaration": "Toy.route", "module": "lean/Toy.lean"}]
            document = {"schema": registry.SCHEMA, "boundary": "metadata only", "rows": [row]}
            f.write(root, registry.REGISTRY_PATH, document)
            f.write(root, registry.ATLAS_PATH, {"declarations": []})
            toy = root / "lean/Toy.lean"
            toy.parent.mkdir()
            toy.write_text("namespace Toy\ntheorem route : True := by trivial\nend Toy\n")
            cli = [sys.executable, *(["-O"] if sys.flags.optimize else []), b.__file__]
            for filename, fresh_first in (("RelationBindings.lean", False),
                                          ("manifest.json", False), ("manifest.json", True)):
                with self.subTest(filename=filename, fresh_first=fresh_first):
                    out = directory / f"output {filename} {fresh_first} with 'quotes"
                    arguments = ["--root", str(root), "emit", "--out", str(out)]
                    result = subprocess.run([*cli, *arguments], capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    source = out / "RelationBindings.lean"
                    manifest = out / "manifest.json"
                    self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), json.loads(manifest.read_text())["source_sha256"])
                    row["note"] += " changed row digest"
                    f.write(root, registry.REGISTRY_PATH, document)
                    notes = out / "notes.txt"
                    notes.write_bytes(b"unrelated contributor notes\n")
                    if fresh_first:
                        source.unlink()
                    readonly = out / filename
                    readonly.chmod(0o444)
                    existing = [path for path in (source, manifest, notes) if path.exists()]
                    before = {path: (path.read_bytes(), path.stat()) for path in existing}
                    # The in-process journey uses real permissions and refuses any
                    # attempt to enter the Lean/probe lane; the child is also real.
                    stdout, stderr = io.StringIO(), io.StringIO()
                    with mock.patch.object(sys, "argv", [b.__file__, *arguments]), \
                            mock.patch.object(b, "replay", side_effect=AssertionError("emit entered replay")), \
                            mock.patch.object(b.probes, "run_probe", side_effect=AssertionError("emit ran Lean")), \
                            contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                        self.assertEqual(b.main(), 2)
                    self.assertEqual(stdout.getvalue(), "")
                    self.assertIn("Permission denied", stderr.getvalue())
                    result = subprocess.run([*cli, *arguments], capture_output=True, text=True,
                                            env={**os.environ, "PATH": str(directory / "no tools")})
                    self.assertEqual(result.returncode, 2, result.stderr)
                    self.assertEqual(result.stdout, "")
                    self.assertIn("Permission denied", result.stderr)
                    self.assertNotIn("Traceback", result.stderr)
                    for path, (content, info) in before.items():
                        self.assertEqual(path.read_bytes(), content)
                        current = path.stat()
                        self.assertEqual((current.st_dev, current.st_ino, current.st_mode),
                                         (info.st_dev, info.st_ino, info.st_mode))
                    self.assertEqual({path.name for path in out.iterdir()}, {path.name for path in existing})
                    if fresh_first:
                        self.assertFalse(source.exists())
                    readonly.chmod(0o644)
                    # Restoring permission allows real regeneration without replacing
                    # existing regular-file identities or touching contributor notes.
                    result = subprocess.run([*cli, *arguments], capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), json.loads(manifest.read_text())["source_sha256"])
                    self.assertEqual(notes.read_bytes(), b"unrelated contributor notes\n")
                    for path, (_, info) in before.items():
                        current = path.stat()
                        self.assertEqual((current.st_dev, current.st_ino), (info.st_dev, info.st_ino))

    def test_fdopen_failure_cleans_new_empty_outputs_and_preserves_existing(self):
        with tempfile.TemporaryDirectory(prefix="plectis-binding-fdopen-") as temporary:
            for existing_first in (False, True):
                with self.subTest(existing_first=existing_first):
                    out = Path(temporary) / str(existing_first)
                    out.mkdir()
                    first, second = out / "RelationBindings.lean", out / "manifest.json"
                    if existing_first:
                        first.write_bytes(b"preexisting source\n")
                        before = first.stat()
                    real_fdopen = os.fdopen
                    calls = 0

                    def fail_second(*args, **kwargs):
                        nonlocal calls
                        calls += 1
                        if calls == 2:
                            raise OSError("controlled second fdopen failure")
                        return real_fdopen(*args, **kwargs)

                    with mock.patch.object(b.os, "fdopen", side_effect=fail_second):
                        with self.assertRaisesRegex(OSError, "controlled second fdopen failure"):
                            b._write_outputs({first: "new source", second: "new manifest"})
                    self.assertFalse(second.exists())
                    if existing_first:
                        self.assertEqual(first.read_bytes(), b"preexisting source\n")
                        current = first.stat()
                        self.assertEqual((current.st_dev, current.st_ino, current.st_mode),
                                         (before.st_dev, before.st_ino, before.st_mode))
                    else:
                        self.assertFalse(first.exists())
                    self.assertEqual({path.name for path in out.iterdir()},
                                     {"RelationBindings.lean"} if existing_first else set())

    def test_failed_new_pair_acquisition_removes_only_unchanged_owned_empty_file(self):
        with tempfile.TemporaryDirectory(prefix="plectis-binding-acquire-") as temporary:
            for modification in ("none", "content", "replacement"):
                with self.subTest(modification=modification):
                    out = Path(temporary) / modification
                    out.mkdir()
                    first, second = out / "RelationBindings.lean", out / "manifest.json"
                    real_open = os.open

                    def fail_second(path, flags, *args, **kwargs):
                        if Path(path) == second and flags & os.O_CREAT:
                            if modification == "content":
                                first.write_bytes(b"concurrent contributor content")
                            elif modification == "replacement":
                                first.unlink()
                                first.symlink_to(out / "outside")
                            raise PermissionError("second creation refused")
                        return real_open(path, flags, *args, **kwargs)

                    with mock.patch.object(b.os, "open", side_effect=fail_second):
                        with self.assertRaisesRegex(PermissionError, "second creation refused"):
                            b._write_outputs({first: "source", second: "manifest"})
                    self.assertFalse(second.exists())
                    if modification == "none":
                        self.assertFalse(first.exists())
                    elif modification == "content":
                        self.assertEqual(first.read_bytes(), b"concurrent contributor content")
                    else:
                        self.assertTrue(first.is_symlink())
                        self.assertEqual(first.readlink(), out / "outside")

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
