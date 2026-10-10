#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
import copy
from pathlib import Path
import tempfile
import contextlib
import io
import json
import os
import subprocess
import sys
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


class GateCandidateInputTests(unittest.TestCase):
    def test_candidate_json_shape_refuses_without_tools_or_writes_and_keeps_valid_triage(self):
        with tempfile.TemporaryDirectory(prefix="plectis-gate-candidate-") as temporary:
            directory = Path(temporary)
            root = directory / "metadata root with spaces and 'quotes"
            root.mkdir()
            f.fixture(root)
            capsule = d.build(root, 249, f.COMMIT)
            decision_path = directory / "valid decision.json"
            decision_path.write_text(json.dumps(capsule), encoding="utf-8")
            before = {path.relative_to(root): path.read_bytes()
                      for path in root.rglob("*") if path.is_file()}
            before_nodes = {path.relative_to(root) for path in root.rglob("*")}
            cli = [sys.executable, *(["-O"] if sys.flags.optimize else []), b.__file__]
            bad = [("null", None, "candidate must be a JSON object"),
                   ("list", [], "candidate must be a JSON object"),
                   ("string", "text", "candidate must be a JSON object"),
                   ("number", 12, "candidate must be a JSON object"),
                   ("boolean", True, "candidate must be a JSON object"),
                   ("list kind", {"contribution": []}, "candidate needs an explicit contribution kind"),
                   ("object kind", {"contribution": {}}, "candidate needs an explicit contribution kind"),
                   ("empty object", {}, "candidate needs an explicit contribution kind")]
            good = [("registered statement", {"statement": "Target is open.", "contribution": "new_statement"},
                     "registered_text_not_a_new_statement"),
                    ("registered proof", {"statement": "Target is open.", "contribution": "new_proof"},
                     "proof_of_registered_statement_requires_verification"),
                    ("unknown statement", {"statement": "Unseen.", "contribution": "new_statement"},
                     "not_matched_in_selected_claims_unknown"),
                    ("representation", {"statement": "A useful view.", "contribution": "representation_gain"},
                     "requires_fixed_baseline_and_consumer_test")]
            cases = [(name, value, 2, message) for name, value, message in bad]
            cases += [("malformed JSON", "{", 2, "Expecting"),
                      ("missing request", None, 2, "No such file")]
            cases += [(name, value, 0, disposition) for name, value, disposition in good]
            for name, value, expected, message in cases:
                with self.subTest(name=name):
                    candidate = directory / f"{name} candidate with 'quotes.json"
                    if name != "missing request":
                        candidate.write_text("{" if name == "malformed JSON" else json.dumps(value), encoding="utf-8")
                    request_before = candidate.read_bytes() if candidate.exists() else None
                    arguments = ["--root", str(root), "gate", "--decision", str(decision_path),
                                 "--candidate", str(candidate)]
                    stdout, stderr = io.StringIO(), io.StringIO()
                    with mock.patch.object(sys, "argv", [b.__file__, *arguments]), \
                            mock.patch.object(b, "emit", side_effect=AssertionError("gate entered emit")), \
                            mock.patch.object(b, "replay", side_effect=AssertionError("gate entered replay")), \
                            mock.patch.object(b.probes, "run_probe", side_effect=AssertionError("gate ran Lean")), \
                            mock.patch.object(subprocess, "run", side_effect=AssertionError("gate started tool")), \
                            mock.patch.object(Path, "write_text", side_effect=AssertionError("gate wrote artifact")), \
                            mock.patch.object(Path, "write_bytes", side_effect=AssertionError("gate wrote artifact")), \
                            mock.patch.object(Path, "mkdir", side_effect=AssertionError("gate made directory")), \
                            contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                        self.assertEqual(b.main(), expected)
                    result = subprocess.run([*cli, *arguments], capture_output=True, text=True,
                                            env={**os.environ, "PATH": str(directory / "no tools"),
                                                 "PYTHONDONTWRITEBYTECODE": "1"})
                    self.assertEqual(result.returncode, expected, result.stderr)
                    if expected:
                        self.assertEqual(stdout.getvalue(), "")
                        self.assertEqual(result.stdout, "")
                        self.assertIn(message, stderr.getvalue())
                        self.assertIn(message, result.stderr)
                        self.assertIn("relation_binding:", result.stderr)
                        self.assertNotIn("Traceback", result.stderr)
                    else:
                        self.assertEqual(stderr.getvalue(), "")
                        self.assertEqual(result.stderr, "")
                        for output in (stdout.getvalue(), result.stdout):
                            triage = json.loads(output)
                            self.assertEqual(triage["disposition"], message)
                            self.assertFalse(triage["publication_admitted"])
                            self.assertEqual(triage["novelty"], "not_established")
                    self.assertEqual({path.relative_to(root): path.read_bytes()
                                      for path in root.rglob("*") if path.is_file()}, before)
                    self.assertEqual({path.relative_to(root) for path in root.rglob("*")}, before_nodes)
                    self.assertEqual(candidate.read_bytes() if candidate.exists() else None, request_before)
                    self.assertEqual(json.loads(decision_path.read_text()), capsule)


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


if __name__ == "__main__": unittest.main()
