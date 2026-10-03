#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
import contextlib
import copy
import io
import json
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import research_decision as d
import research_decision_test_support as f


class DecisionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name); f.fixture(self.root)

    def build(self, **kwargs):
        return d.build(self.root, 249, f.COMMIT, **kwargs)

    def test_explicit_endpoint_not_status_ranking(self):
        c = self.build()
        self.assertIn("good_index_endpoint", [x["id"] for x in c["claims"]])
        self.assertNotIn("unlinked_general_tool", [x["id"] for x in c["claims"]])
        self.assertEqual(c["selection"]["unselected_claim_count"], 1)
        self.assertIn("not mathematical strength", c["selection"]["order"])

    def test_missing_optional_is_explicit(self):
        c = self.build()
        self.assertIn("docs/orientation.json", c["capabilities"]["route_memory"]["missing"])
        self.assertFalse(c["capabilities"]["route_memory"]["execution_tested"])

    def test_missing_required_refuses(self):
        (self.root / d.CLAIMS).unlink()
        with self.assertRaises(d.DecisionError): self.build()

    def test_no_silent_budget_truncation(self):
        with self.assertRaisesRegex(d.DecisionError, "byte budget"): self.build(byte_budget=100)

    def test_stale_claim_and_appearing_optional_refused(self):
        c = self.build(); (self.root / "docs/orientation.json").write_text("{}")
        with self.assertRaisesRegex(d.DecisionError, "stale"): d.check_decision(self.root, c)

    def test_nonobject_refuses_before_snapshot_or_tools(self):
        for value in (None, [], [1], "decision", 3, True):
            with self.subTest(value=value), \
                    mock.patch.object(d, "verify_snapshot", side_effect=AssertionError("invalid decision read snapshot")), \
                    mock.patch.object(d, "build", side_effect=AssertionError("invalid decision rebuilt sources")), \
                    mock.patch.object(Path, "read_bytes", side_effect=AssertionError("invalid decision read artifact")), \
                    mock.patch.object(subprocess, "run", side_effect=AssertionError("invalid decision ran tool")):
                with self.assertRaisesRegex(d.DecisionError, "decision must be a JSON object"):
                    d.check_decision(self.root, value)

    def test_valid_decision_still_checks_source(self):
        capsule = self.build()
        original = copy.deepcopy(capsule)
        d.check_decision(self.root, capsule)
        self.assertEqual(capsule, original)
        with self.assertRaisesRegex(d.DecisionError, "decision identity mismatch"):
            d.check_decision(self.root, {})

    def test_digest_tamper(self):
        c = self.build(); c["programme"]["statement"] = "Solved."
        with self.assertRaisesRegex(d.DecisionError, "identity"): d.check_decision(self.root, c)

    def test_rehashing_forged_capsule_does_not_bind_to_source(self):
        c = self.build(); c["programme"]["statement"] = "Solved."
        c["decision_sha256"] = d.digest({k: v for k, v in c.items() if k != "decision_sha256"})
        with self.assertRaisesRegex(d.DecisionError, "projection differs"):
            d.check_decision(self.root, c)

    def test_symlink_and_traversal(self):
        for path in ("../outside", "/etc/passwd", "a\\b"):
            with self.assertRaises(d.DecisionError): d.safe_path(self.root, path)
        (self.root / "link").symlink_to(self.root / "baseline.txt")
        with self.assertRaises(d.DecisionError): d.snapshot(self.root, ["link"])

    def test_registry_global_error_refuses(self):
        with mock.patch.object(d.relation_registry, "check", return_value={"ok": False, "errors": ["contradiction"]}):
            with self.assertRaisesRegex(d.DecisionError, "contradiction"): self.build()

    def test_graph_local_filename_not_revision(self):
        p = self.root / "graph.json"
        p.write_text(json.dumps({"source": {"source_revision": "/producer/local/revision.txt", "lean_tree": "b" * 40}}))
        with self.assertRaisesRegex(d.DecisionError, "graph source mismatch"):
            d.graph_check(p, source_commit=f.COMMIT, lean_tree="b" * 40, assumptions=[])

    def test_graph_reuses_native_owners(self):
        p = self.root / "graph.json"
        p.write_text(json.dumps({"source": {"source_revision": f.COMMIT, "lean_tree": "b" * 40}}))
        import build_argument_continuations as graph
        import argument_graph_frontier as frontier
        with mock.patch.object(graph.Graph, "from_payload", return_value=object()) as make_graph, \
             mock.patch.object(frontier, "Frontier") as native:
            native.return_value.check.return_value = {"status": "unknown_budget"}
            out = d.graph_check(p, source_commit=f.COMMIT, lean_tree="b" * 40, assumptions=["A"], target="G")
            make_graph.assert_called_once(); native.return_value.check.assert_called_once_with(["A"], target="G")
            self.assertEqual(out["result"]["status"], "unknown_budget")

    def test_new_lean_file_invalidates_inventory(self):
        c = self.build()
        (self.root / "lean").mkdir()
        (self.root / "lean/New.lean").write_text("theorem added : True := trivial")
        with self.assertRaisesRegex(d.DecisionError, "inventory"):
            d.check_decision(self.root, c)

    def test_deterministic(self):
        self.assertEqual(self.build(), self.build())

    def test_bad_commit_and_problem(self):
        with self.assertRaises(d.DecisionError): d.build(self.root, True, f.COMMIT)
        with self.assertRaises(d.DecisionError): d.build(self.root, 249, "HEAD")


class DecisionInputCLITests(unittest.TestCase):
    def test_both_explicit_public_callers_refuse_nonobjects_without_artifacts(self):
        import research_episode as episode
        import relation_binding as binding
        import research_record as record

        with tempfile.TemporaryDirectory(prefix="plectis-decision-shape-") as temporary:
            directory = Path(temporary)
            root = directory / "metadata root with spaces and 'quotes"
            root.mkdir()
            foreign = root / "contributor notes.txt"
            foreign.write_bytes(b"keep existing material\n")
            inputs = directory / "input files"
            inputs.mkdir()
            candidate = inputs / "candidate.json"
            candidate.write_text("{}", encoding="utf-8")
            cli = [sys.executable]
            if sys.flags.optimize:
                cli.append("-O")
            for value in (None, [], [1], "decision", 3, True, {}):
                request = inputs / "decision file with spaces.json"
                payload = json.dumps(value).encode("utf-8")
                request.write_bytes(payload)
                expected = "decision identity mismatch" if isinstance(value, dict) else "decision must be a JSON object"
                callers = [
                    (episode, ["--root", str(root), "plan", "--decision", str(request),
                               "--contract", "contract.json", "--producer", "round-test"]),
                    (binding, ["--root", str(root), "gate", "--decision", str(request),
                               "--candidate", str(candidate)]),
                ]
                for module, arguments in callers:
                    with self.subTest(caller=module.__name__, value=value):
                        stdout, stderr = io.StringIO(), io.StringIO()
                        with mock.patch.object(sys, "argv", [module.__file__, *arguments]), \
                                mock.patch.object(d, "verify_snapshot", side_effect=AssertionError("invalid decision read snapshot")), \
                                mock.patch.object(d, "build", side_effect=AssertionError("invalid decision rebuilt sources")), \
                                mock.patch.object(record, "append_batch", side_effect=AssertionError("invalid decision wrote journal")), \
                                mock.patch.object(Path, "write_bytes", side_effect=AssertionError("invalid decision wrote artifact")), \
                                mock.patch.object(Path, "write_text", side_effect=AssertionError("invalid decision wrote artifact")), \
                                mock.patch.object(Path, "mkdir", side_effect=AssertionError("invalid decision created directory")), \
                                mock.patch.object(subprocess, "run", side_effect=AssertionError("invalid decision ran tool")), \
                                contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                            self.assertEqual(module.main(), 2)
                        self.assertEqual(stdout.getvalue(), "")
                        self.assertIn(expected, stderr.getvalue())
                        self.assertNotIn("Traceback", stderr.getvalue())
                        output = directory / "output packet with spaces and 'quotes.json"
                        with output.open("w", encoding="utf-8") as handle:
                            result = subprocess.run(
                                [*cli, module.__file__, *arguments], cwd=root,
                                stdout=handle, stderr=subprocess.PIPE, text=True, check=False,
                            )
                        self.assertEqual(result.returncode, 2, result.stderr)
                        self.assertEqual(output.read_bytes(), b"")
                        self.assertIn(expected, result.stderr)
                        self.assertNotIn("Traceback", result.stderr)
                        self.assertEqual(request.read_bytes(), payload)
                        self.assertEqual(candidate.read_text(encoding="utf-8"), "{}")
                        self.assertEqual(list(root.iterdir()), [foreign])
                        self.assertEqual(foreign.read_bytes(), b"keep existing material\n")


if __name__ == "__main__": unittest.main()
