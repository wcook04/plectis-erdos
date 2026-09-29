#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
import copy
import json
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


if __name__ == "__main__": unittest.main()
