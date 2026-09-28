#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Offline developmental benchmark tests; synthetic receipts are never Lean evidence."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import build_restatement_benchmark as b
import relation_binding
import relation_registry

ROOT = Path(__file__).resolve().parents[1]


class RestatementBenchmarkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.source, cls.binding = relation_binding.emit(ROOT)
        cls.rows = relation_registry.load_registry(ROOT)["rows"]
        patcher = mock.patch.object(b.relation_binding, "emit",
                                    return_value=(cls.source, cls.binding))
        patcher.start()
        cls.addClassCleanup(patcher.stop)

    def synthetic_receipt(self) -> dict:
        """Structure fixture only: no Lean process was run by this test."""
        names = [o["declaration"] for o in self.binding["obligations"]]
        result = {"evidence_class": "compilation_probe", "exit_code": 0,
                  "timed_out": False, "compilation_accepted": True,
                  "accepted": True, "uses_sorry": False, "axioms_declared": [],
                  "nonstandard_axioms": [], "errors": [],
                  "source_sha256": self.binding["source_sha256"],
                  "axioms_printed": {n: [] for n in names}}
        return copy.deepcopy(relation_binding.checked_result(ROOT, self.source, self.binding, result))

    def fixture_root(self) -> tuple[tempfile.TemporaryDirectory, Path]:
        tmp = tempfile.TemporaryDirectory()
        root = Path(tmp.name)
        paths = {relation_registry.REGISTRY_PATH}
        paths.update(r["certificate"]["module"] for r in self.rows)
        for relative in paths:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / relative).read_bytes())
        return tmp, root

    def test_live_development_bank_has_five_families_and_separate_key(self) -> None:
        prompts, key, manifest = b.build(ROOT)
        self.assertEqual((len(prompts["tasks"]), len(key["answers"])), (8, 8))
        self.assertEqual(len(manifest["independent_families"]), 5)
        self.assertEqual(manifest["gold_state"], "development_unverified")
        self.assertFalse(manifest["confirmatory_sealed"])
        self.assertEqual([a["category"] for a in key["answers"]].count("restatement"), 4)
        self.assertEqual([a["category"] for a in key["answers"]].count("conditional_route"), 2)
        self.assertEqual([a["category"] for a in key["answers"]].count("local_refutation"), 1)
        self.assertEqual([a["category"] for a in key["answers"]].count("local_feasibility"), 1)
        self.assertTrue(all("relation" not in task and "certificate" not in task
                            for task in prompts["tasks"]))
        self.assertTrue(all(a["certificate_source"].endswith((":43", ":58", ":73", ":82", ":106", ":112", ":128", ":133"))
                            for a in key["answers"]))

    def test_writes_separate_participant_and_control_trees(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "bank"
            docs = b.build(ROOT)
            b.write_bundle(out, docs)
            self.assertEqual(json.loads((out / "participant/prompts.json").read_text()), docs[0])
            self.assertEqual(json.loads((out / "control/answer_key.json").read_text()), docs[1])
            with self.assertRaisesRegex(b.BenchmarkError, "empty"):
                b.write_bundle(out, docs)

    def test_unreplayed_bank_cannot_be_confirmatory(self) -> None:
        with self.assertRaisesRegex(b.BenchmarkError, "requires a current binding replay"):
            b.build(ROOT, seal_confirmatory=True)

    def test_disclosed_development_bank_stays_nonconfirmatory_even_with_receipt(self) -> None:
        receipt = self.synthetic_receipt()
        with self.assertRaisesRegex(b.BenchmarkError, "development families"):
            b.build(ROOT, binding_receipt=receipt, trusted_local_replay=True,
                    seal_confirmatory=True)

    def test_receipt_requires_explicit_local_trust_assertion(self) -> None:
        with self.assertRaisesRegex(b.BenchmarkError, "explicit trusted-local-replay"):
            b.build(ROOT, binding_receipt=self.synthetic_receipt())

    def test_current_structurally_bound_fixture_is_limited_to_development(self) -> None:
        _, _, manifest = b.build(ROOT, binding_receipt=self.synthetic_receipt(),
                                 trusted_local_replay=True)
        self.assertEqual(manifest["gold_state"], "development_binding_replay_checked")
        self.assertFalse(manifest["confirmatory_sealed"])
        self.assertIn("locally supplied receipt", manifest["binding_replay"]["boundary"])

    def test_stale_obligation_or_missing_axiom_report_refused(self) -> None:
        stale = self.synthetic_receipt()
        stale["manifest"]["obligations"][0]["row_sha256"] = "0" * 64
        with self.assertRaisesRegex(b.BenchmarkError, "stale"):
            b.build(ROOT, binding_receipt=stale, trusted_local_replay=True)
        missing = self.synthetic_receipt()
        missing["probe_result"]["axioms_printed"].pop(self.binding["obligations"][0]["declaration"])
        with self.assertRaisesRegex(b.BenchmarkError, "axiom report"):
            b.build(ROOT, binding_receipt=missing, trusted_local_replay=True)

    def test_disallowed_axiom_refused(self) -> None:
        receipt = self.synthetic_receipt()
        name = self.binding["obligations"][0]["declaration"]
        receipt["probe_result"]["axioms_printed"][name] = ["fixture.unsafeAxiom"]
        with self.assertRaisesRegex(b.BenchmarkError, "invalid axiom"):
            b.build(ROOT, binding_receipt=receipt, trusted_local_replay=True)

    def test_changed_registry_bytes_refused_against_binding_snapshot(self) -> None:
        tmp, root = self.fixture_root(); self.addCleanup(tmp.cleanup)
        path = root / relation_registry.REGISTRY_PATH
        path.write_bytes(path.read_bytes() + b" ")
        with mock.patch.object(b.relation_binding, "emit", return_value=(self.source, self.binding)), \
             mock.patch.object(b.relation_registry, "load_registry", return_value={"rows": self.rows}):
            with self.assertRaisesRegex(b.BenchmarkError, "registry bytes differ"):
                b.build(root)

    def test_changed_certificate_bytes_refused_against_binding_snapshot(self) -> None:
        tmp, root = self.fixture_root(); self.addCleanup(tmp.cleanup)
        path = root / self.rows[0]["certificate"]["module"]
        path.write_bytes(path.read_bytes() + b"\n-- changed after binding\n")
        with mock.patch.object(b.relation_binding, "emit", return_value=(self.source, self.binding)), \
             mock.patch.object(b.relation_registry, "load_registry", return_value={"rows": self.rows}):
            with self.assertRaisesRegex(b.BenchmarkError, "certificate bytes differ"):
                b.build(root)


if __name__ == "__main__":
    unittest.main(verbosity=2)
