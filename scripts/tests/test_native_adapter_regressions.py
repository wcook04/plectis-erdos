"""Native relation and residual adapter safety regressions; no Lean run."""

import _test_bootstrap  # noqa: F401
# SPDX-License-Identifier: Apache-2.0
import importlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
class NativeRegressions(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        sys.path.insert(0, str(Path(ROOT) / "scripts"))
        cls.ev = importlib.import_module("residual_evaluator")
        cls.rr = importlib.import_module("relation_registry")
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name); (self.root / "docs").mkdir()
    def classify(self, residuals, proved, binders=""):
        s = self.ev.Sketch("S", "P", residuals, binders=binders)
        results = [self.ev.ProbeResult(p.name,p.kind,p.subject,p.statement,p.kind in proved)
                   for p in self.ev.build_probes([s], cross=False)]
        return self.ev.classify(s, results)
    def rows(self,v):
        p = self.root / "docs/residualbench_report.json"
        p.write_text(json.dumps({"schema":"residual_evaluator/1", "module":"Fixture",
                                "tactic_budget":{"id":"B"}, "verdicts":[v]}))
        return self.rr.residualbench_rows(self.root)
    def test_individual_equivalence_does_not_drop_extra_demand(self):
        rows = self.rows(self.classify(["P","Q"], {"soundness","p2r0","r2p0"}))
        main = rows[0]; led = self.rr.Ledger(rows)
        self.assertFalse(led.compare(main["context"], "P", main["right"])["left_gives_right"])
        self.assertTrue(led.compare(main["context"], main["right"], "P")["left_gives_right"])
        self.assertEqual(rows[1]["relation"], "equivalent")
    def test_full_conjunction_equivalence_needs_every_reverse(self):
        rows = self.rows(self.classify(["P","Q"], {"soundness","p2r0","r2p0","p2r1"}))
        self.assertEqual(rows[0]["relation"], "equivalent")
    def test_joint_equivalence_without_individual_equivalence(self):
        rows = self.rows(self.classify(["Q", "R"], {"soundness", "p2r0", "p2r1"}))
        self.assertEqual(rows[0]["relation"], "equivalent")
    def test_legacy_multiresidual_report_does_not_invent_matching_residual(self):
        v = self.classify(["P","Q"], {"soundness","p2r0","r2p0"})
        v.pop("equivalent_residuals"); v.pop("target_implies_all_residuals")
        self.assertEqual(self.rows(v)[0]["relation"], "slot_replacement")
    def test_closed_refutation_retained(self):
        rows = self.rows(self.classify(["Q"], {"refutation"}))
        self.assertEqual(rows[0]["relation"], "refuted")
    def test_negated_universal_not_pointwise_refutation(self):
        rows = self.rows(self.classify(["Q n"], {"refutation"}, binders="(n : Nat)"))
        self.assertEqual(rows[0]["relation"], "unknown")
    def test_distinct_contexts_not_merged(self):
        v1 = self.classify(["P"], {"p2r0","r2p0"}, "(n : Nat)")
        v2 = self.classify(["P"], {"p2r0","r2p0"}, "(n : Nat) (h : n > 0)")
        self.assertNotEqual(self.rows(v1)[0]["context"], self.rows(v2)[0]["context"])
    def test_implication_operands_parenthesized(self):
        sketch = self.ev.Sketch("S", "P → Q", ["P ∨ Q","R"])
        p = self.ev.build_probes([sketch], cross=False)[0]
        self.assertIn("((P ∨ Q) ∧ (R))", p.statement)
        self.assertTrue(p.statement.endswith("→ (P → Q)"))
    def test_empty_demand_is_true(self):
        self.assertEqual(self.ev.Sketch("S","P",[]).demand(), "True")
    def controls(self):
        return {name+"__t0":[] for name,_,must in self.ev.CONTROL_PROBES if must}
    def test_custom_axiom_cannot_pass(self):
        p = self.ev.Probe("probe_soundness__S","soundness","S","False",[])
        ax = self.controls(); ax[p.name+"__t0"]=["untrusted_axiom"]
        self.assertFalse(self.ev.decide([p],ax,{})[0].proved)
    def test_actual_winning_attempt_owns_axiom_list(self):
        p = self.ev.Probe("probe_soundness__S","soundness","S","True",[])
        ax = self.controls(); ax[p.name+"__t1"]=["Classical.choice"]
        self.assertEqual(self.ev.decide([p],ax,{})[0].axioms,["Classical.choice"])
    def test_failed_custom_attempt_can_fall_through_to_allowed_attempt(self):
        p = self.ev.Probe("probe_soundness__S","soundness","S","True",[])
        ax = self.controls(); ax[p.name+"__t0"]=["untrusted_axiom"]; ax[p.name+"__t1"]=["propext"]
        r = self.ev.decide([p],ax,{})[0]
        self.assertTrue(r.proved); self.assertEqual(r.axioms,["propext"])
    def test_nonboolean_legacy_receipts_rejected(self):
        v = self.classify(["P"], {"soundness"}); v["receipts"]["soundness"]="false"
        with self.assertRaises(self.rr.RegistryError): self.rows(v)

if __name__ == "__main__": unittest.main(verbosity=2)
