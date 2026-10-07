"""Synthetic trust-boundary tests. NO receipt below is actual Lean evidence."""
# SPDX-License-Identifier: Apache-2.0
from __future__ import annotations

import _test_bootstrap  # noqa: F401
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent))
import research_return_gate as g
import check_assimilation_cut as ac

class Fixture(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name); self.raw = self.root / "return.txt"
        self.raw.write_text("Claim: P.\n\nSources and caveats.\n", encoding="utf-8")
        self.foundation = g.digest("foundation-fixture-not-a-real-build")
        self.index = {"schema": "plectis-trusted-evidence-index/1", "receipts": {},
                      "producers": {"test-fixture-owner": []}}
        self.ids = []
        self.req = {"schema": "plectis-gate-request/1", "claim_id": "C1", "kind": "mathematical",
            "source_span": {"return_sha256": g.bytes_sha(self.raw.read_bytes()), "start_byte": 0,
                            "end_byte": 9, "span_sha256": g.bytes_sha(self.raw.read_bytes()[:9])},
            "foundation_sha256": self.foundation, "context_sha256": g.digest("same telescope"),
            "new_statement_sha256": g.digest("P"), "old_statement_sha256": g.digest("Q"),
            "assumptions": ["H remains open"],
            "goals": {k: g.digest("elaborated fixture goal " + k) for k in g.KERNEL_CHECKS},
            "comparison_basis": "restricted_relation", "comparison_role": "theorem_statement"}

    def receipt(self, check, *, subject=None, **changes):
        rid = f"r{len(self.ids)}"; self.ids.append(rid)
        r = {"schema": "plectis-checked-evidence/1", "check": check,
             "subject_sha256": subject or g.digest(self.req), "foundation_sha256": self.foundation,
             "producer": "test-fixture-owner", "status": "checked"}
        if check in g.KERNEL_CHECKS:
            r.update(evidence_class="kernel_checked", axioms=[], goal_sha256=self.req["goals"][check],
                     proof_sha256=g.digest("not a real proof"), checker_sha256=g.digest("fixture checker"),
                     dependency_manifest_sha256=g.digest("fixture dependencies"))
        elif check in g.REVIEW_CHECKS:
            r["evidence_class"] = g.REVIEW_CHECKS[check]
            if check.endswith("search"):
                r.update(scope={"query": "P", "snapshot": "test-only"}, unsearched=["all external papers"])
        else:
            r.update(evidence_class="owner_verified_assimilation", validator_sha256=g.digest("fixture"),
                     inputs_sha256=g.digest(self.cut["files"]))
        r.update(changes)
        path = self.root / f"{rid}.json"; path.write_bytes(g.canonical(r))
        self.index["receipts"][rid] = {"path": path.name, "sha256": g.bytes_sha(path.read_bytes())}
        self.index["producers"]["test-fixture-owner"].append(check)
        return r

    def run_gate(self):
        return g.assess(self.req, self.index, self.root, self.ids, self.raw)

class GateTests(Fixture):
    def test_no_interpretation_means_no_verdict(self):
        self.receipt("proof"); self.assertEqual(self.run_gate()["interpretation"], "pending")
    def test_context_change_invalidates_receipt(self):
        self.receipt("interpretation"); self.req["context_sha256"] = g.digest("different scope")
        with self.assertRaises(g.GateError): self.run_gate()
    def test_return_change_invalidates_receipt(self):
        self.receipt("interpretation"); self.raw.write_text("Different claim")
        with self.assertRaises(g.GateError): self.run_gate()
    def test_span_change_rejected(self):
        self.req["source_span"]["end_byte"] = 10
        with self.assertRaises(g.GateError): self.run_gate()
    def test_custom_axiom_rejected(self):
        self.receipt("interpretation"); self.receipt("proof", axioms=["userAxiom"])
        with self.assertRaises(g.GateError): self.run_gate()
    def test_sorry_rejected(self):
        self.receipt("proof", axioms=["sorryAx"])
        with self.assertRaises(g.GateError): self.run_gate()
    def test_missing_axiom_audit_rejected(self):
        self.receipt("proof", axioms=None)
        with self.assertRaises(g.GateError): self.run_gate()
    def test_stale_goal_rejected(self):
        self.receipt("proof", goal_sha256=g.digest("True instead of intended goal"))
        with self.assertRaises(g.GateError): self.run_gate()
    def test_atlas_evidence_not_kernel(self):
        self.receipt("proof", evidence_class="declaration_atlas_at_pin")
        with self.assertRaises(g.GateError): self.run_gate()
    def test_stale_foundation_rejected(self):
        self.receipt("proof", foundation_sha256=g.digest("old"))
        with self.assertRaises(g.GateError): self.run_gate()
    def test_unauthorized_producer_rejected(self):
        self.receipt("proof"); self.index["producers"] = {}
        with self.assertRaises(g.GateError): self.run_gate()
    def test_unindexed_receipt_rejected(self):
        self.receipt("proof"); self.index["receipts"] = {}
        with self.assertRaises(g.GateError): self.run_gate()
    def test_modified_receipt_rejected(self):
        self.receipt("proof"); (self.root / "r0.json").write_text("{}")
        with self.assertRaises(g.GateError): self.run_gate()
    def test_supply_and_refutation_without_witness_mean_empty_context(self):
        self.receipt("interpretation"); self.receipt("proof"); self.receipt("refutation")
        self.assertEqual(self.run_gate()["feasibility"], "context_refuted")
    def test_corpus_identity_is_not_an_assertion_of_truth(self):
        self.receipt("interpretation"); self.receipt("existing_exact"); self.receipt("refutation")
        self.assertEqual(self.run_gate()["formal_correctness"], "refuted")
    def test_supply_conflicts_with_witness_failing_new(self):
        self.receipt("interpretation"); self.receipt("proof"); self.receipt("separator_old_not_new")
        self.assertEqual(self.run_gate()["action"], "quarantine_evidence_conflict")
    def test_refutation_conflicts_with_witness_satisfying_new(self):
        self.receipt("interpretation"); self.receipt("refutation"); self.receipt("separator_new_not_old")
        self.assertEqual(self.run_gate()["action"], "quarantine_evidence_conflict")
    def test_capabilities_string_is_rejected(self):
        self.receipt("proof"); self.index["producers"]["test-fixture-owner"] = "proof"
        with self.assertRaises(g.GateError): self.run_gate()
    def test_missing_comparison_role_is_not_silently_inferred(self):
        self.req.pop("comparison_role")
        with self.assertRaises(g.GateError): self.run_gate()
    def test_missing_reverse_not_strictness(self):
        self.receipt("interpretation"); self.receipt("new_to_old")
        self.receipt("old_to_new", status="unknown")
        self.assertEqual(self.run_gate()["relation"], "sufficient_converse_unknown")
    def test_witness_certifies_strict_strength(self):
        self.receipt("interpretation"); self.receipt("new_to_old"); self.receipt("separator_old_not_new")
        self.assertEqual(self.run_gate()["relation"], "strictly_stronger")
    def test_witness_certifies_strict_weakness(self):
        self.receipt("interpretation"); self.receipt("old_to_new"); self.receipt("separator_new_not_old")
        self.assertEqual(self.run_gate()["relation"], "strictly_weaker")
    def test_no_match_is_not_novelty(self):
        self.receipt("interpretation"); self.receipt("corpus_search"); self.receipt("literature_search")
        v = self.run_gate(); self.assertEqual(v["corpus_status"], "not_located_in_recorded_search")
        self.assertEqual(v["new_mathematical_credit"], "not_authorized")
    def test_library_proof_is_not_rediscovery(self):
        self.receipt("interpretation"); self.receipt("proof")
        self.assertEqual(self.run_gate()["corpus_status"], "unassessed")
    def test_unrestricted_equivalence_not_identity(self):
        self.req["comparison_basis"] = "unrestricted_provability"
        self.receipt("interpretation"); self.receipt("new_to_old"); self.receipt("old_to_new")
        self.assertEqual(self.run_gate()["relation"], "provability_only_not_a_novelty_comparison")
    def test_equivalent_preserves_utility_lane(self):
        self.receipt("interpretation"); self.receipt("new_to_old"); self.receipt("old_to_new")
        self.assertEqual(self.run_gate()["action"], "assess_representation_utility_separately")
    def test_existing_exact_requires_dedicated_receipt(self):
        self.receipt("interpretation"); self.receipt("existing_exact")
        self.assertEqual(self.run_gate()["corpus_status"], "existing_exact_statement")
    def test_open_assumption_is_not_vacuity(self):
        self.receipt("interpretation"); self.receipt("proof")
        self.assertEqual(self.run_gate()["feasibility"], "unknown")
    def test_refuted_context_is_vacuous(self):
        self.receipt("interpretation"); self.receipt("context_refutation")
        self.assertEqual(self.run_gate()["feasibility"], "context_refuted")
    def test_refuted_claim_not_proof_failure(self):
        self.receipt("interpretation"); self.receipt("refutation")
        self.assertEqual(self.run_gate()["formal_correctness"], "refuted")
    def test_contradictory_receipts_quarantined(self):
        self.receipt("interpretation"); self.receipt("proof"); self.receipt("refutation"); self.receipt("feasible")
        self.assertEqual(self.run_gate()["action"], "quarantine_evidence_conflict")
    def test_duplicate_checks_rejected(self):
        self.receipt("proof"); self.receipt("proof")
        with self.assertRaises(g.GateError): self.run_gate()
    def test_inline_authority_field_rejected(self):
        self.req["proved"] = True
        with self.assertRaises(g.GateError): self.run_gate()
    def test_unknown_status_rejected(self):
        self.receipt("proof", status="passed")
        with self.assertRaises(g.GateError): self.run_gate()
    def test_extraction_preserves_nonclaim_caveat(self):
        v = g.extract(self.raw)
        self.assertEqual(len(v["all_paragraphs"]), 2)
        self.assertEqual(v["semantic_coverage"], "review_required")
        self.assertIn("caveats", v["all_paragraphs"][1]["text"])
    def test_duplicate_json_keys_rejected(self):
        p = self.root / "duplicate.json"; p.write_text('{"status":"unknown","status":"checked"}')
        with self.assertRaises(g.GateError): g.read_json(p)
    def test_symlink_rejected(self):
        (self.root / "linked").symlink_to(self.raw)
        with self.assertRaises(g.GateError): g.safe_file(self.root, "linked")
    def test_traversal_rejected(self):
        with self.assertRaises(g.GateError): g.safe_file(self.root, "../return.txt")

class AssimilationTests(Fixture):
    def setUp(self):
        super().setUp()
        (self.root / "artifact.txt").write_text("fixture artifact")
        self.cut = {"schema": "plectis-assimilation-cut/1", "cut_id": "cut-fixture", "foundation_sha256": self.foundation,
            "formal_source_commit": "0" * 40, "record_parent_sha256": g.digest("old record head"),
            "claims": ["C1"], "files": {"artifact.txt": g.bytes_sha((self.root / "artifact.txt").read_bytes())},
            "consumers": [{"claim_id": "C1", "role": role, "disposition": "updated", "paths": ["artifact.txt"],
                           "reason": "", "owner": "", "trigger": ""} for role in ac.ROLES]}
    def complete(self):
        for check in sorted(ac.GLOBAL_CHECKS): self.receipt(check, subject=g.digest(self.cut))
        for r in self.cut["consumers"]:
            self.receipt("consumer/C1/" + r["role"], subject=g.digest(self.cut))
    def run_cut(self):
        return ac.validate(self.cut, self.root, self.index, self.root, self.ids)
    def test_queued_not_compared(self):
        self.complete(); v = self.run_cut()
        self.assertEqual(v["comparator_status"], "pending_not_claimed_passed")
        self.assertEqual(v["round_status"], "not_fully_closed")
    def test_compared_not_published(self):
        self.complete(); self.receipt("comparator_result", subject=g.digest(self.cut))
        self.assertEqual(self.run_cut()["round_status"], "not_fully_closed")
    def test_explicit_full_closure(self):
        self.complete(); self.receipt("comparator_result", subject=g.digest(self.cut))
        self.receipt("remote_publication", subject=g.digest(self.cut))
        self.assertEqual(self.run_cut()["round_status"], "closed")
    def test_missing_frontier_blocks(self):
        self.cut["consumers"] = [r for r in self.cut["consumers"] if r["role"] != "frontier"]
        self.complete()
        with self.assertRaises(g.GateError): self.run_cut()
    def test_stale_summary_blocks(self):
        self.complete(); (self.root / "artifact.txt").write_text("stale summary")
        with self.assertRaises(g.GateError): self.run_cut()
    def test_missing_impact_analysis_blocks(self):
        self.complete(); self.ids = [x for x in self.ids if g.read_json(self.root / (x + ".json"))["check"] != "impact_analysis"]
        with self.assertRaises(g.GateError): self.run_cut()
    def test_new_claim_requires_all_consumers(self):
        self.cut["claims"].append("C2"); self.complete()
        with self.assertRaises(g.GateError): self.run_cut()
    def test_no_unreviewed_unchanged(self):
        self.cut["consumers"][0]["disposition"] = "unchanged"
        with self.assertRaises(g.GateError): self.run_cut()
    def test_core_deferral_blocked(self):
        self.cut["consumers"][0].update(disposition="deferred", reason="later", owner="A", trigger="build finishes")
        self.complete()
        with self.assertRaises(g.GateError): self.run_cut()
    def test_queue_deferral_keeps_round_open(self):
        self.cut["consumers"][-1].update(disposition="deferred", reason="service unavailable", owner="A", trigger="service returns")
        self.complete(); self.assertEqual(self.run_cut()["round_status"], "not_fully_closed")
    def test_essential_na_blocked(self):
        self.cut["consumers"][0].update(disposition="not_applicable", reason="not needed")
        self.complete()
        with self.assertRaises(g.GateError): self.run_cut()
    def test_parent_record_move_invalidates(self):
        self.complete(); self.cut["record_parent_sha256"] = g.digest("concurrent append")
        with self.assertRaises(g.GateError): self.run_cut()

if __name__ == "__main__":
    unittest.main(verbosity=2)
