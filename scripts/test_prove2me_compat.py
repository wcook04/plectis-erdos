#!/usr/bin/env python3
"""Focused offline round-trip tests for the preferred #257 and legacy #249 packets."""

import copy
import unittest

import prove2me_compat as compat


class Prove2MeCompatTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.packet = compat.prepare()

    def test_prepare_prefers_source_bound_257_theorem(self):
        packet = self.packet
        self.assertEqual(packet["unit"], compat.DEFAULT_UNIT)
        self.assertEqual(packet["claim_id"], "reciprocal_summable_support")
        self.assertEqual(packet["paper_label"], "res:reciprocal-support")
        self.assertIn("remaining_open.universal_257_all_infinite_supports", packet["remaining_open_proposition_ids"])
        self.assertEqual(packet["native_draft"]["theorem_name"],
                         "Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal")
        self.assertIn("AllBaseReciprocalSupportIrrationality.lean#L395", packet["native_draft"]["source"])
        self.assertIn("plectis-erdos/blob/", packet["native_draft"]["source"])
        self.assertIn("erdos-257-mersenne-support-subseries.tex#L90", packet["native_draft"]["paper_source"])
        self.assertEqual(packet["mathlib_rev"], "5e932f97dd25535344f80f9dd8da3aab83df0fe6")

    def test_249_remains_selectable_with_its_own_source_and_boundary(self):
        packet = compat.prepare("erdos249_all_base_totient_kernel_paper_theorem")
        self.assertEqual(packet["claim_id"], "all_base_totient_kernel_index_reduction")
        self.assertEqual(packet["paper_label"], "thm:kkernelrank")
        self.assertIn("remaining_open.erdos_249_irrationality", packet["remaining_open_proposition_ids"])
        self.assertIn("FullKernelAssemblies.lean#L", packet["native_draft"]["source"])
        self.assertIn("unconditional_rank_declaration", packet["local_attachment"])
        self.assertIn("environment_unverified", compat.validate(packet)["blockers"])
        swapped = copy.deepcopy(packet)
        swapped["unit"] = compat.DEFAULT_UNIT
        self.assertIn("source_or_claim_mismatch", compat.validate(swapped)["blockers"])

    def test_validate_blocks_environment_source_and_type_mismatch(self):
        missing = compat.validate(self.packet)
        self.assertIn("environment_unverified", missing["blockers"])
        self.assertIn("platformized_source_missing", missing["blockers"])
        env = {"source_url": "https://prove2.me/api/v1/environments", "captured_with_authenticated_request": True,
               "environments": [{"mathlib_rev": "other", "toolchain": "leanprover/lean4:v4.33.1"}]}
        stage = {"source_sha256": "wrong", "original_type": "α", "staged_type": "β",
                 "declaration_graph_receipt": "graph", "sketch_info_receipt": "sketch",
                 "compiled_exact_upload_text": True, "compiled_solution": True,
                 "formal_statement": f"theorem {self.packet['native_draft']['theorem_name']} (n : Nat) : n = n := by sorry",
                 "preamble": "import Mathlib", "solution": "theorem solution (n : Nat) : n = n := by rfl"}
        bad = compat.validate(self.packet, env, stage)
        self.assertIn("environment_mismatch", bad["blockers"])
        self.assertIn("staged_source_mismatch", bad["blockers"])
        self.assertIn("type_mismatch_or_missing", bad["blockers"])
        env["environments"][0] = {"mathlib_rev": self.packet["mathlib_rev"],
                                   "toolchain": self.packet["lean_toolchain"]}
        stage["source_sha256"] = self.packet["sources_sha256"][compat.UNITS[compat.DEFAULT_UNIT]["lean_source"]]
        stage["staged_type"] = stage["original_type"]
        self.assertEqual(compat.validate(self.packet, env, stage)["status"], "draft_for_review")
        tampered = copy.deepcopy(self.packet)
        tampered["sources_sha256"][compat.UNITS[compat.DEFAULT_UNIT]["lean_source"]] = "0" * 64
        self.assertIn("source_or_claim_mismatch", compat.validate(tampered)["blockers"])
        tampered = copy.deepcopy(self.packet)
        tampered["native_draft"]["natural_language_statement"] = "unrelated theorem"
        self.assertIn("packet_metadata_mismatch", compat.validate(tampered)["blockers"])

    def test_publish_job_is_not_a_theorem_id_and_retries_are_distinct(self):
        queued = compat.normalize_event("publish_job", {"jobs": [{"job_id": "job-1", "name": "x"}]})
        self.assertEqual(queued["status"], "PENDING")
        self.assertIsNone(queued["theorem_id"])
        state = compat.reconcile(self.packet, None, queued)
        failed = compat.normalize_event("publish_job", {"id": "job-1", "status": "FAILED", "error_message": "compile error"})
        state = compat.reconcile(self.packet, state, failed)
        self.assertEqual(state["publish_jobs"]["job-1"]["status"], "FAILED")
        self.assertEqual(compat.reconcile(self.packet, state, queued), state)
        error = compat.normalize_event("publish_job", {"id": "job-2", "status": "ERROR"})
        state = compat.reconcile(self.packet, state, error)
        self.assertEqual(state["publish_jobs"]["job-2"]["status"], "ERROR")
        published = compat.normalize_event("publish_job", {"id": "job-3", "status": "PUBLISHED", "theorem_id": "thm-1"})
        state = compat.reconcile(self.packet, state, published)
        self.assertEqual(state["publish_jobs"]["job-3"]["theorem_id"], "thm-1")
        with self.assertRaises(ValueError):
            compat.normalize_event("publish_job", {"id": "job-4", "status": "PENDING", "theorem_id": "not-yet"})

    def test_verification_acceptance_and_correction_lineage(self):
        published = compat.normalize_event("publish_job", {"id": "job-a", "status": "PUBLISHED", "theorem_id": "thm-a"})
        state = compat.reconcile(self.packet, None, published)
        accepted = compat.normalize_event("verification", {"id": "sub-a", "status": "ACCEPTED", "theorem_id": "thm-a"})
        state = compat.reconcile(self.packet, state, accepted)
        self.assertEqual(state["verifications"]["sub-a"]["status"], "ACCEPTED")
        pending = compat.normalize_event("verification", {"id": "sub-a", "status": "PENDING", "theorem_id": "thm-a"})
        self.assertEqual(compat.reconcile(self.packet, state, pending), state)
        replacement = compat.normalize_event("publish_job", {"id": "job-b", "status": "PUBLISHED", "theorem_id": "thm-b"})
        state = compat.reconcile(self.packet, state, replacement, replaces_theorem="thm-a")
        self.assertEqual(state["replacements"]["thm-a"]["new_theorem_id"], "thm-b")
        self.assertEqual(state["replacements"]["thm-a"]["source_status"],
                         "external_lineage_only_unverified")
        self.assertEqual(compat.reconcile(self.packet, state, replacement, replaces_theorem="thm-a"), state)
        with self.assertRaises(ValueError):
            compat.reconcile(self.packet, state, compat.normalize_event("verification", {
                "id": "sub-orphan", "status": "ACCEPTED", "theorem_id": "thm-unknown"}))

    def test_conflicting_terminal_status_rejected(self):
        state = compat.reconcile(self.packet, None, compat.normalize_event("publish_job", {
            "id": "job-a", "status": "PUBLISHED", "theorem_id": "thm-a"}))
        conflict = compat.normalize_event("publish_job", {"id": "job-a", "status": "FAILED"})
        with self.assertRaises(ValueError):
            compat.reconcile(self.packet, state, conflict)


if __name__ == "__main__":
    unittest.main()
