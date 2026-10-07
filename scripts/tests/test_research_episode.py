
import _test_bootstrap  # noqa: F401
#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import research_decision as d
import research_episode as e
import research_record as r
import research_decision_test_support as f


class EpisodeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name); f.fixture(self.root)
        self.env = mock.patch.dict(os.environ); self.env.start(); self.addCleanup(self.env.stop)
        os.environ.pop("CI", None)
        clock = mock.patch.object(r, "utc_now", return_value=f.TIME)
        clock.start(); self.addCleanup(clock.stop)
        f.open_round(r, self.root)
        self.capsule = d.build(self.root, 249, f.COMMIT)
        self.contract = f.contract(self.root, self.capsule)
        f.write(self.root, "research/experiments/calibration.json", self.contract)

    def plan(self):
        return e.make_plan(self.root, self.capsule, "research/experiments/calibration.json", "round-test")

    def test_plan_is_read_only(self):
        before = r.journal_path(self.root).read_bytes(); plan = self.plan()
        self.assertEqual(before, r.journal_path(self.root).read_bytes())
        self.assertFalse(plan["publication_admitted"]); self.assertEqual(plan["transfer"], "not_tested")

    def test_apply_keeps_scientific_reviews_pending(self):
        plan = self.plan(); added = e.apply(self.root, plan)
        self.assertEqual(len(added), 7); self.assertTrue(r.verify(self.root)["ok"])
        _, state = r.replay(self.root)
        out = state.outputs["insight/calibration-1"]
        self.assertEqual(out["reported"], {})
        self.assertEqual(out["detail"]["required"], list(e.REQUIRED_REVIEWS))

    def test_stale_head_refuses_second_writer(self):
        plan = self.plan(); f.open_round(r, self.root, "other-round")
        before = r.journal_path(self.root).read_bytes()
        with self.assertRaisesRegex(ValueError, "stale"): e.apply(self.root, plan)
        self.assertEqual(before, r.journal_path(self.root).read_bytes())

    def test_changed_protocol_refuses(self):
        plan = self.plan(); (self.root / "protocol.txt").write_text("rewritten after seeing outcome")
        with self.assertRaisesRegex(d.DecisionError, "protocol bytes do not match"): e.apply(self.root, plan)

    def test_invalid_last_event_has_no_partial_write(self):
        plan = self.plan(); before = r.journal_path(self.root).read_bytes()
        changes = copy.deepcopy(plan["changes"]); changes[-1]["detail"]["status"] = "invented"
        with self.assertRaises(r.RecordError):
            r.append_batch(self.root, changes, expected_head=plan["expected_head"], recorded_at=f.TIME)
        self.assertEqual(before, r.journal_path(self.root).read_bytes())

    def test_read_set_rechecked_before_publication(self):
        plan = self.plan(); before = r.journal_path(self.root).read_bytes(); count = []
        def validator():
            count.append(1)
            if len(count) == 2: raise d.DecisionError("concurrent source edit")
        with self.assertRaises(d.DecisionError):
            r.append_batch(self.root, plan["changes"], expected_head=plan["expected_head"],
                           validate_read_set=validator, recorded_at=f.TIME)
        self.assertEqual(before, r.journal_path(self.root).read_bytes())

    def test_new_source_between_plan_rebuild_and_locked_append_refused(self):
        plan = self.plan(); before = r.journal_path(self.root).read_bytes()
        native_append = r.append_batch
        def add_source_then_append(*args, **kwargs):
            (self.root / "lean").mkdir(exist_ok=True)
            (self.root / "lean/NewModule.lean").write_text("theorem marker : True := trivial\n")
            return native_append(*args, **kwargs)
        with mock.patch.object(r, "append_batch", side_effect=add_source_then_append):
            with self.assertRaisesRegex(d.DecisionError, "source inventory changed"):
                e.apply(self.root, plan)
        self.assertEqual(before, r.journal_path(self.root).read_bytes())

    def test_prediction_rejects_embedded_outcome(self):
        self.contract["outcome"] = "success"
        with self.assertRaises(d.DecisionError): e.validate_contract(self.contract)

    def test_boolean_budget_refused(self):
        self.contract["budget"]["model_tokens"] = True
        with self.assertRaises(d.DecisionError): e.validate_contract(self.contract)

    def test_native_ci_refusal_retained(self):
        plan = self.plan(); os.environ["CI"] = "true"
        with self.assertRaisesRegex(r.RecordError, "CI"): e.apply(self.root, plan)

    def test_unknown_mechanism_uses_native_owner(self):
        self.contract["mechanism_id"] = "invented"
        f.write(self.root, "research/experiments/calibration.json", self.contract)
        with self.assertRaisesRegex(d.DecisionError, "native theory-lab"): self.plan()

    def test_plan_tamper_refused(self):
        plan = self.plan(); plan["changes"][0]["detail"]["required"] = ["publication_review"]
        with self.assertRaisesRegex(d.DecisionError, "digest"): e.apply(self.root, plan)

    def test_rehashing_forged_plan_cannot_complete_review(self):
        plan = self.plan()
        plan["changes"][0]["detail"]["required"] = ["publication_review"]
        plan["plan_sha256"] = d.digest({k: v for k, v in plan.items() if k != "plan_sha256"})
        with self.assertRaisesRegex(d.DecisionError, "native prospective"):
            e.apply(self.root, plan)

    def test_declaring_output_does_not_report_computed_milestone(self):
        plan = self.plan()
        for change in plan["changes"]:
            self.assertNotEqual(change["kind"], "milestone_reported")


if __name__ == "__main__": unittest.main()
