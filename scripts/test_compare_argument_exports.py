#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for compare_argument_exports.py on synthetic graphs and exports."""
import gzip
import json
import tempfile
import unittest
from pathlib import Path

import compare_argument_exports as ca


def graph(supplied, statements=None, demands=(), summary=None):
    keys = set(statements if statements is not None else supplied) | set(supplied)
    return {"statements": [{"key": k, "type": f"T{k}", "status": "supplied" if k in supplied else "open",
                            "origins": ["hypothesis" if k in demands else "residual"], "problems": []}
                           for k in sorted(keys)],
            "theorems": [{"name": "thm", "hypotheses": list(demands)}],
            "source": {"export_summary": summary or {}, "export_config": {}}}


class CompareArms(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp())

    def arms(self, graphs, searched=None, caps=None):
        spec = {}
        for code, g in graphs.items():
            gp = self.dir / f"g{code}.json.gz"
            with gzip.open(gp, "wt", encoding="utf-8") as f:
                json.dump(g, f)
            spec[code] = {"graph": str(gp), "caps": (caps or {}).get(code, {"weaken": 0, "generalise": 0, "search": 60})}
            if searched is not None:
                ep = self.dir / f"e{code}.jsonl"
                ep.write_text("".join(json.dumps({"record": "statement", "key": k}) + "\n" for k in searched[code]))
                spec[code]["export"] = str(ep)
        return spec

    def test_joint_novel_excludes_what_the_baseline_supplies(self):
        # The advisory's fixture: S00 = S11 = {q}, S10 = S01 = {}.
        spec = self.arms({"00": graph({"q"}), "10": graph(set(), {"q"}), "01": graph(set(), {"q"}),
                          "11": graph({"q"})})
        r = ca.compare(spec)
        self.assertEqual(r["whole_graph_sets"]["joint_novel"], 0)
        self.assertEqual(r["whole_graph_sets"]["joint_versus_one_sided_only"], 1)

    def test_contrasts(self):
        # t1 only joint (0,0,0,1); t2 each pass alone but not both (0,1,1,0);
        # t3 baseline and joint (1,0,0,1).
        S = {"00": {"t3"}, "10": {"t2"}, "01": {"t2"}, "11": {"t1", "t3"}}
        every = {"t1", "t2", "t3"}
        spec = self.arms({a: graph(S[a], every, demands=every) for a in ca.ARMS}, {a: every for a in ca.ARMS})
        m = ca.compare(spec)["matched"]["corpus_demands_searched_by_every_arm"]
        self.assertEqual(m["targets"], 3)
        self.assertEqual(m["patterns_y00_y10_y01_y11"], {"0001": 1, "0110": 1, "1001": 1})
        # weakening: (0.5 + 0 + 0) / 3; interaction: (0.5 - 1 + 1) / 3
        self.assertAlmostEqual(m["weakening_effect"], 0.5 / 3)
        self.assertAlmostEqual(m["generalisation_effect"], 0.5 / 3)
        self.assertAlmostEqual(m["interaction"], 0.5 / 3)
        self.assertEqual(m["joint_novel"], ["t1"])

    def test_a_target_one_arm_did_not_search_is_left_out(self):
        S = {"00": set(), "10": set(), "01": set(), "11": {"u"}}
        searched = {"00": {"v"}, "10": {"u", "v"}, "01": {"u", "v"}, "11": {"u", "v"}}
        spec = self.arms({a: graph(S[a], {"u", "v"}) for a in ca.ARMS}, searched)
        matched = ca.compare(spec)["matched"]
        self.assertEqual(matched["searched_by_every_arm"]["targets"], 1)
        self.assertEqual(matched["searched_by_every_arm"]["joint_novel"], [])
        self.assertEqual(matched["supplied_but_not_searched_by_every_arm"], 1)

    def test_a_zero_cap_that_still_attempted_is_flagged(self):
        caps = {"00": {"weaken": 0, "generalise": 0, "search": 7200}, "10": {"weaken": 600, "generalise": 0, "search": 6000},
                "01": {"weaken": 0, "generalise": 1500, "search": 5700}, "11": {"weaken": 600, "generalise": 1500, "search": 4500}}
        g0 = graph(set(), {"q"}, summary={"weakening_tried": 1, "weakening_ms": 30})
        spec = self.arms({"00": g0, "10": graph(set(), {"q"}), "01": graph(set(), {"q"}), "11": graph(set(), {"q"})},
                         caps=caps)
        r = ca.compare(spec)
        self.assertIn("weakening launched off but tried 1 candidate(s)", r["arms"]["baseline"]["flags"])
        self.assertEqual([r["arms"][n]["cap_total_seconds"] for n in ("baseline", "consumer", "producer", "joint")],
                         [7200, 6600, 7200, 6600])
        self.assertTrue(any("cap totals differ" in f for f in r["design_flags"]))


if __name__ == "__main__":
    unittest.main()
