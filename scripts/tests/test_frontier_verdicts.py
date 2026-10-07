#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for scripts/frontier_verdicts.py: a verdict needs positive evidence for the
output the command was asked for, and a log that stops early decides nothing."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import frontier_verdicts as verdicts  # noqa: E402

SOURCE = "\n".join([
    "import Lean",                                  # 1
    'run_cmd Lean.logInfo "@@COMMAND 3"',           # 2
    "derive_idle A.a",                              # 3
    'run_cmd Lean.logInfo "@@COMMAND 5"',           # 4
    "derive_factor A.b",                            # 5
    'run_cmd Lean.logInfo "@@COMMAND 7"',           # 6
    "derive_weakening A.c",                         # 7
    'run_cmd Lean.logInfo "@@COMMAND 9"',           # 8
    "derive_frontier A.d",                          # 9
    'run_cmd Lean.logInfo "@@COMMAND 11"',          # 10
    "derive_idle A.e",                              # 11
    'run_cmd Lean.logInfo "@@COMMAND 13"',          # 12
    "derive_factor A.f",                            # 13
    'run_cmd Lean.logInfo "@@COMMAND 15"',          # 14
    "derive_frontier A.g",                          # 15
])

LOG = "\n".join([
    "@@COMMAND 3",
    "added A.a.idle : ∀ x, P x",
    "@@COMMAND 5",
    "added A.lemma.factored : ∃ w, Q w ∧ (H → R w)",
    "added A.b.factored : ∃ w, Q w ∧",
    "  (H → R w)",
    "placed A.b.factored :: H :: claim 2: R w",
    "placed A.b.factored :: G :: unused",
    "@@COMMAND 7",
    "research/probes/F.lean:7:0: warning: derive_weakening A.c: no hypothesis is used only through consequences",
    "@@COMMAND 9",
    "added A.d.frontier_0 : S",
    "research/probes/F.lean:9:0: error: kernel rejected A.d.frontier_1",
    "@@COMMAND 11",
    "@@COMMAND 13",
    # the requested factoring is refused after a lemma factoring was derived on the way
    "added A.lemma.factored : ∃ w, Q w ∧ (H → R w)",
    "research/probes/F.lean:13:0: warning: derive_factor A.f: every hypothesis its proof uses "
    "is needed before the conclusion's first claim",
    "@@COMMAND 15",
    "added A.g.frontier_0 : S",
    "research/probes/F.lean:15:0: warning: derive_frontier A.g: no supplier discharges hypothesis 1",
    "@@END",
    "DERIVED\tA.a.idle\t1f",
    "DERIVED\tA.b.factored\t2e",
    "DERIVED\tA.lemma.factored\t3d",
])


class Verdicts(unittest.TestCase):
    def test_credited_only_with_the_requested_output(self):
        out = verdicts.probe_verdicts(SOURCE, LOG, "F")
        self.assertTrue(out["derive_idle A.a"]["added"])
        b = out["derive_factor A.b"]
        self.assertTrue(b["clean"])
        self.assertEqual(b["names"], ["A.b.factored"])
        self.assertEqual(b["helpers"], ["A.lemma.factored"])
        self.assertEqual(b["statements"]["A.b.factored"], "∃ w, Q w ∧ (H → R w)")
        self.assertEqual(b["placements"],
                         [{"derived": "A.b.factored", "hypothesis": "H", "claims": "claim 2: R w"},
                          {"derived": "A.b.factored", "hypothesis": "G", "claims": "unused"}])
        self.assertFalse(out["derive_weakening A.c"]["added"])
        # an error at the line outweighs an `added` line before it
        self.assertFalse(out["derive_frontier A.d"]["satisfied"])
        # a command the log says nothing about has no verdict
        self.assertNotIn("derive_idle A.e", out)
        # a helper derived on the way does not satisfy a refused factoring
        f = out["derive_factor A.f"]
        self.assertFalse(f["satisfied"])
        self.assertFalse(f["added"])
        self.assertEqual(f["names"], [])
        self.assertEqual(f["helpers"], ["A.lemma.factored"])
        # a frontier that adds one theorem and warns about another is satisfied, not clean:
        # it cannot run in strict mode
        g = out["derive_frontier A.g"]
        self.assertTrue(g["satisfied"])
        self.assertFalse(g["clean"])
        self.assertFalse(g["added"])

    def test_created_and_reused(self):
        out = verdicts.probe_verdicts(SOURCE, LOG, "F")
        self.assertEqual(out["derive_factor A.b"]["created"], ["A.b.factored", "A.lemma.factored"])
        self.assertEqual(out["derive_factor A.f"]["created"], [])
        self.assertEqual(out["derive_factor A.f"]["reused"], ["A.lemma.factored"])

    def test_the_advisory_false_positive(self):
        source = "\n".join(["import Lean", 'run_cmd Lean.logInfo "@@COMMAND 3"', "derive_factor Target"])
        log = "\n".join(["@@COMMAND 3", "added Helper.factored : True",
                         "F.lean:3:0: warning: derive_factor Target: no useful factoring", "@@END"])
        out = verdicts.probe_verdicts(source, log, "F")
        self.assertFalse(out["derive_factor Target"]["satisfied"])
        self.assertEqual(out["derive_factor Target"]["helpers"], ["Helper.factored"])
        # the log cut right after the helper's line decides nothing
        cut = "\n".join(["@@COMMAND 3", "added Helper.factored : True"])
        self.assertEqual(verdicts.probe_verdicts(source, cut, "F"), {})

    def test_a_log_that_stops_early_leaves_the_last_command_open(self):
        truncated = LOG.split("@@COMMAND 15")[0] + "@@COMMAND 15\nadded A.g.frontier_0 : S"
        out = verdicts.probe_verdicts(SOURCE, truncated, "F")
        self.assertIn("derive_factor A.f", out)
        self.assertNotIn("derive_frontier A.g", out)

    def test_derived_lines_close_the_last_message(self):
        source = "\n".join(["import Lean", 'run_cmd Lean.logInfo "@@COMMAND 3"', "derive_idle A.c"])
        log = "\n".join(["@@COMMAND 3", "added A.c.idle : ∀ x, P x", "DERIVED\tA.c.idle\t1f",
                         "DERIVED\tL.factored\t2e"])
        out = verdicts.probe_verdicts(source, log, "F")
        self.assertEqual(out["derive_idle A.c"]["statements"]["A.c.idle"], "∀ x, P x")

    def test_imported_lemma_factorings_are_requested_by_name(self):
        self.assertTrue(verdicts.requested("derive_factor Nat.foo", "ErdosProblems.ArgumentGraph.Factored.Nat.foo"))
        self.assertTrue(verdicts.requested("derive_weakening A.«b»", "A.b.use_0_1"))
        self.assertFalse(verdicts.requested("derive_weakening A.b", "A.b.c.weakened_0"))
        self.assertFalse(verdicts.requested("derive_factor A.b", "A.lemma.factored"))

    def test_main_collects_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "probes").mkdir()
            (root / "art").mkdir()
            (root / "probes" / "F.lean").write_text(SOURCE)
            (root / "art" / "F.log").write_text(LOG)
            (root / "probes" / "G.lean").write_text("derive_idle Z.z\n")
            out = root / "v.json"
            self.assertEqual(verdicts.main(["--run", "9", "--run", "10", "--artifact", str(root / "art"),
                                            "--probes", str(root / "probes"), "--out", str(out)]), 0)
            data = json.loads(out.read_text())
            self.assertEqual(data["probe_run"], ["9", "10"])
            self.assertEqual(data["statement_hashes"],
                             {"A.a.idle": "1f", "A.b.factored": "2e", "A.lemma.factored": "3d"})
            self.assertEqual(data["probes_without_log"], ["G"])


if __name__ == "__main__":
    unittest.main()
