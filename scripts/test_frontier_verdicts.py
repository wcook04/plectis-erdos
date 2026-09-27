#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for scripts/frontier_verdicts.py: a verdict needs positive evidence."""

from __future__ import annotations

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
    "DERIVED\tA.a.idle\t1f",
    "DERIVED\tA.b.factored\t2e",
])


class Verdicts(unittest.TestCase):
    def test_positive_evidence_only(self):
        out = verdicts.probe_verdicts(SOURCE, LOG, "F")
        self.assertTrue(out["derive_idle A.a"]["added"])
        self.assertEqual(out["derive_factor A.b"]["names"], ["A.b.factored", "A.lemma.factored"])
        self.assertEqual(out["derive_factor A.b"]["statements"]["A.b.factored"], "∃ w, Q w ∧ (H → R w)")
        self.assertEqual(out["derive_factor A.b"]["placements"],
                         [{"derived": "A.b.factored", "hypothesis": "H", "claims": "claim 2: R w"},
                          {"derived": "A.b.factored", "hypothesis": "G", "claims": "unused"}])
        self.assertFalse(out["derive_weakening A.c"]["added"])
        # an error at the line outweighs an `added` line before it
        self.assertFalse(out["derive_frontier A.d"]["added"])
        # a command the log says nothing about has no verdict
        self.assertNotIn("derive_idle A.e", out)

    def test_main_collects_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "probes").mkdir()
            (root / "art").mkdir()
            (root / "probes" / "F.lean").write_text(SOURCE)
            (root / "art" / "F.log").write_text(LOG)
            (root / "probes" / "G.lean").write_text("derive_idle Z.z\n")
            out = root / "v.json"
            self.assertEqual(verdicts.main(["--run", "9", "--artifact", str(root / "art"),
                                            "--probes", str(root / "probes"), "--out", str(out)]), 0)
            data = json.loads(out.read_text())
            self.assertEqual(data["statement_hashes"], {"A.a.idle": "1f", "A.b.factored": "2e"})
            self.assertEqual(data["probes_without_log"], ["G"])


if __name__ == "__main__":
    unittest.main()
