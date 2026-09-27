#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for ``run_kernel_probes.py``: what an accepted probe is. Lean never
runs here; ``subprocess.run`` is replaced by a stub returning the output a
probe would print."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import run_kernel_probes as runner  # noqa: E402


class ProbeVerdicts(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.probe = self.root / "research" / "probes" / "Probe.lean"
        self.probe.parent.mkdir(parents=True)
        self.probe.write_text("theorem target : True := trivial\n#print axioms target\n", encoding="utf-8")
        context = patch.object(runner, "ROOT", self.root)
        context.start()
        self.addCleanup(context.stop)

    def run_probe(self, code: int = 0, output: str = "") -> dict:
        done = subprocess.CompletedProcess([], code, output, "")
        with patch.object(runner.subprocess, "run", return_value=done):
            return runner.run_probe(self.probe, 60)

    def test_a_clean_probe_is_a_compilation_receipt_only(self) -> None:
        verdict = self.run_probe(output="'target' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n")
        self.assertTrue(verdict["accepted"] and verdict["compilation_accepted"])
        self.assertEqual((verdict["evidence_class"], verdict["exact_target_checked"], verdict["environment_replayed"]),
                         ("compilation_probe", False, False))
        self.assertEqual(verdict["axioms_printed"], {"target": ["propext", "Classical.choice", "Quot.sound"]})

    def test_errors_and_sorry_refuse(self) -> None:
        self.assertFalse(self.run_probe(1, "research/probes/Probe.lean:1:0: error: failed")["accepted"])
        self.assertFalse(self.run_probe(0, "research/probes/Probe.lean:1:8: warning: declaration uses 'sorry'")
                         ["accepted"])

    def test_a_declared_axiom_refuses_even_when_lean_is_happy(self) -> None:
        self.probe.write_text("-- axiom in a comment does not count\naxiom cheat : False\n"
                              "theorem target : 1 = 2 := cheat.elim\n", encoding="utf-8")
        verdict = self.run_probe()
        self.assertTrue(verdict["compilation_accepted"])
        self.assertFalse(verdict["accepted"])
        self.assertEqual(verdict["axioms_declared"], ["cheat"])

    def test_a_printed_nonstandard_axiom_refuses(self) -> None:
        verdict = self.run_probe(output="'target' depends on axioms: [propext, Lean.ofReduceBool]\n"
                                        "'other' does not depend on any axioms\n")
        self.assertEqual(verdict["nonstandard_axioms"], ["Lean.ofReduceBool"])
        self.assertEqual(verdict["axioms_printed"]["other"], [])
        self.assertFalse(verdict["accepted"])

    def test_a_timeout_keeps_what_lean_printed(self) -> None:
        expired = subprocess.TimeoutExpired("lean", 1, output=b"partial stdout", stderr=b"partial stderr")
        with patch.object(runner.subprocess, "run", side_effect=expired):
            verdict = runner.run_probe(self.probe, 1)
        self.assertTrue(verdict["timed_out"])
        self.assertFalse(verdict["accepted"])
        self.assertIn("partial stdout", verdict["output_tail"])
        self.assertIn("partial stderr", verdict["output_tail"])

    def test_the_source_is_bound_by_its_hash(self) -> None:
        first = self.run_probe()["source_sha256"]
        self.probe.write_text("theorem target : True := by trivial\n", encoding="utf-8")
        self.assertNotEqual(first, self.run_probe()["source_sha256"])

    def test_a_timeout_must_be_positive(self) -> None:
        with self.assertRaises(ValueError):
            runner.run_probe(self.probe, 0)


if __name__ == "__main__":
    unittest.main()
