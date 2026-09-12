#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check the public finite-computation replay without running the large scans."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
COMPUTATIONS = ROOT / "research" / "experiments" / "erdos251"
spec = importlib.util.spec_from_file_location("erdos251_replay", COMPUTATIONS / "replay.py")
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)


class PublicComputationReplayTests(unittest.TestCase):
    def test_integer_and_type_changes_cannot_hide_in_float_tolerance(self):
        self.assertEqual(replay.differences({"count": 10**50}, {"count": 10**50 + 1}), ["result.count"])
        self.assertEqual(replay.differences(True, 1), ["result"])
        self.assertEqual(replay.differences(1.0, float("nan")), ["result"])
        self.assertEqual(replay.differences([1, 2], [1]), ["result.length"])
        self.assertEqual(replay.differences(0.1, 0.1 + 1e-15), [])
        self.assertEqual(replay.differences({"count": 1}, {"other": 1}), ["result.keys"])

    def test_every_saved_run_binds_program_and_finite_scope(self):
        for name in replay.CASES:
            with self.subTest(name=name):
                record = replay.recorded_case(name)
                self.assertEqual(record["verification_scope"], "finite_computation_only")

    def test_changed_program_and_arguments_are_refused_before_replay(self):
        name = "continued-fraction"
        program, _, receipt = replay.CASES[name]
        with tempfile.TemporaryDirectory() as temp:
            target = Path(temp)
            (target / "receipts").mkdir()
            shutil.copy2(COMPUTATIONS / program, target / program)
            shutil.copy2(COMPUTATIONS / "receipts" / receipt, target / "receipts" / receipt)
            with patch.object(replay, "ROOT", target):
                replay.recorded_case(name)
                (target / program).write_text("raise RuntimeError('must not execute')\n")
                with self.assertRaisesRegex(ValueError, "program changed"):
                    replay.replay(name, 1)
                shutil.copy2(COMPUTATIONS / program, target / program)
                path = target / "receipts" / receipt
                record = json.loads(path.read_text())
                record["arguments"] = ["--scale-bits", "32"]
                path.write_text(json.dumps(record))
                with self.assertRaisesRegex(ValueError, "replay command"):
                    replay.recorded_case(name)

    def test_small_standard_library_example_matches_recorded_prefix(self):
        result = subprocess.run(
            [sys.executable, "-S", str(COMPUTATIONS / "certified_continued_fraction.py"),
             "--problem", "erdos_251", "--scale-bits", "512"],
            cwd=ROOT, capture_output=True, text=True, timeout=15,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        actual = json.loads(result.stdout)
        expected = replay.recorded_case("continued-fraction")["result"]
        self.assertEqual(actual["first_quotients"], expected["first_quotients"])
        self.assertTrue(actual["separation_verified"])
        self.assertEqual(actual["self_check"], expected["self_check"])

    def test_help_does_not_require_optional_numpy(self):
        for program, _, _ in replay.CASES.values():
            with self.subTest(program=program):
                result = subprocess.run(
                    [sys.executable, "-S", str(COMPUTATIONS / program), "--help"],
                    capture_output=True, text=True, timeout=10,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("usage:", result.stdout)

    def test_paper_no_longer_requires_private_receipt_paths(self):
        source = (ROOT / "paper" / "reasoning-parts" / "erdos251" / "core.tex").read_text()
        self.assertNotIn("state/formal", source)
        for _, _, receipt in replay.CASES.values():
            self.assertIn(f"erdos251/receipts/{receipt}", source)


if __name__ == "__main__":
    unittest.main()
