#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Cross-runtime and independent-checker tests for the offline HTML explorer.

Requires Node.js to execute the actual BigInt script embedded in the page.
Neither Python authority imports or calls the JavaScript implementation.
"""
from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
from fractions import Fraction

ROOT = Path(__file__).resolve().parents[1]
HOME = ROOT / "research/experiments/choices_contraction"


def load(name):
    spec = importlib.util.spec_from_file_location(name, HOME / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ExplorerTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.node = shutil.which("node")
        if not cls.node:
            raise RuntimeError("Node.js is required; do not treat an unrun browser core as passing")
        cls.html = (HOME / "explorer.html").read_text()
        cls.core = re.search(r'<script id="exact-core">(.*?)</script>', cls.html, re.S).group(1)
        cls.probe = load("rational_membership_probe")
        cls.checker = load("verify_terminal_witness")

    def run_cases(self, cases):
        driver = self.core + """
const fs = require('node:fs');
const cases = JSON.parse(fs.readFileSync(0, 'utf8'));
console.log(JSON.stringify(cases.map(c => {
  try { return {ok: Explorer.run(...c)}; }
  catch (e) { return {error: e.message}; }
})));
"""
        result = subprocess.run([self.node, "-e", driver], input=json.dumps(cases),
                                text=True, capture_output=True, check=True, timeout=30)
        return json.loads(result.stdout)

    def test_cross_runtime_and_independent_terminal_verification(self):
        cases = [[target, host, depth]
                 for host in self.checker.HOSTS
                 for target in ("189/388", "1/3", "3/4", "1/2", "1/21", "2/7", "1", "4/3")
                 for depth in (1, 16, 17, 64)]
        kinds = set()
        for case, result in zip(cases, self.run_cases(cases)):
            target, host, depth = case
            try:
                expected = self.probe.single_target(Fraction(target), host, depth, 160)
            except ValueError:
                self.assertIn("error", result, case)
                continue
            actual = result["ok"]["row"]
            self.assertEqual(expected, actual, case)
            kinds.add(actual.get("tail_bound_kind", actual["outcome"]))
            if actual["outcome"] == "not_excluded":
                with self.assertRaisesRegex(ValueError, "finite survival"):
                    self.checker.verify(actual)
            else:
                self.assertTrue(self.checker.verify(actual).startswith("verified_"))
        self.assertEqual(kinds, {"universal_analytic", "computed_horizon",
                                 "finite_representation", "not_excluded"})

    def test_late_rejection_and_no_decision_promotion(self):
        rows = [r["ok"]["row"] for r in self.run_cases([
            ["189/388", "all", 16], ["189/388", "all", 17], ["1/2", "all", 64]])]
        self.assertEqual([r["outcome"] for r in rows], ["not_excluded", "excluded", "not_excluded"])
        self.assertEqual(rows[1]["first_rejection"], 17)
        forged = copy.deepcopy(rows[0])
        forged["outcome"] = "finite_representation"
        forged["finite_representation_end"] = 16
        with self.assertRaises(ValueError):
            self.checker.verify(forged)

    def test_tampered_browser_export_is_rejected(self):
        row = self.run_cases([["189/388", "all", 17]])[0]["ok"]["row"]
        for key, value in (("target", "190/388"), ("host", "odd"),
                           ("tail_upper", "0"), ("remainder", "0"),
                           ("selected_indices", []), ("first_rejection", 16)):
            wrong = copy.deepcopy(row)
            wrong[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.checker.verify(wrong)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plectis-result.json"
            path.write_text(json.dumps({"schema": "plectis-single-target-probe/1", "rows": [row]}))
            result = subprocess.run(["python3", "-I", str(HOME / "verify_terminal_witness.py"), str(path)],
                                    text=True, capture_output=True, check=True)
            self.assertEqual(json.loads(result.stdout), ["verified_exclusion"])

    def test_reject_invalid_or_unbounded_inputs(self):
        cases = [[value, "all", 17] for value in ("0", "-1", "1/0", "NaN", "1.5", "2/3/4", "2", "9" * 257)]
        cases += [["1/3", "all", depth] for depth in (0, 65, 1.5, None)]
        cases += [["1/3", host, 17] for host in ("toString", "__proto__", "unknown")]
        self.assertTrue(all("error" in r for r in self.run_cases(cases)))
        self.assertEqual(self.run_cases([[" 2 / 6 ", "all", 17]])[0]["ok"]["row"]["target"], "1/3")

    def test_standalone_and_no_approximate_decisions(self):
        self.assertNotRegex(self.html, r'<script[^>]+src=|<link[^>]+href=|<img[^>]+src=')
        self.assertNotRegex(self.core, r'parseFloat|Math\.pow|Math\.round|eval\(|fetch\(')
        self.assertIn('prefers-reduced-motion', self.html)
        self.assertIn('current=null;', self.html)
        self.assertIn('finite survival is not a certificate', self.html)


if __name__ == "__main__":
    unittest.main()
