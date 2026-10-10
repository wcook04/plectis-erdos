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
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from fractions import Fraction

import validation_singleflight as singleflight

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
        cls.node = singleflight.node_executable()
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
                                env=singleflight.command_environment(),
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

    def run_ui(self, cases):
        # Execute both shipped scripts and the real form/download handlers.
        # The DOM fixture only supplies elements; no probe result is synthesized.
        driver = r"""
const fs = require('node:fs');
const vm = require('node:vm');
const input = JSON.parse(fs.readFileSync(0, 'utf8'));
class Element {
  constructor() { this.value = ''; this.children = []; this.listeners = {}; }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = children; }
  setAttribute() {}
  addEventListener(name, handler) { this.listeners[name] = handler; }
  click() {}
}
const elements = Object.fromEntries([...input.html.matchAll(/\bid="([^"]+)"/g)]
  .map(match => [match[1], new Element()]));
elements.target.value = '189/388'; elements.host.value = 'all'; elements.depth.value = '17';
elements.host.selectedOptions = [{textContent: 'All positive integers'}];
const downloads = [];
const context = vm.createContext({
  document: {getElementById: id => elements[id], createElement: () => new Element(), querySelectorAll: () => []},
  Blob, URL: {createObjectURL: blob => { downloads.push(blob); return 'blob:fixture'; }, revokeObjectURL() {}},
  setTimeout() {},
});
for (const match of input.html.matchAll(/<script\b[^>]*>([\s\S]*?)<\/script>/g))
  vm.runInContext(match[1], context);
(async () => {
  const rows = [];
  for (const [target, depth] of input.cases) {
    elements.target.value = target; elements.depth.value = String(depth);
    elements.controls.listeners.input();
    const cleared = elements['result-json'].value === '' && elements.result.hidden;
    elements.controls.listeners.submit({preventDefault() {}});
    const displayed = elements['result-json'].value;
    const before = downloads.length;
    elements.download.listeners.click();
    rows.push({cleared, hidden: elements.result.hidden, error: elements.error.textContent,
      displayed, downloaded: downloads.length > before ? await downloads.at(-1).text() : null});
  }
  console.log(JSON.stringify(rows));
})();
"""
        result = subprocess.run([self.node, "-e", driver],
                                input=json.dumps({"html": self.html, "cases": cases}),
                                env=singleflight.command_environment(), text=True,
                                capture_output=True, check=True, timeout=30)
        return json.loads(result.stdout)

    def test_visible_json_matches_download_and_independent_checker(self):
        cases = [("189/388", 16), ("189/388", 17), ("1/3", 17), ("1/2", 64)]
        for (target, depth), result in zip(cases, self.run_ui(cases)):
            with self.subTest(target=target, depth=depth):
                self.assertTrue(result["cleared"])
                self.assertFalse(result["hidden"])
                self.assertEqual(result["error"], "")
                self.assertEqual(result["displayed"], result["downloaded"])
                payload = json.loads(result["displayed"])
                self.assertEqual(payload["schema"], "plectis-single-target-probe/1")
                row = payload["rows"][0]
                self.assertEqual(row, self.probe.single_target(Fraction(target), "all", depth, 160))
                if row["outcome"] == "not_excluded":
                    with self.assertRaisesRegex(ValueError, "finite survival"):
                        self.checker.verify(row)
                else:
                    self.assertTrue(self.checker.verify(row).startswith("verified_"))

    def test_edit_or_invalid_input_cannot_leave_exportable_stale_json(self):
        valid, invalid = self.run_ui([("1/3", 17), ("1/0", 17)])
        self.assertIsNotNone(valid["downloaded"])
        self.assertTrue(invalid["cleared"])
        self.assertTrue(invalid["hidden"])
        self.assertTrue(invalid["error"])
        self.assertEqual(invalid["displayed"], "")
        self.assertIsNone(invalid["downloaded"])

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
            result = subprocess.run([sys.executable, "-I", str(HOME / "verify_terminal_witness.py"), str(path)],
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

    def test_checker_rejects_expanding_forms_before_fraction_conversion(self):
        # Compact exponent notation must never reach Fraction: the exponent
        # could otherwise allocate integers unrelated to the horizon limit.
        invalid = ("1e1000000000", "1E-1000000000", "0.5", "1.", ".5",
                   "1_000", " 1/3", "1 / 3", "+1", "１/３", "1/2/3", "")
        with patch.object(self.checker, "Fraction", side_effect=AssertionError("Fraction called")):
            for value in invalid:
                with self.subTest(value=value), self.assertRaisesRegex(ValueError, "integer or fraction"):
                    self.checker.rational(value, "target")

    def test_checker_digit_limit_applies_to_each_component_before_conversion(self):
        too_many = "9" * (self.checker.MAX_RATIONAL_DIGITS + 1)
        with patch.object(self.checker, "Fraction", side_effect=AssertionError("Fraction called")):
            for value in (too_many, "-" + too_many, "1/" + too_many,
                          too_many + "/" + too_many):
                with self.subTest(length=len(value)), self.assertRaisesRegex(ValueError, "digit limit"):
                    self.checker.rational(value, "target")

    def test_checker_accepts_boundary_fractions_without_changing_integer_guard(self):
        before = sys.get_int_max_str_digits()
        digits = min(self.checker.MAX_RATIONAL_DIGITS, before or self.checker.MAX_RATIONAL_DIGITS)
        component = "9" * digits
        number = 10 ** digits - 1
        for value, expected in ((component, Fraction(number)),
                                ("-" + component, Fraction(-number)),
                                ("1/" + component, Fraction(1, number)),
                                (component + "/" + component, Fraction(1)),
                                ("0", Fraction(0)), ("189/388", Fraction(189, 388))):
            self.assertEqual(self.checker.rational(value, "target"), expected)
        self.assertEqual(sys.get_int_max_str_digits(), before)
        for value in ("1/0", "0/0"):
            with self.assertRaisesRegex(ValueError, "invalid target"):
                self.checker.rational(value, "target")

    def test_checker_refuses_expanding_record_under_optimized_python(self):
        row = self.run_cases([["1/3", "all", 17]])[0]["ok"]["row"]
        row["target"] = "1e1000000000"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "malformed.json"
            path.write_text(json.dumps({"rows": [row]}))
            result = subprocess.run([sys.executable, "-I", "-O",
                                     str(HOME / "verify_terminal_witness.py"), str(path)],
                                    text=True, capture_output=True, timeout=5)
        self.assertEqual(result.returncode, 1)
        self.assertIn("target must be an integer or fraction", result.stderr)

    def test_checker_respects_a_stricter_python_integer_guard(self):
        driver = """
import runpy, sys
checker = runpy.run_path(sys.argv[1])
try:
    checker['rational']('9' * 641, 'target')
except ValueError:
    assert sys.get_int_max_str_digits() == 640
else:
    raise AssertionError('stricter Python integer guard was bypassed')
"""
        subprocess.run([sys.executable, "-I", "-X", "int_max_str_digits=640", "-c", driver,
                        str(HOME / "verify_terminal_witness.py")],
                       text=True, capture_output=True, check=True, timeout=5)


if __name__ == "__main__":
    unittest.main()
