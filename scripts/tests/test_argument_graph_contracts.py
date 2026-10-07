#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for ``argument_graph_contracts.py``: exact affine projection and its
replayable certificates."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import random
import sys
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import argument_graph_contracts as contracts  # noqa: E402


def holds(row: dict, point: dict[str, Q]) -> bool:
    value = sum(Q(v) * point.get(k, Q(0)) for k, v in row["a"].items())
    return value < Q(row["b"]) if row.get("strict") else value <= Q(row["b"])


class Projection(unittest.TestCase):
    def test_the_249_budget(self) -> None:
        result = contracts.case249()
        self.assertEqual(result["status"], "projected")
        self.assertEqual(result["admissible_K"]["lower"], {"value": "1", "strict": False})
        self.assertEqual(result["admissible_K"]["upper"], {"value": "10/3", "strict": True})
        self.assertEqual(result["margin"], "1/1000")
        self.assertTrue(all(contracts.replay_certificate(result["input_rows"], row) for row in result["rows"]))

    def test_strict_and_closed_boundaries(self) -> None:
        strict = [{"a": {"x": 1}, "b": 1, "strict": True}, {"a": {"x": -1}, "b": -1}]
        self.assertEqual(contracts.project(strict, ["x"])["status"], "infeasible_relaxation")
        closed = [{"a": {"x": 1}, "b": 1}, {"a": {"x": -1}, "b": -1}]
        self.assertEqual(contracts.project(closed, ["x"])["status"], "projected")
        self.assertFalse(contracts.interval(closed, "x")["empty"])
        self.assertTrue(contracts.interval(strict, "x")["empty"])

    def test_a_negative_coefficient_gives_a_lower_bound(self) -> None:
        self.assertEqual(contracts.interval([{"a": {"x": -2}, "b": -3}], "x")["lower"]["value"], "3/2")

    def test_a_one_sided_variable_leaves_no_bound(self) -> None:
        self.assertEqual(contracts.project([{"a": {"x": 1, "y": 1}, "b": 2}], ["x"])["rows"], [])

    def test_coupled_constants(self) -> None:
        rows = [{"a": {"K": 2, "L": 3, "q": -1}, "b": 0}, {"a": {"q": 1}, "b": 7, "strict": True}]
        row = contracts.project(rows, ["q"])["rows"][0]
        self.assertEqual((row["a"], row["b"], row["strict"]), ({"K": "1", "L": "3/2"}, "7/2", True))

    def test_the_budget_returns_the_last_complete_stage(self) -> None:
        rows = [{"a": {"x": 1, "y": 1}, "b": 1}, {"a": {"x": -1}, "b": 0}]
        result = contracts.project(rows, ["x"], max_pairs=0)
        self.assertEqual((result["status"], result["eliminated"]), ("unknown_budget", []))

    def test_inputs_are_exact(self) -> None:
        for bad in ({"a": {"x": 0.1}, "b": 1}, {"a": {"x": 1}, "b": True}, {"a": {"": 1}, "b": 1},
                    {"a": {"x": 1}, "b": 1, "strict": "yes"}):
            with self.subTest(row=bad), self.assertRaises(ValueError):
                contracts.parse_rows([bad])

    def test_the_interval_refuses_a_hidden_variable(self) -> None:
        with self.assertRaises(ValueError):
            contracts.interval([{"a": {"x": 1, "y": 1}, "b": 1}], "x")

    def test_projection_is_exact_on_random_systems(self) -> None:
        """Eliminating y: a point x satisfies every projected row exactly when
        some y extends it (checked from y's bounds, which are explicit)."""
        rng = random.Random(4211)
        for trial in range(200):
            rows = []
            for _ in range(rng.randrange(2, 6)):
                a = {"x": Q(rng.randrange(-3, 4), rng.randrange(1, 3)), "y": Q(rng.randrange(-3, 4), rng.randrange(1, 3))}
                rows.append({"a": {k: str(v) for k, v in a.items() if v}, "b": str(Q(rng.randrange(-6, 7), 2)),
                             "strict": rng.random() < 0.4})
            result = contracts.project(rows, ["y"])
            for step in range(-16, 17):
                x = Q(step, 4)
                lower, upper, ok = None, None, True
                for row in rows:
                    ay, ax = Q(row["a"].get("y", 0)), Q(row["a"].get("x", 0))
                    bound = Q(row["b"]) - ax * x
                    if ay == 0:
                        ok &= (0 < bound) if row["strict"] else (0 <= bound)
                    elif ay > 0:
                        candidate = (bound / ay, row["strict"])
                        if upper is None or candidate[0] < upper[0] or (candidate[0] == upper[0] and candidate[1]):
                            upper = candidate
                    else:
                        candidate = (bound / ay, row["strict"])
                        if lower is None or candidate[0] > lower[0] or (candidate[0] == lower[0] and candidate[1]):
                            lower = candidate
                if lower and upper:
                    ok &= lower[0] < upper[0] or (lower[0] == upper[0] and not lower[1] and not upper[1])
                projected = all(holds(row, {"x": x}) for row in result["rows"])
                with self.subTest(trial=trial, x=x):
                    self.assertEqual(projected, ok)
                    self.assertTrue(all(contracts.replay_certificate(rows, row) for row in result["rows"]))


class Certificates(unittest.TestCase):
    def test_a_tampered_row_does_not_replay(self) -> None:
        result = contracts.case249()
        row = dict(result["rows"][-1])
        row["b"] = "0"
        self.assertFalse(contracts.replay_certificate(result["input_rows"], row))
        self.assertFalse(contracts.replay_certificate([{"a": {"x": 1}, "b": 1}],
                                                      {"a": {"x": "-1"}, "b": "-1", "strict": False,
                                                       "weights": {"0": "-1"}}))

    def test_lean_source_rechecks_and_never_carries_input_names(self) -> None:
        result = contracts.case249()
        text = contracts.lean_projection_file(result, result["input_rows"])
        self.assertIn("linarith [h1, h2]", text)
        self.assertIn("not a compiled result", text)
        bad = dict(result["rows"][-1])
        bad["b"] = "0"
        with self.assertRaises(ValueError):
            contracts.lean_certificate(result["input_rows"], bad)
        rows = [{"a": {"x) := by trivial --": 1}, "b": 1}]
        source = contracts.lean_projection_file(contracts.project(rows, []), rows)
        self.assertNotIn("trivial", source)
        self.assertIn("x0", source)

    def test_the_command_line(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out, lean = Path(tmp) / "249.json", Path(tmp) / "249.lean"
            self.assertEqual(contracts.main(["--case249", "--output", str(out), "--lean-out", str(lean)]), 0)
            self.assertIn('"status": "projected"', out.read_text(encoding="utf-8"))
            self.assertIn("theorem affine_projection_0", lean.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
