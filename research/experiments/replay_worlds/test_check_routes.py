#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Unit tests for check_routes.py on synthetic records, plus the real record."""

import json
import unittest
from pathlib import Path

import check_routes

HERE = Path(__file__).resolve().parent


def fake_reader(files):
    def read(commit, relpath):
        return files[relpath.split("/")[-1]]
    return read


def record(routes, reopened=None):
    return {
        "source_commit": "c0ffee",
        "records": "docs/papers/full-text",
        "readers": [{"reader": "X", "worlds": ["1"], "routes": routes}],
        "reopened": reopened or {},
    }


class CheckRoutesTest(unittest.TestCase):
    def test_needle_found_and_missing(self):
        files = {"a.md": "the stall was caused by unbounded states"}
        ok = check_routes.check(record([
            {"id": "r1", "closure": "attempt_closed", "needle": "unbounded states", "file": "a.md"},
        ]), fake_reader(files))
        self.assertTrue(ok["ok"])
        bad = check_routes.check(record([
            {"id": "r1", "closure": "attempt_closed", "needle": "bounded and decodable", "file": "a.md"},
        ]), fake_reader(files))
        self.assertFalse(bad["ok"])

    def test_absence_claim_is_falsified_by_an_occurrence(self):
        files = {"a.md": "by the Subspace Theorem"}
        result = check_routes.check(record([
            {"id": "r1", "closure": "out_of_support", "absent_terms": ["Subspace"], "absent_files": ["a.md"]},
        ]), fake_reader(files))
        self.assertFalse(result["ok"])

    def test_unknown_class_and_dangling_reopen(self):
        result = check_routes.check(record([
            {"id": "r1", "closure": "promising"},
            {"id": "r2", "closure": "attempt_closed", "reopened": "R9"},
        ]), fake_reader({}))
        self.assertEqual(len(result["problems"]), 2)

    def test_real_record_at_its_pinned_commit(self):
        real = json.loads((HERE / "routes.json").read_text())
        try:
            receipt = check_routes.check(real)
        except RuntimeError as exc:  # shallow clone: say so instead of passing
            self.fail(str(exc))
        self.assertTrue(receipt["ok"], receipt["problems"])
        self.assertEqual(receipt["reopened"], ["R1", "R2", "R3"])


if __name__ == "__main__":
    unittest.main()
