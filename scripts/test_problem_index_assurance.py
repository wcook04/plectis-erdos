#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Static navigation must not turn conditional receipt wording into evidence."""
import unittest

from build_problem_index import build


class AssuranceWordingTest(unittest.TestCase):
    def test_contract_wording_is_conditional(self):
        source = {
            "problems": [], "reviewed_problems": [], "purpose": "fixture", "reading_rule": "fixture",
            "route_template": "fixture", "status_vocabulary": {}, "library_roots": [],
            "validation_commands": [],
        }
        licensed = "Comparator-checked against a separately declared statement"
        claims = {"external_verification_packet": {
            "receipt_contract": {"public_wording": licensed},
        }}
        result = build(source, {}, claims, None)["external_check"]
        self.assertNotEqual(result["public_wording"], licensed)
        self.assertIn("green exact-commit receipt", result["public_wording"])
        self.assertEqual(result["public_wording_after_green_receipt"], licensed)
        self.assertEqual(result["execution_status_route"],
                         "python3 scripts/query_corpus.py --route comparator_assurance")


if __name__ == "__main__":
    unittest.main()
