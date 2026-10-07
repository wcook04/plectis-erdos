#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check source binding and learner stopping points in the small reading packet."""

import _test_bootstrap  # noqa: F401
import json
import unittest
from unittest.mock import patch
import build_reading_edition as edition


class WeightedTaskTests(unittest.TestCase):
    def test_packet_projects_exact_claim_boundary_and_three_cases(self):
        text = next(iter(edition.build_weighted_task().values()))
        registry = json.loads((edition.ROOT / 'docs/claims.json').read_text())
        row = next(x for x in registry['claims'] if x['id'] == edition.WEIGHTED_ID)
        self.assertIn(row['statement'], text)
        self.assertIn(row['status'], text)
        for key in row['remaining_open_proposition_ids']:
            boundary = next(x for x in registry['remaining_open_propositions'] if x['id'] == key)
            self.assertIn(boundary['statement'], text)
            self.assertIn(key, text)
        for case in ('$c=2,p=1,b=2$', '$c=2,p=1,b=3$', '$c=2,p=2$'):
            self.assertIn(case, text)
        self.assertIn('no arithmetic verdict', text)
        self.assertIn('not a separately named Lean-checked instance', text)
        self.assertLess(len(text.encode()), 16000)

    def test_saved_packet_has_public_example_source_link(self):
        text = next(iter(edition.build_weighted_task().values()))
        self.assertIn("[paper's example](" + edition.BLOB
                      + "paper/257/erdos-257-mersenne-support-subseries.tex)", text)
        self.assertNotIn("(../../paper/", text)
        self.assertIn("(../../paper/257/erdos-257-mersenne-support-subseries.tex)",
                      edition.WEIGHTED_PACKET.read_text())

    def test_hint_disclosures_stop_before_worked_decisions(self):
        text = next(iter(edition.build_weighted_task().values()))
        first = text.split('<summary>Show one hint</summary>', 1)[1].split('</details>', 1)[0]
        second = text.split('<summary>Show a second hint</summary>', 1)[1].split('</details>', 1)[0]
        self.assertNotIn('Converges', first + second)
        self.assertNotIn('The fixed-base clause therefore', first + second)
        self.assertLess(text.index('Show one hint'), text.index('Show the calculation and decisions'))

    def test_missing_or_duplicate_authored_region_refuses(self):
        for value in ('missing', '<!-- BEGIN x --><!-- BEGIN x --><!-- END x -->'):
            with self.assertRaises(edition.ReadingEditionError):
                edition.marked_region(value, 'x')

    def test_claim_only_mode_checks_without_building_large_edition(self):
        with patch.object(edition, 'build') as large:
            self.assertEqual(edition.main(['--claim', edition.WEIGHTED_ID, '--check']), 0)
            large.assert_not_called()


if __name__ == '__main__':
    unittest.main()
