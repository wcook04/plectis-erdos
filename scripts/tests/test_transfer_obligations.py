#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Native graph tests. Set PLECTIS_REPO to the reviewed checkout, or install beside
build_argument_continuations.py. Register in check_ci_release.COMMANDS AND run -O.
"""

import _test_bootstrap  # noqa: F401
import os
from pathlib import Path
import sys
import unittest
import transfer_obligations as t

native=os.environ.get('PLECTIS_REPO')
if native:sys.path.insert(0,str(Path(native)/'scripts'))
try:
    import build_argument_continuations as b
except ImportError:
    b=None

def graph(edges, refutations=()):
    keys={'A','B','T','F'}
    p={'schema':'erdos249257-argument-continuation-graph/2',
       'statements':[{'key':k,'type':'False' if k=='F' else k} for k in sorted(keys)],
       'reductions':[{'statement':head,'producer':f'p{i}','residuals':list(rs)} for i,(head,rs) in enumerate(edges)],
       'refutations':[{'statement':head,'producer':f'r{i}','residuals':list(rs)} for i,(head,rs) in enumerate(refutations)]}
    g=b.Graph.from_payload(p);g.analyse();return g

def row(*rs):return {'supplies':'T','open_residuals':list(rs)}

@unittest.skipIf(b is None,'native owner not available; set PLECTIS_REPO')
class NativeTests(unittest.TestCase):
    def test_refuted_input_is_not_a_transfer(self):
        g=graph([('T',['A'])],[('A',[])])
        self.assertEqual(t.classify(g,row('A'))['decision'],'refuted_residual')
    def test_joint_contradiction_not_detected_individually(self):
        g=graph([('T',['A','B']),('F',['A','B'])])
        self.assertNotIn('A',g.refuted);self.assertNotIn('B',g.refuted)
        self.assertEqual(t.classify(g,row('A','B'))['decision'],'refuted_jointly')
    def test_endpoint_equivalence(self):
        g=graph([('T',['A']),('A',['T'])])
        self.assertEqual(t.classify(g,row('A'))['decision'],'endpoint_equivalent')
    def test_one_way_is_not_strictness(self):
        g=graph([('T',['A'])]);r=t.classify(g,row('A'))
        self.assertEqual(r['decision'],'candidate_not_proved_useful')
        self.assertEqual(r['satisfiability'],'not_established')
    def test_zero_work_abstains(self):
        g=graph([('T',['A'])]);self.assertEqual(t.classify(g,row('A'),max_work=0)['decision'],'unknown_budget')
    def test_unknown_key_abstains(self):
        g=graph([]);self.assertEqual(t.classify(g,row('MISSING'))['decision'],'unknown_key')
    def test_inconsistent_base_abstains(self):
        g=graph([('A',[])],[('A',[])])
        self.assertEqual(t.classify(g,row('B'))['decision'],'base_graph_inconsistent')
    def test_check_budget_is_preserved(self):
        g=graph([('T',['A'])]);o=t.screen(g,[row('A'),row('A')],max_checks=1)
        self.assertEqual(o['joint_checks'],1);self.assertEqual(o['rows'][1]['obligation_screen']['decision'],'unknown_budget')
    def test_negative_budget_refused(self):
        g=graph([])
        with self.assertRaises(ValueError):t.screen(g,[],max_checks=-1)
    def test_preserves_original_input(self):
        g=graph([('T',['A'])]);r=row('A');o=t.screen(g,[r]);self.assertNotIn('obligation_screen',r)
    def test_scalar_metadata_never_awards_novelty(self):
        g=graph([('T',['A'])]);self.assertEqual(t.classify(g,row('A'))['novelty'],'not_assessed')
    def test_four_letter_counterexample_from_paper(self):
        def f(xs):
            suffix=1;total=0
            for x in reversed(xs):total+=suffix;suffix*=x
            return total
        self.assertEqual(f([5,7,3,2]),51);self.assertEqual(f([7,2,3,5]),51)

if __name__=='__main__':unittest.main()
