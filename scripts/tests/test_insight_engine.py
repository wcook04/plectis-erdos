#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for the proposed read-only adapter. Register under check_ci_release.COMMANDS."""

import _test_bootstrap  # noqa: F401
import copy
import gzip
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import insight_engine as e

class InputTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
        (self.root/'a.txt').write_text('first\nsecond\nthird\n')
    def tearDown(self):self.tmp.cleanup()
    def test_span_identity(self):
        r=e.span(self.root,{'path':'a.txt','start':1,'end':2});self.assertEqual(e.span(self.root,r),r)
    def test_source_drift(self):
        r=e.span(self.root,{'path':'a.txt','start':1,'end':2});(self.root/'a.txt').write_text('changed\nsecond\n')
        with self.assertRaises(e.InputError):e.span(self.root,r)
    def test_range_outside_file(self):
        with self.assertRaises(e.InputError):e.span(self.root,{'path':'a.txt','start':0,'end':4})
    def test_boolean_not_line_number(self):
        with self.assertRaises(e.InputError):e.span(self.root,{'path':'a.txt','start':True,'end':2})
    def test_path_traversal(self):
        with self.assertRaises(e.InputError):e.regular_path(self.root,'../a.txt')
    def test_absolute_path(self):
        with self.assertRaises(e.InputError):e.regular_path(self.root,str(self.root/'a.txt'))
    def test_symlink(self):
        (self.root/'link').symlink_to(self.root/'a.txt')
        with self.assertRaises(e.InputError):e.regular_path(self.root,'link')
    def test_byte_limit(self):
        with self.assertRaises(e.InputError):e.read_bytes(self.root/'a.txt',2)
    def test_decompression_limit(self):
        p=self.root/'bomb.json.gz';p.write_bytes(gzip.compress(b'"'+b'a'*2000+b'"'))
        with self.assertRaises(e.InputError):e.read_json(p,100)
    def test_nonfinite(self):
        p=self.root/'x.json';p.write_text('{"x":NaN}')
        with self.assertRaises(e.InputError):e.read_json(p)
    def test_ambiguous_name(self):
        rs=[{'module':'A','name':'x'},{'module':'B','name':'x'}]
        with self.assertRaises(e.InputError):e.resolve(rs,'x')
        self.assertEqual(e.resolve(rs,'x','B')['module'],'B')

class ProposalTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
        self.rec={'mechanism_id':'x','authority':'proposal_not_canonical','novelty':'not_assessed',
                  'requirements':[{'id':'bounded','statement':'A uniform bound is required.'}], 'sources':[]}
    def tearDown(self):self.tmp.cleanup()
    def save(self,r):
        p=self.root/'rec.json';p.write_text(json.dumps({'schema':e.VERSION,'records':r}));return p
    def test_duplicate_record(self):
        with self.assertRaises(e.InputError):e.catalogue(self.save([self.rec,self.rec]))
    def test_cannot_grant_authority(self):
        r={**self.rec,'authority':'kernel_checked'}
        with self.assertRaises(e.InputError):e.catalogue(self.save([r]))
    def test_cannot_award_novelty(self):
        r={**self.rec,'novelty':'new'}
        with self.assertRaises(e.InputError):e.catalogue(self.save([r]))
    def test_cannot_omit_obligations(self):
        r={**self.rec,'requirements':[]}
        with self.assertRaises(e.InputError):e.catalogue(self.save([r]))
    def test_cannot_reuse_obligation_id(self):
        r={**self.rec,'requirements':self.rec['requirements']*2}
        with self.assertRaises(e.InputError):e.catalogue(self.save([r]))
    def test_string_mapping_never_discharges(self):
        r=e.obligation_plan(self.rec,{'source_id':'decl','context':'Gamma','target_statement':'P'},{'C':'True; proved'})
        self.assertFalse(r['verified_transfer']);self.assertEqual(r['requirements'][0]['verdict'],'unestablished')
    def test_empty_context_rejected_as_untyped(self):
        with self.assertRaises(e.InputError):e.obligation_plan(self.rec,{'source_id':'x','context':'','target_statement':'P'},{})
    def test_path_specific_world(self):
        self.assertEqual(e.world('lean/ErdosProblems/Erdos269/Some.lean'),'269')
        self.assertEqual(e.world('lean/Erdos249257/Some.lean'),'shared_or_unattributed')
    def test_no_match_is_empty_not_refuted(self):
        self.assertEqual(e.retrieve([], 'integer pulse'),[])
    def test_generated_certificate_excluded(self):
        d={'module':'a','name':'pulse','line':1,'signature':'pulse','generated_certificate':True}
        self.assertEqual(e.retrieve([d],'pulse'),[])
    def test_deterministic_tie(self):
        a={'module':'a','name':'pulse','line':1,'signature':'pulse'};b={**a,'module':'b'}
        self.assertEqual(e.retrieve([a,b],'pulse'),e.retrieve([b,a],'pulse'))
    def test_one_file_does_not_swamp_results(self):
        a={'module':'a','name':'pulse','line':1,'signature':'pulse'}
        rs=[{**a,'line':i} for i in range(10)]
        self.assertEqual(len(e.retrieve(rs,'pulse',k=10,per_module=2)),2)
    def test_archive_current_graph_blocked(self):
        (self.root/'lean-toolchain').write_text('leanprover/lean4:v4.29.1\n')
        p=self.root/'g.json';p.write_text(json.dumps({'source':{'source_revision':'/private/ref.txt','lean_version':'4.29.1'}}))
        o=e.graph_preflight(self.root,p,'a'*40)
        self.assertEqual(o['status'],'blocked_current_graph')
        self.assertIn('graph_source_revision_is_not_a_full_commit',o['reasons'])
    def test_even_matching_commit_does_not_authenticate_export(self):
        (self.root/'lean-toolchain').write_text('leanprover/lean4:v4.29.1\n')
        p=self.root/'g.json';p.write_text(json.dumps({'source':{'source_revision':'a'*40,'lean_version':'4.29.1'}}))
        o=e.native(self.root,p,'a'*40,'transfer',[])
        self.assertEqual(o['status'],'blocked_current_graph')

class NativeCatalogueTests(unittest.TestCase):
    def test_default_catalogue_is_bound_to_authored_mechanisms(self):
        root=Path(__file__).resolve().parents[2]
        records=e.native_catalogue(root)
        self.assertEqual({r['mechanism_id'] for r in records},
                         {r['mechanism_id'] for r in e.read_json(root/'docs/semantic/lab/mechanisms.json')})
        self.assertTrue(all(r['authority']=='authored_mechanism_explanation'
                            and r['requirements'] and r['novelty']=='not_assessed' for r in records))
        first=next(r for r in records if r['mechanism_id']=='modular_gap_denominator_exclusion')
        self.assertIn('lean/Erdos249257/CertificateKernel.lean',first['origin_modules'])
    def test_origin_exclusion_is_applied_to_native_record(self):
        root=Path(__file__).resolve().parents[2]
        record=next(r for r in e.native_catalogue(root)
                    if r['mechanism_id']=='modular_gap_denominator_exclusion')
        result=e.forward(root,[record],record['mechanism_id'],k=3,exclude_origin=True)
        self.assertTrue(all(c['source']['path'] not in record['origin_modules']
                            for c in result['candidates']))
        self.assertEqual(result['verified_transfers'],0)

if __name__=='__main__':unittest.main()
