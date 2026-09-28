# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Owner: public scripts/test_compile_research_packet.py (new sibling suite).
Run with PLECTIS_ROOT and PLECTIS_CANDIDATE_SCRIPTS, or installed in scripts/.
"""
import os
import json
import sys
import unittest
from pathlib import Path
ROOT=Path(os.environ.get('PLECTIS_ROOT', str(Path(__file__).resolve().parents[1])))
sys.path.insert(0,str(ROOT/'scripts'))
sys.path.insert(0,os.environ.get('PLECTIS_CANDIDATE_SCRIPTS', str(ROOT/'scripts')))
import compile_research_packet as crp
import test_compile_research_packet as t
# The legacy fixture inserts its own scripts directory; keep the imported candidate.
t.crp=crp

class SafetyTests(unittest.TestCase):
    def test_guard_cannot_be_overridden_in_dispatch_profile(self):
        spec=t.base_spec(protect_contrasts=True, include_triggered_contrasts=True,
            target={'problem':7,'anchor':'Demo','declarations':[]},
            obligations=[{'id':'replacement','origin':'contrast:c-demo','alternatives':[['c-part']]}])
        with self.assertRaisesRegex(crp.SpecError,'protected contrast'):
            t.Repo(self).compile(spec)

    def test_protected_mode_retains_additional_views_and_guard(self):
        result=t.Repo(self).compile(t.base_spec(protect_contrasts=True,
            include_triggered_contrasts=True, target={'problem':7,'anchor':'Demo','declarations':[]}))
        self.assertEqual(result['manifest']['ask_type_b']['disconfirming_check'],
                         ['[c-demo] Name the telescope.'])
        self.assertIn('contrast-c-demo',[r['id'] for r in result['receipt']['obligations']])

    def test_invalid_boolean_is_not_accepted(self):
        with self.assertRaises(crp.SpecError):
            t.Repo(self).compile(t.base_spec(protect_contrasts='true'))

    def test_raw_payload_copy_is_blocked_despite_new_path(self):
        repo=t.Repo(self)
        for path in ['notes/private.md','notes/copy.md']:
            t.write(repo.root,path,'secret first\nsecret second\n')
        resources=t.base_spec()['resources']+[
            t.span('private','notes/private.md',1,2),t.span('copy','notes/copy.md',1,2)]
        result=repo.compile(t.base_spec(resources=resources,withheld=['private'],
            obligations=[{'id':'leak','alternatives':[['copy']]}]))
        self.assertEqual(result['status'],'refused_infeasible_in_declared_model')
        self.assertEqual(result['receipt']['blocked']['copy'],'same_bytes_as_blocked:private')

    def test_subspan_of_copy_is_blocked(self):
        repo=t.Repo(self)
        for path in ['notes/private.md','notes/copy.md']:
            t.write(repo.root,path,'secret first\nsecret second\n')
        result=repo.compile(t.base_spec(resources=t.base_spec()['resources']+[
            t.span('private','notes/private.md',1,2),t.span('copy','notes/copy.md',1,2),
            t.span('partial','notes/copy.md',2,2)],withheld=['private'],
            obligations=[{'id':'leak','alternatives':[['partial']]}]))
        self.assertEqual(result['status'],'refused_infeasible_in_declared_model')
        self.assertIn('partial',result['receipt']['blocked'])

    def test_payload_hash_is_not_rendered_hash(self):
        result=t.Repo(self).compile(t.base_spec())
        row=result['receipt']['resources'][0]
        self.assertNotEqual(row['payload_sha256'],row['excerpt_sha256'])
        self.assertEqual(len(row['payload_sha256']),64)

    def test_interval_overlap_does_not_taint_unrelated_lines(self):
        repo=t.Repo(self)
        result=repo.compile(t.base_spec(resources=t.base_spec()['resources']+[
            t.span('secret','notes/C.md',1,2),t.span('overlap','notes/C.md',2,9),
            t.span('safe','notes/C.md',8,10)],withheld=['secret'],
            obligations=[{'id':'safe','alternatives':[['safe']]}]))
        self.assertEqual(result['status'],'compiled')
        self.assertNotIn('safe',result['receipt']['blocked'])

class ContrastDirectionTests(unittest.TestCase):
    def test_fixed_contrast_matches_the_existing_direction(self):
        default=Path(__file__).resolve().parents[1]/'patched_public/docs/research-commons/record/contrasts.json'
        path=default if default.exists() else ROOT/'docs/research-commons/record/contrasts.json'
        row=next(r for r in json.loads(path.read_text())['rows']
                 if r['id']=='c-slot-replacement-not-weakening')
        self.assertIn('satisfies R and fails H once R reconstructs H',row['right_reading'])
        self.assertNotIn('satisfies H and fails R once R reconstructs H',row['right_reading'])
        contract=(ROOT/'lean/ErdosProblems/ArgumentGraph/Contracts.lean').read_text()
        self.assertIn('reconstruct : Entails Γ R H',contract)
    def test_boolean_countermodel_is_feasible_not_vacuous(self):
        xs=[False,True]
        gamma=lambda x: True
        h=lambda x: True
        r=lambda x: x
        self.assertTrue(all(not (gamma(x) and r(x)) or h(x) for x in xs))
        self.assertTrue(any(gamma(x) and r(x) for x in xs))
        self.assertTrue(any(gamma(x) and h(x) and not r(x) for x in xs))
        self.assertFalse(any(gamma(x) and r(x) and not h(x) for x in xs))

if __name__=='__main__': unittest.main()
