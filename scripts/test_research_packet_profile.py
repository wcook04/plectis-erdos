# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
import copy
import gzip
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(os.environ.get('PLECTIS_ROOT', str(Path(__file__).resolve().parents[1])))
HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
sys.path.insert(0,os.environ.get('PLECTIS_CANDIDATE_SCRIPTS', str(ROOT/'scripts')))
import compile_research_packet as native
import test_compile_research_packet as fixture
fixture.crp=native
sys.path.insert(0,str(HERE/'scripts'))
import research_packet_profile as profile


def docs(commit='a'*40,arm='informed'):
    roles={r:{'status':'not_applicable','reason':'Only a compiler fixture, not a mathematical task.',
              'resources':[]} for r in profile.ROLES}
    for r,ids in [('target',['target']),('scope',['b-short']),('frontier',['b-long']),
                  ('baseline',['target'])]:
        roles[r]={'status':'evidence','reason':'Exact fixture source, not kernel evidence.','resources':ids}
    roles['negative_routes']={'status':'unknown','reason':'No failure catalogue in this fixture.', 'resources':[]}
    p={'schema':'plectis-packet-profile/1','wave_id':'wave7','round_id':'r7-p3','arm':arm,'roles':roles}
    b={'schema':'plectis-first-attempt/1','baseline_id':'fixture-first-attempt','source_commit':commit,
       'public_fact_resources':['target'],'route_resources':['c-part'],
       'attempts':[{'kind':'fixture','outcome':'syntax-only; no Lean invocation'}],
       'cost':{'elapsed_seconds':None,'status':'not_measured'}}
    return p,b

def git_pin(repo):
    for cmd in [('init','-q'),('add','-A'),('commit','-q','-m','fixture')]:
        subprocess.run(['git','-C',str(repo.root),'-c','user.name=fixture',
                        '-c','user.email=f@example.invalid','-c','commit.gpgsign=false',*cmd],
                       check=True,capture_output=True)
    return subprocess.check_output(['git','-C',str(repo.root),'rev-parse','HEAD'],text=True).strip()

class ProfileTests(unittest.TestCase):
    def make(self,arm='informed'):
        repo=fixture.Repo(self)
        commit=git_pin(repo)
        p,b=docs(commit,arm)
        return repo,p,b

    def test_pinned_profile_calls_native_compiler_and_preserves_manifest_binding(self):
        repo,p,b=self.make()
        r=profile.prepare(fixture.base_spec(),p,b,root=repo.root)
        self.assertEqual(r['status'],'pinned_dispatch_candidate')
        self.assertTrue(r['native']['receipt']['protect_contrasts'])
        self.assertEqual(r['receipt']['native_manifest_sha256'],r['native']['receipt']['manifest_sha256'])
        self.assertEqual(r['bindings'],r['manifest']['return_contract']['bindings'])
        self.assertEqual(r['bindings']['baseline_sha256'],profile.digest(b))
        self.assertIn('not_certified',r['receipt'])

    def test_baseline_mismatch_refuses(self):
        repo,p,b=self.make(); b['source_commit']='f'*40
        with self.assertRaisesRegex(profile.ProfileError,'source commit differ'):
            profile.prepare(fixture.base_spec(),p,b,root=repo.root)

    def test_missing_role_not_silently_accepted(self):
        repo,p,b=self.make(); del p['roles']['literature']
        with self.assertRaises(profile.ProfileError): profile.prepare(fixture.base_spec(),p,b,root=repo.root)

    def test_role_resource_unknown_refuses(self):
        repo,p,b=self.make(); p['roles']['scope']['resources']=['missing']
        with self.assertRaises(profile.ProfileError): profile.prepare(fixture.base_spec(),p,b,root=repo.root)

    def test_blind_route_not_selected(self):
        repo,p,b=self.make('blind_route')
        r=profile.prepare(fixture.base_spec(),p,b,root=repo.root)
        self.assertNotIn('c-part',r['native']['receipt']['selected'])
        self.assertIn('c-part',r['native']['receipt']['blocked'])

    def test_blind_route_required_by_role_refuses_not_weakens(self):
        repo,p,b=self.make('blind_route'); p['roles']['scope']['resources']=['c-part']
        r=profile.prepare(fixture.base_spec(),p,b,root=repo.root)
        self.assertEqual(r['status'],'refused_infeasible_in_declared_model')

    def test_snapshot_is_review_only(self):
        repo=fixture.Repo(self); p,b=docs()
        r=profile.prepare(fixture.base_spec(),p,b,root=repo.root,ref=None,review_only=True)
        self.assertEqual(r['status'],'snapshot_review_only')

    def test_baseline_hash_commits_attempt_and_cost(self):
        _,b=docs(); b2=copy.deepcopy(b); b2['cost']['elapsed_seconds']=5
        self.assertNotEqual(profile.digest(b),profile.digest(b2))

    def test_graph_with_path_revision_is_not_current_authority(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'graph.json.gz'
            with gzip.open(path,'wb') as f:
                f.write(json.dumps({'source':{'source_revision':'/private/revision.txt',
                       'lean_tree':'a'*40,'export_summary':{'truncated':True}}}).encode())
            r=profile.assess_graph(path,'a'*40)
            self.assertIn('source_revision_is_not_a_commit',r['identity_problems'])
            self.assertFalse(r['absence_or_novelty_authority'])

    def test_untruncated_graph_still_is_not_a_novelty_oracle(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'graph.json'
            path.write_text(json.dumps({'source':{'source_revision':'b'*40,'lean_tree':'a'*40,
                                                 'export_summary':{'truncated':False}}}))
            r=profile.assess_graph(path,'a'*40)
            self.assertEqual(r['state'],'identity_fields_match')
            self.assertFalse(r['absence_or_novelty_authority'])

class DeliveryTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        (self.root/'00_ASK_TYPE_B.md').write_text('Ask\n')
        (self.root/'01_DECISION_BRIEF.md').write_text('Brief\n')
        self.kw={'first_read':['00_ASK_TYPE_B.md','01_DECISION_BRIEF.md'],
                 'first_read_budget':1_000,'total_budget':10_000}
    def test_generated_bytes_are_counted(self):
        r=profile.audit_delivery(self.root,**self.kw)
        self.assertEqual(r['total_bytes'],10)
    def test_extra_bytes_exceed_total_budget(self):
        (self.root/'extra.md').write_bytes(b'x'*10_000)
        with self.assertRaises(profile.ProfileError): profile.audit_delivery(self.root,**self.kw)
    def test_first_read_budget_is_separate(self):
        self.kw['first_read_budget']=1
        with self.assertRaises(profile.ProfileError): profile.audit_delivery(self.root,**self.kw)
    def test_forbidden_literal_reappears_in_generated_guide(self):
        (self.root/'generated.md').write_text('A secret route.\n')
        with self.assertRaises(profile.ProfileError):
            profile.audit_delivery(self.root,forbidden_payloads=[b'secret route'],**self.kw)
    def test_json_escaped_forbidden_payload_refuses(self):
        (self.root/'generated.json').write_text(json.dumps({'text':'private\nroute'}))
        with self.assertRaises(profile.ProfileError):
            profile.audit_delivery(self.root,forbidden_payloads=[b'private\nroute'],**self.kw)
    def test_nested_archive_refuses(self):
        (self.root/'reserve.zip').write_bytes(b'fake')
        with self.assertRaises(profile.ProfileError): profile.audit_delivery(self.root,**self.kw)
    def test_case_collision_refuses(self):
        (self.root/'one.md').write_text('x'); (self.root/'ONE.md').write_text('y')
        if (self.root/'one.md').samefile(self.root/'ONE.md'):
            self.skipTest('filesystem does not preserve case-distinct filenames')
        with self.assertRaises(profile.ProfileError): profile.audit_delivery(self.root,**self.kw)
    def test_symlink_refuses(self):
        (self.root/'link').symlink_to(self.root/'00_ASK_TYPE_B.md')
        with self.assertRaises(profile.ProfileError): profile.audit_delivery(self.root,**self.kw)

if __name__=='__main__': unittest.main()
