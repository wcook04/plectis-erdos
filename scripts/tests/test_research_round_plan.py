
import _test_bootstrap  # noqa: F401
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
import copy
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import unittest
from unittest import mock
import zipfile

HERE=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(Path(__file__).resolve().parent))
sys.path.insert(0,str(HERE/'scripts'))
import research_round_plan as plan


def binding(packet='p3',round_id='r7-p3',arm='informed'):
    return {'wave_id':'wave7','round_id':round_id,'packet_id':packet,'source_commit':'a'*40,
            'baseline_sha256':'b'*64,'arm':arm,'dispatch_id':('c' if packet=='p3' else 'd')*64}

def component(cid='fix',**kw):
    c={'id':cid,'kind':'code','statement':'Protect selected contrast gates.','scope':'Frozen compiler fixture.',
       'polarity':'asserts','depends_on':[],'owner_paths':['scripts/compile_research_packet.py'],
       'evidence_paths':['REPORT.md']}
    c.update(kw); return c

def envelope(rid='return-p3',bindings=None,components=None,files=None):
    files=files or {'REPORT.md':b'Fixture only; no corpus theorem checked.\n','SOURCES.md':b'No external source in this fixture.\n'}
    e={'schema':'plectis-research-return/1','return_id':rid,'bindings':bindings or binding(),
       'artifacts':{name:{'sha256':plan.sha(data),'bytes':len(data)} for name,data in files.items()},
       'components':components if components is not None else [component()],
       'limitations':['Integrity validation is not acceptance.']}
    return e,files

def make_zip(path,e,files,extras=None):
    with zipfile.ZipFile(path,'w',zipfile.ZIP_DEFLATED) as z:
        z.writestr('RETURN.json',plan.canonical(e))
        for name,body in files.items(): z.writestr(name,body)
        for name,body in extras or []: z.writestr(name,body)

class ReturnTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.path=Path(self.tmp.name)/'return.zip'
        self.e,self.files=envelope()
    def valid(self):
        make_zip(self.path,self.e,self.files)
        return plan.validate_return(self.path,binding())
    def test_valid_is_not_accepted(self):
        self.assertEqual(self.valid()['status'],'integrity_checked_not_accepted')
    def test_wrong_frozen_binding_refuses(self):
        make_zip(self.path,self.e,self.files); expected=binding(); expected['baseline_sha256']='f'*64
        with self.assertRaisesRegex(plan.ReturnError,'wrong packet'): plan.validate_return(self.path,expected)
    def test_bad_artifact_hash_refuses(self):
        self.e['artifacts']['REPORT.md']['sha256']='f'*64
        with self.assertRaises(plan.ReturnError): self.valid()
    def test_undeclared_file_refuses(self):
        make_zip(self.path,self.e,self.files,[('hidden.md',b'not declared')])
        with self.assertRaises(plan.ReturnError): plan.validate_return(self.path,binding())
    def test_path_traversal_refuses(self):
        make_zip(self.path,self.e,self.files,[('../outside.py',b'print(1)')])
        with self.assertRaises(plan.ReturnError): plan.validate_return(self.path,binding())
    def test_case_collision_refuses(self):
        make_zip(self.path,self.e,self.files,[('report.md',b'collision')])
        with self.assertRaises(plan.ReturnError): plan.validate_return(self.path,binding())
    def test_duplicate_member_refuses(self):
        make_zip(self.path,self.e,self.files)
        with zipfile.ZipFile(self.path,'a') as z: z.writestr('REPORT.md',b'collision')
        with self.assertRaises(plan.ReturnError): plan.validate_return(self.path,binding())
    def test_symlink_member_refuses(self):
        make_zip(self.path,self.e,self.files)
        info=zipfile.ZipInfo('link'); info.create_system=3
        info.external_attr=(stat.S_IFLNK|0o777)<<16
        with zipfile.ZipFile(self.path,'a') as z: z.writestr(info,'../../secret')
        with self.assertRaises(plan.ReturnError): plan.validate_return(self.path,binding())
    def test_nested_archive_refuses(self):
        self.files['nested.zip']=b'PK\x03\x04'
        self.e['artifacts']['nested.zip']={'sha256':plan.sha(self.files['nested.zip']),'bytes':4}
        with self.assertRaises(plan.ReturnError): self.valid()
    def test_ingress_byte_budget_refuses(self):
        make_zip(self.path,self.e,self.files)
        with self.assertRaises(plan.ReturnError): plan.validate_return(self.path,binding(),max_member_bytes=10)
    def test_duplicate_json_key_refuses(self):
        make_zip(self.path,self.e,self.files)
        data=plan.canonical(self.e).decode().replace('{','{"schema":"other",',1)
        with zipfile.ZipFile(self.path,'w') as z:
            z.writestr('RETURN.json',data)
            for n,b in self.files.items(): z.writestr(n,b)
        with self.assertRaises(plan.ReturnError): plan.validate_return(self.path,binding())
    def test_missing_component_evidence_refuses(self):
        self.e['components'][0]['evidence_paths']=['missing.lean']
        with self.assertRaises(plan.ReturnError): self.valid()
    def test_no_execution_of_returned_program(self):
        marker=Path(self.tmp.name)/'executed'
        self.files['candidate.py']=f'open({str(marker)!r},"w").write("BAD")'.encode()
        self.e['artifacts']['candidate.py']={'sha256':plan.sha(self.files['candidate.py']),
                                           'bytes':len(self.files['candidate.py'])}
        self.valid(); self.assertFalse(marker.exists())

class ReconciliationTests(unittest.TestCase):
    def return_object(self,rid='a',components=None,b=None):
        e,_=envelope(rid,b,components)
        return {'status':'integrity_checked_not_accepted','zip_sha256':plan.sha(plan.canonical(e)),
                'zip_bytes':1000,'envelope':e}
    def test_dependencies_before_consumers(self):
        r=self.return_object(components=[component('base'),component('uses',depends_on=['base'])])
        p=plan.reconciliation_plan([r])
        self.assertEqual(p['integration_layers'],[['a:base'],['a:uses']])
        self.assertEqual(p['acceptance'].split(';')[0],'none')
    def test_cycle_blocks_instead_of_topological_fabrication(self):
        r=self.return_object(components=[component('x',depends_on=['y']),component('y',depends_on=['x'])])
        p=plan.reconciliation_plan([r]); self.assertEqual(p['integration_layers'],[])
        self.assertEqual(p['cycle_or_dependent_on_cycle'],['a:x','a:y'])
    def test_missing_dependency_and_consumers_blocked(self):
        r=self.return_object(components=[component('x',depends_on=['unknown']),component('y',depends_on=['x'])])
        p=plan.reconciliation_plan([r])
        self.assertEqual(p['blocked_by_missing_or_conflict'],['a:x','a:y'])
    def test_opposite_claims_quarantined_not_voted(self):
        r1=self.return_object('a',[component('x')]); r2=self.return_object('b',[component('x',polarity='denies')])
        p=plan.reconciliation_plan([r1,r2])
        self.assertEqual(p['opposite_authored_claim_groups'],[['a:x','b:x']])
        self.assertEqual(p['integration_layers'],[])
    def test_different_scope_not_silently_contradictory(self):
        r1=self.return_object('a',[component('x')]); r2=self.return_object('b',[component('x',scope='Other domain.',polarity='denies')])
        p=plan.reconciliation_plan([r1,r2]); self.assertEqual(p['opposite_authored_claim_groups'],[])
    def test_identical_text_keeps_both_for_review(self):
        p=plan.reconciliation_plan([self.return_object('a'),self.return_object('b')])
        self.assertEqual(p['identical_authored_statement_groups'],[['a:fix','b:fix']])
        self.assertEqual(p['integration_layers'],[['a:fix','b:fix']])
        self.assertEqual(p['serialize_owner_paths']['scripts/compile_research_packet.py'],['a:fix','b:fix'])
    def test_mixed_baseline_refused(self):
        b=binding('p4','r7-p4'); b['baseline_sha256']='e'*64
        with self.assertRaises(plan.ReturnError): plan.reconciliation_plan([self.return_object('a'),self.return_object('b',b=b)])
    def test_reused_return_id_changed_bytes_refused(self):
        a=self.return_object(); b=copy.deepcopy(a); b['zip_sha256']='f'*64
        with self.assertRaises(plan.ReturnError): plan.reconciliation_plan([a,b])
    def test_exact_repeated_zip_is_custody_group_only(self):
        a=self.return_object(); p=plan.reconciliation_plan([a,a])
        self.assertEqual(p['exact_zip_repeat_groups'],[['a','a']])
        self.assertEqual(p['integration_layers'],[['a:fix']])
    def test_native_events_pass_existing_owner_schema_and_replay(self):
        import research_record as journal
        b=binding()
        opened=plan.round_opened_proposal(b,'e'*64,'Audit compiler guard retention.',['compiler','papers'])
        r=self.return_object('a')
        received=plan.journal_received_proposal(r,{
                    'return_id':'arrival-a','sha256':r['zip_sha256'],'byte_length':r['zip_bytes'],
                    'packet_or_run_identity':r['envelope']['bindings']['dispatch_id']},batch_id='batch7')
        for e in [opened,received]:
            self.assertEqual(journal.detail_errors(e['kind'],e['subject'],e['detail']),[])
        # Simulate a maintainer process ONLY inside the disposable fixture.
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(os.environ, {k: v for k, v in os.environ.items() if k != 'CI'}, clear=True):
            for e in [opened,received]: journal.append(Path(tmp),e['kind'],e['subject'],e['detail'])
            events,state=journal.replay(Path(tmp))
            self.assertEqual(len(events),2)
class SplitTests(unittest.TestCase):
    def missions(self):
        return [{'id':'p2','decision':'Substrate interface','boundary':'No caller mutation',
                 'deliverables':['schema'],'depends_on':[],'owner_paths':['scripts/shared.py'],'mode':'production'},
                {'id':'p3','decision':'Packet compiler','boundary':'Consume frozen interface',
                 'deliverables':['compiler'],'depends_on':['p2'],'owner_paths':['scripts/shared.py'],'mode':'production'}]
    def test_split_has_integration_order_and_owner_collision(self):
        p=plan.split_wave(self.missions())
        self.assertEqual(p['integration_layers'],[['p2'],['p3']])
        self.assertEqual(p['serialize_owner_paths']['scripts/shared.py'],['p2','p3'])
    def test_duplicate_production_deliverable_refuses(self):
        m=self.missions(); m[1]['deliverables']=['schema']
        with self.assertRaises(plan.ReturnError): plan.split_wave(m)
    def test_replication_must_be_explicit(self):
        m=self.missions(); m[1].update(mode='replication',replicate_of='p2',deliverables=['schema'])
        self.assertEqual(plan.split_wave(m)['deliverable_owners'],{'schema':'p2'})
    def test_cycle_refuses(self):
        m=self.missions(); m[0]['depends_on']=['p3']
        with self.assertRaises(plan.ReturnError): plan.split_wave(m)
    def test_custody_precedes_parsing_even_for_invalid_zip(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'raw.zip'; p.write_bytes(b'opaque invalid ZIP retained for custody')
            result=plan.custody_plan(p,arrival_id='arrival1',batch_id='batch7',bindings=binding(),
                                    intake_script=Path('/fixture/type_b_return_intake.py'))
            self.assertEqual(result['expected_sha256'],plan.sha(p.read_bytes()))
            self.assertEqual(result['custody_argv'][1][2],'add')
    def test_journal_proposal_refuses_changed_custody(self):
        r=ReconciliationTests().return_object('a')
        row={'return_id':'arrival-a','sha256':'f'*64,'byte_length':1000,
             'packet_or_run_identity':binding()['dispatch_id']}
        with self.assertRaises(plan.ReturnError): plan.journal_received_proposal(r,row,batch_id='batch7')

if __name__=='__main__': unittest.main()
