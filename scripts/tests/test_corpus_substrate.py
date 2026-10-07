#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Proposed native tests. Run plain and -O. No Lean installation is required.
The synthetic hooks deliberately do NOT act as proof/attestation authorities.
"""
from __future__ import annotations

import _test_bootstrap  # noqa: F401
import copy
import json
import subprocess
import sys
from pathlib import Path
import sqlite3
import tempfile
import unittest
import research_record
import corpus_substrate as s


class FakeOwners:
    def resolve(self, name, module):
        return {"state":"absent","atlas_id":None,"candidates":[]}
    def attest(self,row): return {"state":"attested","type_head":"Equivalent"}
    def triggered(self,rows,number): return [{"id":r["id"]} for r in rows]
    def events(self,path): return []


def fixture(root):
    docs = {
        "claim":{"claims":[
            {"id":"erdos_249","status":"open","statement":"Target remains open.","declarations":[],"remaining_open_proposition_ids":[]},
            {"id":"shared","status":"proved here","statement":"Shared result, not a solution.","declarations":[],"remaining_open_proposition_ids":[]},
            {"id":"route_result","status":"conditional reduction","statement":"H suffices for the target.","declarations":[],"remaining_open_proposition_ids":["need"]}],
            "remaining_open_propositions":[{"id":"need","open_target_claim":"erdos_249","statement":"Prove H.","status":"open"}],"release":{}},
        "problem":{"problems":[{"erdos_number":249,"claim_registration":{"programme_claim_id":"erdos_249","registered_claim_ids":["route_result"]}}]},
        "declaration":{"declarations":[],"source_fingerprint":"f"},
        "dependency":{"nodes":[],"edges":[],"source_fingerprint":"f"},
        "paper_result":{"rows":[{"id":"paper1","problem":249,"lean":{"status":"exact","declarations":[]},"comparator":{"status":"queued"}}]},
        "relation":{"rows":[{"id":"eq","problem":249,"left":"P","right":"Q","context":"ctx","relation":"equivalent"}]},
        "contrast":{"rows":[{"id":"misread","right_reading":"H was not proved."}]},
        "route":{"readers":[{"routes":[{"id":"cross","world":"251->269","closure":"attempt_closed"},{"id":"synth","world":"synthesis"}]}],"reopened":{"R1":{"note":"Retry under different hypotheses."}}},
    }
    for owner,path in s.OWNER.items():
        p=root/path;p.parent.mkdir(parents=True,exist_ok=True)
        p.write_text("" if owner=="event" else json.dumps(docs[owner]),encoding="utf-8")
    return docs


class ModelTest(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)/"repo";self.root.mkdir()
        self.docs=fixture(self.root);self.path=Path(self.tmp.name)/"model.sqlite"
        s.build(self.root,self.path,hooks=FakeOwners())
    def tearDown(self): self.tmp.cleanup()
    def test_native_journal_rejects_hash_valid_semantic_corruption(self):
        body = {"sequence": 0, "previous": research_record.ZERO,
                "kind": "invented_event", "subject": "fixture", "detail": {},
                "recorded_at": "2026-09-28T00:00:00Z"}
        event = dict(body, event_sha=research_record.event_hash(body))
        path = research_record.journal_path(self.root)
        path.write_text(research_record.canonical(event) + "\n")
        self.assertEqual(len(research_record.read_events(path)), 1)
        owner = s.NativeOwners.__new__(s.NativeOwners)
        owner.root, owner.record = self.root, research_record
        with self.assertRaisesRegex(s.SubstrateError, "native journal rejected"):
            owner.events(path)
    def write(self,owner):
        (self.root/s.OWNER[owner]).write_text(json.dumps(self.docs[owner]),encoding="utf-8")
    def test_complete_claim_coverage(self):
        with s.View(self.root,self.path) as v:
            self.assertEqual({r['id'] for r in v.rows('claim')},{'erdos_249','shared','route_result'})
            index = v.register()
            self.assertNotIn('Shared result, not a solution.', index)
            for ident in ('erdos_249', 'shared', 'route_result'):
                self.assertEqual(index.count(f'<a id="{ident}"></a>'), 1)
            self.assertIn('open (1)', index)
            self.assertIn(v.meta['snapshot_id'], index)
            self.assertEqual(v.node('claim', 'shared')['record'], self.docs['claim']['claims'][1])
    def test_complete_record_cli_and_export_survive_compact_index(self):
        command = [sys.executable, str(Path(s.__file__).resolve()), '--root', str(self.root),
                   '--database', str(self.path)]
        node = subprocess.run(command + ['--node', 'claim', 'shared'], capture_output=True, text=True)
        self.assertEqual(node.returncode, 0, node.stderr)
        row = json.loads(node.stdout)
        self.assertEqual(row['record'], self.docs['claim']['claims'][1])
        self.assertEqual(row['source']['path'], s.OWNER['claim'])
        self.assertTrue(row['source']['sha256'].startswith('sha256:'))
        exported = subprocess.run(command + ['--rows', 'claim'], capture_output=True, text=True)
        self.assertEqual(exported.returncode, 0, exported.stderr)
        self.assertEqual({r['id']: r['record'] for r in json.loads(exported.stdout)['rows']},
                         {r['id']: r for r in self.docs['claim']['claims']})
        self.docs['claim']['claims'][1]['statement'] = 'Changed after cache build.'
        self.write('claim')
        stale = subprocess.run(command + ['--node', 'claim', 'shared'], capture_output=True, text=True)
        self.assertNotEqual(stale.returncode, 0)
        self.assertIn('stale substrate', stale.stderr)

    def test_cross_and_synthesis_retained(self):
        with s.View(self.root,self.path) as v:
            self.assertEqual(len(v.cross_problem()['routes']),2)
            self.assertEqual(len(v.cross_problem()['reopenings']),1)
    def test_parent_open_and_condition_preserved(self):
        with s.View(self.root,self.path) as v:
            p=v.frontier(249)
            self.assertEqual(p['programme']['record']['status'],'open')
            self.assertEqual(p['registered_open_obligations'][0]['record']['statement'],'Prove H.')
            self.assertEqual(p['strongest_result']['state'],'not_established')
    def test_unassigned_is_not_discarded(self):
        with s.View(self.root,self.path) as v:
            self.assertEqual(v.frontier(249)['global_registry']['unassigned_claims'],1)
    def test_pending_comparator_not_promoted(self):
        with s.View(self.root,self.path) as v:
            self.assertEqual(v.frontier(249)['paper_result_coverage']['status_counts'],{'queued':1})
    def test_native_attested_does_not_enable_inference(self):
        with s.View(self.root,self.path) as v:
            rel=v.rows('relation')[0]['record']
            self.assertEqual(rel['native_certificate_observation']['state'],'attested')
            self.assertFalse(rel['inference_eligible'])
    def test_false_true_metadata_stays_quarantined(self):
        r=copy.deepcopy(self.docs['relation']['rows'][0]);r.update(left='False',right='True',inference_eligible=True)
        self.assertFalse(s.quarantined_relation(r,{'state':'attested'})['inference_eligible'])
    def test_source_change_refuses_old_index(self):
        self.docs['claim']['claims'][0]['statement']='Changed target.';self.write('claim')
        with self.assertRaises(s.SubstrateError):s.View(self.root,self.path)
    def test_added_source_refuses_old_index(self):
        p=self.root/'lean/New.lean';p.parent.mkdir();p.write_text('-- new source')
        with self.assertRaises(s.SubstrateError):s.View(self.root,self.path)
    def test_missing_owner_refuses(self):
        (self.root/s.OWNER['route']).unlink()
        with self.assertRaises(s.SubstrateError):s.build(self.root,self.path,hooks=FakeOwners())
    def test_duplicate_claim_id_refuses(self):
        self.docs['claim']['claims'].append(self.docs['claim']['claims'][0]);self.write('claim')
        with self.assertRaises(s.SubstrateError):s.build(self.root,self.path,hooks=FakeOwners())
    def test_dangling_obligation_refuses(self):
        self.docs['claim']['claims'][0]['remaining_open_proposition_ids']=['missing'];self.write('claim')
        with self.assertRaises(s.SubstrateError):s.build(self.root,self.path,hooks=FakeOwners())
    def test_dangling_problem_registration_refuses(self):
        self.docs['problem']['problems'][0]['claim_registration']['registered_claim_ids'].append('missing');self.write('problem')
        with self.assertRaises(s.SubstrateError):s.build(self.root,self.path,hooks=FakeOwners())
    def test_tampered_generated_claim_is_rejected_independently(self):
        db=sqlite3.connect(self.path);db.execute("DELETE FROM node WHERE kind='claim' AND id='shared'");db.commit();db.close()
        with self.assertRaises(s.SubstrateError):s.View(self.root,self.path)
    def test_tampered_generated_statement_is_rejected(self):
        db=sqlite3.connect(self.path);db.execute("UPDATE node SET payload='{}' WHERE kind='claim' AND id='shared'");db.commit();db.close()
        with self.assertRaises(s.SubstrateError):s.View(self.root,self.path)
    def test_tampered_relation_cannot_enable_inference(self):
        db=sqlite3.connect(self.path)
        raw=db.execute("SELECT payload FROM node WHERE kind='relation'").fetchone()[0]
        row=json.loads(raw);row['inference_eligible']=True
        db.execute("UPDATE node SET payload=? WHERE kind='relation'",(json.dumps(row),));db.commit();db.close()
        with self.assertRaises(s.SubstrateError):s.View(self.root,self.path)
    def test_hidden_identifier_does_not_satisfy_summary(self):
        with s.View(self.root,self.path) as v:
            expected=v.register()
            actual=expected.replace('<a id="shared"></a>`shared`','<!-- shared -->')
            with self.assertRaises(s.SubstrateError):s.check_generated(expected,actual)
    def test_exact_generated_summary(self):
        with s.View(self.root,self.path) as v:s.check_generated(v.register(),v.register())
    def test_cursor_rejects_different_snapshot(self):
        with s.View(self.root,self.path) as v:
            with self.assertRaises(s.SubstrateError):v.frontier(249,cursor=s.canonical({'snapshot':'old','problem':'249','offset':0}))
    def test_bad_page_limit(self):
        with s.View(self.root,self.path) as v:
            for n in (0,65):
                with self.assertRaises(s.SubstrateError):v.frontier(249,limit=n)
    def test_unknown_problem_is_not_empty_success(self):
        with s.View(self.root,self.path) as v:
            with self.assertRaises(s.SubstrateError):v.frontier(999)
    def test_symlink_source_rejected(self):
        p=self.root/'lean/link.lean';p.parent.mkdir();p.symlink_to(self.root/s.OWNER['claim'])
        with self.assertRaises(s.SubstrateError):s.snapshot(self.root)
    def test_path_escape_rejected(self):
        with self.assertRaises(s.SubstrateError):s.safe_file(self.root,'../model.sqlite')
    def test_generated_register_does_not_self_invalidate(self):
        p=self.root/'docs/reference/CORPUS_REGISTER.md';p.parent.mkdir();p.write_text('derived output')
        with s.View(self.root,self.path) as v:self.assertEqual(v.meta['counts']['claim'],3)
    def test_unknown_current_graph_explicit(self):
        with s.View(self.root,self.path) as v:
            self.assertIn('not_admitted',v.frontier(249)['current_argument_graph'])


class EncodingTest(unittest.TestCase):
    def test_duplicate_json_key(self):
        with self.assertRaises(s.SubstrateError):s.decode(b'{"a":1,"a":2}')
    def test_nonfinite_json(self):
        for text in (b'NaN',b'Infinity',b'-Infinity'):
            with self.assertRaises(s.SubstrateError):s.decode(text)
    def test_context_text_does_not_gain_proof_authority(self):
        for c in ('False','Empty','Unit','forall x, False'):
            self.assertFalse(s.quarantined_relation({'context':c},{'state':'attested'})['inference_eligible'])


if __name__=='__main__':unittest.main()
