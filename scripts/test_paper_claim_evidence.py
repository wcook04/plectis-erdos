#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Offline regressions for the native claim-evidence join and wording contract."""
from __future__ import annotations
import copy
import io
import contextlib
import json
from pathlib import Path
import tempfile
import unittest

import paper_claim_evidence as ce
import paper_evidence as pe
import check_lean_paper_propagation as lp

PIN = "1" * 40
CORPUS = "2" * 40
PID = "synthetic-note"
SOURCE = "paper/99/synthetic-note.tex"
LEAN = "lean/Syn/Results.lean"
CID = PID + "#res:first"
TEX = "\\newtheorem{theorem}{Theorem}\n\\begin{theorem}\\label{res:first}\nAdding zero changes nothing.\n\\end{theorem}\n"
LEAN_TEXT = "namespace Syn\ntheorem first (n : Nat) : n + 0 = n := rfl\nend Syn\n"


class Fixture:
    def __init__(self):
        statement = lp.inventory([(SOURCE, TEX)], [])[0]
        decl = pe.lean_declaration(pe.LeanFile(LEAN_TEXT), LEAN, "Syn.first", allow_suffix=False)
        self.data = {}
        self.write(SOURCE, TEX.encode())
        self.write(LEAN, LEAN_TEXT.encode())
        row = {"id": CID, "paper_id": PID, "problem": 99, "side": "short",
               "label": "res:first", "environment": "theorem", "kind": "theorem",
               "source": SOURCE + ":2", "statement_sha256": statement["statement_sha256"],
               "lean": {"status": "exact", "declarations": [{"name": "Syn.first", "file": LEAN}]},
               "comparator": {"status": "pending", "queued_at": "2026-09-29"},
               "palomar": {"status": "pending"}}
        ledger = {"schema": lp.LEDGER_SCHEMA, "lean_pin": PIN, "rows": [row],
                  "papers": [{"paper_id": PID, "problem": 99, "side": "short", "sources": [SOURCE], "asserting_environments": 1}]}
        ledger["summary"] = lp.ledger_summary(ledger["rows"])
        ledger["content_digest"] = lp.content_digest(ledger)
        self.set(pe.LEDGER, ledger)
        self.set(pe.EVIDENCE_MAP, {"schema": pe.SCHEMA, "lean_pin": PIN, "corpus_commit": CORPUS,
            "papers": [{"paper_id": PID, "results": [{**row, "lean": {"status": "exact", "declarations": [
                {"name": "Syn.first", "path": LEAN, "kind": "theorem", "statement_sha256": ce.digest(decl.normalised.encode()).removeprefix('sha256:')} ]}}]}]})
        self.set(pe.ASSOCIATIONS, {"corpus_commit": CORPUS, "run_id": "1", "declarations": {}})
        self.set(pe.CONFIG, {"corpus_commit": CORPUS, "replay": {"run_id": "1", "receipts": "evidence/comparator/replay-1"}})
        self.set(ce.INDEX, {"formal_source": {"ref": PIN}, "nodes": [{"handle": "Syn.first", "module": LEAN, "line": 2}], "unresolved_atlas_declarations": []})
        self.set(ce.CLAIMS, {"release": {"formal_source": {"ref": PIN}}, ce.POLICY_KEY: {"schema": ce.POLICY_SCHEMA, "nonformal_evidence": ce.ANN, "status_assertions": {}}})
        self.set(ce.ANN, {"schema": "plectis-nonformal-claim-evidence/1", "rows": {}})

    def write(self, path, data): self.data[path] = data
    def read(self, path):
        if path not in self.data: raise FileNotFoundError(path)
        return self.data[path]
    def get(self, path): return json.loads(self.data[path])
    def set(self, path, value): self.data[path] = ce.canonical(value)
    def modify(self, path, fn):
        value = self.get(path); fn(value); self.set(path, value)
    def ledger_edit(self, fn):
        value = self.get(pe.LEDGER); fn(value)
        value['summary'] = lp.ledger_summary(value['rows']);value['content_digest'] = lp.content_digest(value)
        self.set(pe.LEDGER, value)
    def report(self): return ce.project(self.read, source_commit=PIN)
    def codes(self): return {g['code'] for g in self.report()['gaps']}
    def nonformal(self, cls='computed'):
        self.ledger_edit(lambda l:l['rows'][0].update(lean={'status':'none','counted':True,'declarations':[],'reason':'ordinary proof has not been formalised'},comparator={'status':'not_applicable'},palomar={'status':'not_applicable'}))
        self.modify(pe.EVIDENCE_MAP,lambda e:e['papers'][0]['results'][0].update(lean={'status':'none','declarations':[]}))
        self.write('evidence/artifact.txt',b'Exact finite computation.\n')
        loc={'path':'evidence/artifact.txt','start_line':1,'end_line':1,'sha256':ce.digest(self.read('evidence/artifact.txt'))}
        ann={'statement_hash':self.get(pe.LEDGER)['rows'][0]['statement_sha256'],'evidence_class':cls,
             'computation':loc,'domain':'n = 0,...,9','command':'python3 finite.py',
             'proof':loc,'review':loc,'reviewer_kind':'ai','reviewer_id':'fixture-only-reviewer',
             'review_outcome':'accepted','review_scope':'entire fixture statement',
             'source':loc,'source_version':'fixture-v1','theorem_locator':'Theorem 1'}
        self.set(ce.ANN,{'schema':'plectis-nonformal-claim-evidence/1','rows':{CID:ann}})
    def compared(self):
        self.ledger_edit(lambda l:l['rows'][0].update(comparator={'status':'compared','entries':['PalomarCorpus/E1'],'run_ids':['1'],'corpus_commits':[CORPUS]}))
        assoc={'entry':'E1','challenge':'Syn.first','solution':'Solutions.Syn.first','solution_path':'Solutions/E1.lean'}
        self.modify(pe.ASSOCIATIONS,lambda a:a['declarations'].update({'Syn.first':assoc}))
        receipt={'schema':pe.RECEIPT_SCHEMA,'entry':'E1','exit':0,'process_exit':0,'render_audit_exit':0,
                 'github':{'sha':CORPUS,'run_id':'1','repository':'wcook04/plectis-erdos-lean'},
                 'kernel_acceptance':{'lean_default':True,'nanoda':True},'verification':{'outcome':'passed'},
                 'permitted_axioms':pe.PERMITTED_AXIOMS,'axiom_audit':{'permitted_axioms':pe.PERMITTED_AXIOMS},
                 'theorem_names':['Syn.first'],'theorem_count':1,
                 'entry_digests':{k:'0'*64 for k in ('Challenge.lean','comparator.json','formalization.yaml')},
                 'solution':{'files':{'Solutions/E1.lean':'0'*64}}}
        path='evidence/comparator/replay-1/receipt-E1.json';self.set(path,receipt)
        self.modify(pe.EVIDENCE_MAP,lambda e:e['papers'][0]['results'][0].update(comparator={
            'status':'compared','commit':CORPUS,'run_id':'1','checks':[
                {'declaration':'Syn.first','entry':'E1','receipt':path,'challenge':{'declaration':'Syn.first'},'solution':{'path':'Solutions/E1.lean','declaration':'Syn.first'}}]}))


class ClaimEvidenceTests(unittest.TestCase):
    def setUp(self):self.f=Fixture()
    def test_sound_fixture_is_bound(self):
        r=self.f.report();self.assertEqual(r['gaps'],[]);self.assertEqual(r['summary']['bound'],1)
        self.assertEqual(r['rows'][0]['evidence_class'],'lean')
        self.assertTrue(set(ce.REQUIRED)<=set(r['rows'][0]))
    def test_deterministic(self):self.assertEqual(ce.canonical(self.f.report()),ce.canonical(self.f.report()))
    def test_missing_index_is_not_no_proof(self):
        self.f.modify(ce.INDEX,lambda i:i.update(nodes=[]))
        r=self.f.report();self.assertIn('dependency_index',self.f.codes())
        self.assertEqual(r['rows'][0]['recorded_evidence_class'],'lean')
        self.assertEqual(r['rows'][0]['evidence_class'],'evidence_gap')
    def test_stale_paper(self):
        self.f.write(SOURCE,TEX.replace('Adding zero','Multiplying by two').encode())
        self.assertIn('statement_missing',self.f.codes())
    def test_unrowed_theorem(self):
        self.f.write(SOURCE,(TEX+'\\begin{theorem}\\label{extra}Extra.\\end{theorem}\n').encode())
        self.assertIn('paper_inventory',self.f.codes())
    def test_deleted_declaration(self):
        self.f.write(LEAN,b'namespace Syn\nend Syn\n')
        self.assertIn('declaration_missing',self.f.codes())
    def test_changed_statement(self):
        self.f.write(LEAN,LEAN_TEXT.replace('n + 0 = n','True').encode())
        self.assertIn('formal_statement_hash',self.f.codes())
    def test_wrong_index_path(self):
        self.f.modify(ce.INDEX,lambda i:i['nodes'][0].update(module='lean/Wrong.lean'))
        self.assertIn('index_path',self.f.codes())
    def test_wrong_index_line(self):
        self.f.modify(ce.INDEX,lambda i:i['nodes'][0].update(line=20))
        self.assertIn('index_line',self.f.codes())
    def test_no_promotion_from_ordinary_review_prose(self):
        self.f.nonformal('ordinary_reviewed');self.f.set(ce.ANN,{'schema':'plectis-nonformal-claim-evidence/1','rows':{}})
        self.assertIn('nonformal_missing',self.f.codes())
    def test_reviewed_ordinary_is_distinct(self):
        self.f.nonformal('ordinary_reviewed');r=self.f.report();self.assertEqual(r['gaps'],[])
        self.assertEqual(r['rows'][0]['evidence_class'],'ordinary_reviewed')
        self.assertIn('ai review',r['rows'][0]['status_phrase_required'])
    def test_changed_review_span(self):
        self.f.nonformal('ordinary_reviewed');self.f.write('evidence/artifact.txt',b'Changed review.\n')
        self.assertIn('nonformal_binding',self.f.codes())
    def test_review_identity_missing(self):
        self.f.nonformal('ordinary_reviewed');self.f.modify(ce.ANN,lambda a:a['rows'][CID].pop('reviewer_id'))
        self.assertIn('nonformal_binding',self.f.codes())
    def test_cited_never_becomes_local_proof(self):
        self.f.nonformal('cited');r=self.f.report();self.assertEqual(r['gaps'],[])
        self.assertNotIn('lean',ce.allowed_statuses(r['rows'][0]))
    def test_computed_proved_request_is_rejected(self):
        self.f.nonformal();self.f.modify(ce.CLAIMS,lambda c:c[ce.POLICY_KEY]['status_assertions'].update({CID:['proved']}))
        self.assertIn('overstatement',self.f.codes())
    def test_computed_lean_status_in_real_tex_is_rejected(self):
        self.f.nonformal();self.f.write(SOURCE,(TEX+'\\claimstatus{res:first}{lean}\n').encode())
        self.assertIn('overstatement',self.f.codes())
    def test_negative_statement_word_is_not_keyword_scanned(self):
        self.f.nonformal();self.f.write(SOURCE,(TEX+'This does not prove a general theorem.\n').encode())
        self.assertNotIn('overstatement',self.f.codes())
    def test_claim_of_human_review_needs_own_dimension(self):
        self.f.nonformal('ordinary_reviewed');self.f.modify(ce.CLAIMS,lambda c:c[ce.POLICY_KEY]['status_assertions'].update({CID:['human_reviewed']}))
        self.assertIn('overstatement',self.f.codes())
    def test_recorded_comparator(self):
        self.f.compared();r=self.f.report();self.assertEqual(r['gaps'],[])
        self.assertEqual(r['rows'][0]['evidence_class'],'comparator')
        self.assertEqual(r['rows'][0]['validation']['comparator_execution'],'UNRUN')
    def test_receipt_numeric_kernel_flag_is_rejected(self):
        self.f.compared();self.f.modify('evidence/comparator/replay-1/receipt-E1.json',lambda r:r['kernel_acceptance'].update(lean_default=1))
        self.assertIn('receipt_binding',self.f.codes())
    def test_receipt_boolean_theorem_count_is_rejected(self):
        self.f.compared();self.f.modify('evidence/comparator/replay-1/receipt-E1.json',lambda r:r.update(theorem_count=True))
        self.assertIn('receipt_binding',self.f.codes())
    def test_computed_assumptions_never_grant_formal_status(self):
        row={'id':CID,'evidence_class':'computed','conditional':True,'binding_status':'bound'}
        self.assertEqual(ce.allowed_statuses(row),{'computed'})
        self.assertIn('Computed evidence',ce.status_phrase(row))
        self.assertTrue(ce.status_errors(row,'conditional_lean'))
    def test_ordinary_assumptions_never_grant_formal_status(self):
        row={'id':CID,'evidence_class':'ordinary_reviewed','conditional':True,'binding_status':'bound','reviewer_kind':'ai'}
        self.assertEqual(ce.allowed_statuses(row),{'ordinary_reviewed'})
        self.assertIn('recorded ai review',ce.status_phrase(row))
    def test_native_alternate_solution_path_roles_are_preserved(self):
        self.f.compared()
        alternate='Solutions/E1/Statement.lean'
        self.f.modify('evidence/comparator/replay-1/receipt-E1.json',lambda r:r['solution']['files'].update({alternate:'f'*64}))
        self.f.modify(pe.EVIDENCE_MAP,lambda d:d['papers'][0]['results'][0]['comparator']['checks'][0]['solution'].update(path=alternate))
        r=self.f.report();self.assertEqual(r['gaps'],[])
        self.assertTrue(r['rows'][0]['binding_extension']['declarations'][0]['comparator']['different_path_roles'])
    def test_resolved_solution_must_name_selected_proposition(self):
        self.f.compared()
        self.f.modify(pe.EVIDENCE_MAP,lambda d:d['papers'][0]['results'][0]['comparator']['checks'][0]['solution'].update(declaration='Other'))
        self.assertIn('receipt_binding',self.f.codes())
    def test_resolved_declaring_path_must_be_in_receipt(self):
        self.f.compared()
        self.f.modify(pe.EVIDENCE_MAP,lambda d:d['papers'][0]['results'][0]['comparator']['checks'][0]['solution'].update(path='Solutions/Evil.lean'))
        self.assertIn('receipt_binding',self.f.codes())
    def test_receipt_missing(self):
        self.f.compared();del self.f.data['evidence/comparator/replay-1/receipt-E1.json']
        self.assertIn('receipt_missing',self.f.codes())
    def test_receipt_wrong_run(self):
        self.f.compared();self.f.modify('evidence/comparator/replay-1/receipt-E1.json',lambda r:r['github'].update(run_id='2'))
        self.assertIn('receipt_binding',self.f.codes())
    def test_receipt_false_is_not_exit_zero(self):
        self.f.compared();self.f.modify('evidence/comparator/replay-1/receipt-E1.json',lambda r:r.update(exit=False))
        self.assertIn('receipt_binding',self.f.codes())
    def test_receipt_missing_selected_theorem(self):
        self.f.compared();self.f.modify('evidence/comparator/replay-1/receipt-E1.json',lambda r:r.update(theorem_names=['Other'],theorem_count=1))
        self.assertIn('receipt_binding',self.f.codes())
    def test_missing_association(self):
        self.f.compared();self.f.modify(pe.ASSOCIATIONS,lambda a:a.update(declarations={}))
        self.assertIn('association_missing',self.f.codes())
    def test_invalid_axiom_budget(self):
        self.f.compared();self.f.modify('evidence/comparator/replay-1/receipt-E1.json',lambda r:r.update(permitted_axioms=['sorryAx']))
        self.assertIn('receipt_binding',self.f.codes())
    def test_missing_digest(self):
        self.f.compared();self.f.modify('evidence/comparator/replay-1/receipt-E1.json',lambda r:r.update(entry_digests={}))
        self.assertIn('receipt_binding',self.f.codes())
    def test_duplicate_claim_rejected(self):
        self.f.ledger_edit(lambda l:l['rows'].append(copy.deepcopy(l['rows'][0])))
        with self.assertRaisesRegex(ValueError,'duplicate'):self.f.report()
    def test_duplicate_dependency_handle_rejected(self):
        self.f.modify(ce.INDEX,lambda i:i['nodes'].append(copy.deepcopy(i['nodes'][0])))
        with self.assertRaisesRegex(ValueError,'duplicate'):self.f.report()
    def test_unresolved_local_names_can_repeat(self):
        self.f.modify(ce.INDEX,lambda i:i.update(unresolved_atlas_declarations=[{'handle':'R','module':LEAN},{'handle':'R','module':'lean/B.lean'}]))
        self.assertEqual(self.f.report()['gaps'],[])
    def test_missing_paper_pair(self):
        self.f.modify(ce.CLAIMS,lambda c:c[ce.POLICY_KEY].update(require_sixteen_papers=True))
        self.assertIn('portfolio',self.f.codes())
    def test_wrong_pin(self):
        self.f.modify(ce.INDEX,lambda i:i.update(formal_source={'ref':'3'*40}))
        self.assertIn('formal_pin',self.f.codes())
    def test_conditional_is_never_unconditional(self):
        row={'id':CID,'evidence_class':'lean','conditional':True,'binding_status':'bound'}
        self.assertEqual(ce.allowed_statuses(row),{'conditional_lean'})
        self.assertTrue(ce.status_errors(row,'unconditional'))
    def test_conditional_gap_cannot_authorize_lean(self):
        row={'id':CID,'evidence_class':'evidence_gap','conditional':True,'binding_status':'gap'}
        self.assertEqual(ce.allowed_statuses(row),{'evidence_gap'})
    def test_unsafe_paths(self):
        for p in ('../escape','/abs','a/../../b','.git/config','a\\b','a/./b'):
            with self.subTest(p=p),self.assertRaises(ValueError):ce.safe_relative(p)
    def test_symlink_reader(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'file').symlink_to('/etc/passwd')
            with self.assertRaises(ValueError):ce.root_reader(root)('file')
    def test_publication_checks_same_bytes_and_projection(self):
        r=self.f.report();self.f.set(ce.OUTPUT,r)
        self.assertEqual(ce.publication_errors(self.f.read,self.f.get(ce.CLAIMS)),[])
        self.f.modify(ce.OUTPUT,lambda r:r['rows'][0].update(status_phrase_required='Proved.'))
        self.assertTrue(any('stale rows' in e for e in ce.publication_errors(self.f.read,self.f.get(ce.CLAIMS))))
    def writer_manifest(self):
        r=self.f.report();phrase=r['rows'][0]['status_phrase_required']
        start=len(self.f.read(SOURCE).decode().splitlines())+1
        self.f.write(SOURCE,self.f.read(SOURCE)+(phrase+'\n').encode())
        r=self.f.report()
        return r,{'schema':'claim_evidence_writer/1','require_complete':True,'rows':[{
            'claim_id':CID,'statement_hash':r['rows'][0]['statement_hash'],'phrase':phrase,
            'rendered_span':{'path':SOURCE,'start_line':start,'end_line':start,'sha256':ce.digest((phrase+'\n').encode())}}]}
    def test_writer_matching_generated_phrase(self):
        r,m=self.writer_manifest();self.assertEqual(ce.validate_writer_manifest(m,r,self.f.read),[])
    def test_writer_modified_phrase_rejected(self):
        self.f.nonformal();r,m=self.writer_manifest();m['rows'][0]['phrase']='Proved by Lean.'
        self.assertTrue(ce.validate_writer_manifest(m,r,self.f.read))
    def test_writer_omission_rejected(self):
        r,m=self.writer_manifest();m['rows']=[]
        self.assertTrue(ce.validate_writer_manifest(m,r,self.f.read))
    def test_writer_sidecar_decoy_rejected(self):
        r,m=self.writer_manifest();phrase=m['rows'][0]['phrase']
        self.f.write('paper/status.txt',(phrase+'\n').encode())
        m['rows'][0]['rendered_span'].update(path='paper/status.txt',start_line=1,end_line=1)
        self.assertTrue(ce.validate_writer_manifest(m,r,self.f.read))
    def test_writer_distant_status_rejected(self):
        r,m=self.writer_manifest();phrase=m['rows'][0]['phrase']
        self.f.write(SOURCE,self.f.read(SOURCE)+b'\n'*30+(phrase+'\n').encode())
        line=len(self.f.read(SOURCE).decode().splitlines())
        m['rows'][0]['rendered_span'].update(start_line=line,end_line=line)
        self.assertTrue(ce.validate_writer_manifest(m,r,self.f.read))
    def test_writer_stale_hash_rejected(self):
        r,m=self.writer_manifest();m['rows'][0]['statement_hash']='sha256:'+'0'*64
        self.assertTrue(ce.validate_writer_manifest(m,r,self.f.read))


if __name__ == '__main__':
    unittest.main(verbosity=2)
