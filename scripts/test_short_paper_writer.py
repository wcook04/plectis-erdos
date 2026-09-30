#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Real-paper regression/mutation tests; no model, Lean or network execution."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import short_paper_writer as w
import build_short_paper_demo as demo

class WriterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.d, cls.e = demo.build(demo.FIXTURE_ROOT)
        cls.paper = (demo.FIXTURE_ROOT/demo.PAPER).read_text()
        cls.pairs, errors = w.source_tree(demo.FIXTURE_ROOT,demo.PAPER)
        if errors: raise RuntimeError(errors)

    def setUp(self):
        self.t = tempfile.TemporaryDirectory(); self.addCleanup(self.t.cleanup)
        self.root = Path(self.t.name)
        for path,text in self.pairs:
            target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(text)
        q=self.root/'docs/paper_lean_coverage.json';q.parent.mkdir(exist_ok=True)
        q.write_bytes((demo.FIXTURE_ROOT/'docs/paper_lean_coverage.json').read_bytes())
        self.d=copy.deepcopy(self.__class__.d);self.e=copy.deepcopy(self.__class__.e)

    def audit(self):return w.audit(self.root,demo.PID,demo.PAPER)
    def change(self,before,after):
        p=self.root/demo.PAPER;s=p.read_text();self.assertIn(before,s);p.write_text(s.replace(before,after,1))
    def has(self,rule):return [f for f in self.audit()['findings'] if f['rule']==rule]
    def render(self):return w.render(self.d,self.e,self.root)
    def refuse(self,field):
        with self.assertRaises(w.Refusal) as c:self.render()
        self.assertIn(field,c.exception.field)

    def test_SP01_literal_inputs_pass_missing_fail(self):
        self.assertFalse(self.has('SP01'))
        self.change(r'\begin{document}',r'\input{absent-fixture}\begin{document}')
        self.assertTrue(self.has('SP01'))
    def test_SP01_cycles_and_traversal_refused(self):
        self.change(r'\begin{document}',r'\input{erdos-269-three-prime-running-lcm}\begin{document}')
        self.assertTrue(any('cyclic' in f['message'] for f in self.has('SP01')))
        for bad in ['../secret','/etc/passwd','paper/../file','a\\b']:
            with self.subTest(path=bad),self.assertRaises(w.Refusal):w.safe_path(self.root,bad)
    def test_SP01_symlink_is_not_a_source(self):
        (self.root/'link').symlink_to(self.root/'paper',target_is_directory=True)
        with self.assertRaises(w.Refusal):w.safe_path(self.root,'link/269/a.tex')
    def test_SP02_unique_labels_pass_duplicate_fail(self):
        self.assertFalse(self.has('SP02'))
        self.change(r'\label{res:distinct-height-all}',r'\label{res:distinct-height-all}\label{res:distinct-height-all}')
        self.assertTrue(self.has('SP02'))
    def test_SP02_unlabelled_statement_refused(self):
        self.change(r'\label{res:distinct-height-all}','')
        self.assertTrue(self.has('SP02'))
    def test_SP03_literal_references_pass_missing_fail(self):
        self.assertFalse(self.has('SP03'))
        self.change(r'\ref{res:lcm}',r'\ref{missing-lcm}')
        self.assertTrue(self.has('SP03'))
    def test_SP04_citations_pass_missing_fail(self):
        self.assertFalse(self.has('SP04'))
        self.change(r'\cite{erdos1974letter}',r'\cite{missing-letter}')
        self.assertTrue(self.has('SP04'))
    def test_SP05_house_prose_pass_em_dash_fail(self):
        self.assertFalse(self.has('SP05'))
        self.change('The two\nsums differ','The two\nsums differ—')
        self.assertTrue(self.has('SP05'))
    def test_SP05_comments_and_math_not_house_prose(self):
        self.change(r'\begin{document}', '\\begin{document}\n% — not this but that\n$---$\n')
        self.assertFalse(self.has('SP05'))
    def test_SP06_contrast_is_review_not_hard_error(self):
        self.assertFalse(self.has('SP06'))
        self.change('The two\nsums differ','The two\nsums are not identical but different. The sums differ')
        fs=self.has('SP06');self.assertTrue(fs)
        self.assertTrue(all(f['severity']=='review' for f in fs))
    def test_SP07_body_digest_pass_hypothesis_mutation_fail(self):
        self.assertFalse(self.has('SP07'))
        self.change('For every finite set $P$ of primes with $|P|\\ge2$',
                    'For every finite set $P$ of primes with $|P|\\ge1$')
        self.assertTrue(self.has('SP07'))
    def test_SP08_actual_recorded_marks_pass_missing_fail(self):
        self.assertFalse([f for f in self.has('SP08') if f['severity']=='error'])
        # Remove the generated marks only, never edit proof evidence authority.
        found=False
        for path,text in self.pairs:
            if '\\DeclareResultEvidence{' in text:
                (self.root/path).write_text(text.replace('\\DeclareResultEvidence{','\\RemovedMark{'));found=True
        self.assertTrue(found)
        self.assertTrue([f for f in self.has('SP08') if f['severity']=='error'])
    def test_SP08_nested_dagger_is_parsed(self):
        # The nested macro is present in the real #269 evidence sidecar.
        text='\n'.join(t for _,t in self.pairs)
        rows=w.command_arguments(w.mask_comments(text),'DeclareResultEvidence',4)
        self.assertTrue(any(r'\textsuperscript{\dag}' in args[1] for _,args in rows))
        self.assertTrue(all(len(args)==4 for _,args in rows))
    def test_SP09_role_map_pass_missing_role_fail(self):
        tex,m=self.render();self.assertEqual(w.verify_draft(tex,m,self.d,self.e,self.root),[])
        m['blocks'].pop();self.assertEqual(w.verify_draft(tex,m,self.d,self.e,self.root)[0]['rule'],'SP09')
    def test_SP09_source_span_drift_refused(self):
        self.d['extensions']['short_paper_v1']['bindings']['mechanism'][0]=dict(self.d['extensions']['short_paper_v1']['bindings']['mechanism'][0],sha256='sha256:'+'0'*64)
        self.refuse('bindings.mechanism')
    def test_SP09_missing_mechanism_refused(self):
        del self.d['results'][0]['mechanism_sentence'];self.refuse('mechanism_sentence')
    def test_SP10_exact_replay_pass_external_edit_fail(self):
        tex,m=self.render();self.assertEqual(w.verify_draft(tex,m,self.d,self.e,self.root),[])
        tex=tex.replace('is irrational.','is rational.',1)
        self.assertIn('SP10',[x['rule'] for x in w.verify_draft(tex,m,self.d,self.e,self.root)])
    def test_SP11_status_pass_cross_source_mismatch_fail(self):
        self.render();self.e['rows'][0]['evidence_class']='lean';self.refuse('evidence_class')
    def test_SP11_consistent_fake_promotion_still_refused(self):
        self.d['results'][0]['evidence']['class']='lean';self.e['rows'][0]['evidence_class']='lean'
        self.e['rows'][0]['lean_declaration']='Invented.Proof'
        self.refuse('evidence_class')
    def test_SP11_changed_statement_even_with_new_hash_refused(self):
        self.d['results'][0]['statement']=self.d['results'][0]['statement'].replace(r'\ge2',r'\ge1')
        self.e['rows'][0]['statement_hash']=w.digest(self.d['results'][0]['statement'])
        self.refuse('lead.statement')
    def test_SP11_computed_cannot_be_a_proved_theorem(self):
        self.d['results'][0]['evidence']['class']='computed';self.e['rows'][0]['evidence_class']='computed'
        self.refuse('evidence_class')
    def test_SP11_ai_review_not_human(self):
        status='Ordinary proof, reviewed.'
        self.d['extensions']['short_paper_v1']['lead']['status_phrase']=status
        self.e['rows'][0]['status_phrase_required']=status
        self.refuse('status_phrase')
    def test_SP11_duplicate_rows_and_malformed_extensions(self):
        self.e['rows'].append(copy.deepcopy(self.e['rows'][0]));self.refuse('rows')
        self.e['rows'].pop();self.d['extensions']=[];self.refuse('extensions')
    def test_SP11_unsupported_tex_refused(self):
        self.d['extensions']['short_paper_v1']['motivation']=r'\input{/etc/passwd}'
        self.refuse('motivation')
    def test_SP12_balanced_pass_unclosed_fail(self):
        self.assertFalse(self.has('SP12'));self.change(r'\end{theorem}','')
        self.assertTrue(self.has('SP12'))
    def test_full_nine_paper_inventory_is_reproducible(self):
        one=w.run_portfolio(w.ROOT);two=w.run_portfolio(w.ROOT)
        self.assertEqual(one,two);self.assertEqual(one['summary']['papers'],9)
        selected={p['paper_id'] for p in w.portfolio(w.ROOT)}
        expected=sum(r['paper_id'] in selected for r in w.read_json(w.ROOT/'docs/paper_lean_coverage.json')['rows'])
        self.assertEqual(one['summary']['assertions'],expected)
        self.assertEqual(one['summary']['findings'].get('error',0),0)
    def test_target_relation_and_review_limits_survive_render(self):
        tex,m=self.render();self.assertEqual(m['target_relation'],'related_distinct_target')
        for fragment in ['no human review','has no Lean proof','different sum','full proof must be incorporated']:
            self.assertIn(fragment,tex)
    def test_all_rendered_result_claims_are_selected_from_dossier(self):
        tex,m=self.render();self.assertEqual(tex.count('\\begin{theorem}'),1)
        self.assertIn(self.d['results'][0]['statement'],tex)
        self.assertEqual(m['lead_result_id'],self.d['results'][0]['id'])
    def test_semantic_canary_is_not_misrepresented_as_verified(self):
        # A real limitation: matching bytes do not prove paraphrase entailment.
        # This mutation deliberately survives, so documentation cannot claim a semantic gate.
        self.d['extensions']['short_paper_v1']['problem_relation']='This theorem settles the repeated-value problem.'
        tex,m=self.render()
        self.assertIn('settles the repeated-value',tex)
        self.assertIn('no semantic',m['validation'])
    def test_missing_bibliography_key_refused(self):
        self.d['extensions']['short_paper_v1']['attribution_bibliography']['keys']=['invented']
        self.refuse('attribution_bibliography')
    def test_render_house_style_refusal(self):
        self.d['extensions']['short_paper_v1']['motivation']='One story—many results.'
        self.refuse('motivation')

    def test_count_renderer_recomputes_inventory(self):
        import build_short_paper_report as reports
        report=w.run_portfolio(w.ROOT);md,tex=reports.render(report)
        self.assertIn('PThreeAssertions',tex);self.assertIn('Unassessed',md)
        report['summary']['assertions']+=1
        with self.assertRaises(w.Refusal):reports.render(report)

    def test_cli_refusal_has_no_output_directory(self):
        self.d['results'][0].pop('hard_step')
        (self.root/'d.json').write_text(json.dumps(self.d));(self.root/'e.json').write_text(json.dumps(self.e))
        out=self.root/'out'
        run=subprocess.run([sys.executable,str(w.ROOT/'scripts/short_paper_writer.py'),'--root',str(self.root),
            'draft','--dossier',str(self.root/'d.json'),'--evidence',str(self.root/'e.json'),'--output-dir',str(out)],capture_output=True,text=True)
        self.assertEqual(run.returncode,2);self.assertFalse(out.exists())
        self.assertIn('hard_step',json.loads(run.stdout)['field'])

if __name__=='__main__':unittest.main(verbosity=2)
