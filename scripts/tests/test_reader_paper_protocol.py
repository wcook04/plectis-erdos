#!/usr/bin/env python3
"""Offline manual-session protocol tests; synthetic observations are labelled."""

import _test_bootstrap  # noqa: F401
import copy
import json
from pathlib import Path
import tempfile
import unittest
import zipfile
import reader_paper_protocol as p
import reader_study as native

ROOT=Path(__file__).resolve().parents[2]
RUBRIC=ROOT/'docs/research-commons/benchmarks/paper_eval/rubric.json'

class PaperProtocolTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.base=Path(self.temp.name);self.src=self.base/'src';self.src.mkdir()
        for name,text in [('paper.txt','Realistic fixture statement.\nEvidence is a fixture.\n'),('raw.txt','Raw fixture facts.'),('dossier.txt','Structured fixture facts.'),('reference.txt','Reviewed only inside a synthetic test.\n')]:
            (self.src/name).write_text(text)
        self.r=p.read(RUBRIC)
        self.review={'status':'reviewed','reviewer':'fixture-controller','evidence':'synthetic fixture only'}
        self.spec={'schema':'paper-study/1','execution':'manual_type_b','no_api':True,'mode':'development',
            'source_commit':'a'*40,'seed':19,'synthetic':True,'look_number':1,
            'minimum_useful_difference':.125,'rubric_sha256':p.digest(self.r),
            'independence_review':self.review,'budget':{'output_words':2000},
            'tasks':[{'task_id':'paper68','family_id':'factorial','problem':68,'profile':'short',
                      'prompt':'Improve this fixture using only supplied facts.',
                      'changed_input':'context.txt','semantic_single_change_review':self.review,
                      'reference':self.ref('reference.txt'),
                      'material':{'P':{'paper.txt':self.ref('paper.txt'),'context.txt':self.ref('raw.txt')},
                                  'F':{'paper.txt':self.ref('paper.txt'),'context.txt':self.ref('dossier.txt')}}}]}
        self.study=self.base/'study'
    def ref(self,name):return {'path':name,'sha256':native.sha((self.src/name).read_bytes())}
    def prepare(self):return p.prepare(self.spec,self.r,self.src,self.study)
    def capture(self,control):
        records=[]
        for i,j in enumerate(control['jobs']):
            (self.src/f'trace{i}.txt').write_text('SYNTHETIC controller fixture, no real session')
            records.append({'job_id':j['job_id'],'status':'completed','job_spec_sha256':j['job_spec_sha256'],
                'session_id':f'synthetic-producer-{i}','model_snapshot':'synthetic-model',
                'trace_path':f'trace{i}.txt','answer_path':'paper.txt',
                'effort_review':self.review,'isolation_review':self.review})
        return p.capture(self.study,{'schema':'paper-capture/1','control_sha256':p.digest(control),
                         'synthetic':True,'records':records},self.src,self.base/'capture.json')
    def grades(self,control,captured):
        out=self.base/'graders';mapping=p.graders(self.study,captured,out);grades=[]
        for i in (1,2):
            for g in p.read(out/f'grader_{i}'/'grade_template.json'):
                g.update({'grader_session_id':f'synthetic-grader-{i}','producer_blind':True,'blinding_compromised':False})
                g['scores']={x:2 for x in p.ITEMS};g['rationale']={x:'Fixture behavior only.' for x in p.ITEMS}
                g['evidence']={x:[{'source':'artifact','start_line':1,'end_line':1,'quote':'Realistic fixture statement.'}] for x in p.ITEMS}
                grades.append(g)
        return mapping,grades
    def test_native_prepare_and_exact_job_verification(self):
        c=self.prepare();self.assertEqual(len(c['jobs']),2)
        p.bound_study(self.study)
        for j in c['jobs']:self.assertTrue((self.study/(j['job_id']+'.zip')).exists())
    def test_native_cli_dispatch(self):
        import contextlib,io
        spec=self.base/'spec.json';p.save(spec,self.spec)
        with contextlib.redirect_stdout(io.StringIO()):
            native.main(['paper-prepare','--spec',str(spec),'--rubric',str(RUBRIC),'--source-root',str(self.src),'--out',str(self.study)])
        p.bound_study(self.study)
    def test_single_changed_input_required(self):
        self.spec['tasks'][0]['material']['F']['paper.txt']=self.ref('dossier.txt')
        with self.assertRaisesRegex(ValueError,'exactly declared'):self.prepare()
    def test_unchanged_pair_refused(self):
        self.spec['tasks'][0]['material']['F']=copy.deepcopy(self.spec['tasks'][0]['material']['P'])
        with self.assertRaisesRegex(ValueError,'exactly declared'):self.prepare()
    def test_different_slots_refused(self):
        self.spec['tasks'][0]['material']['F']['extra.txt']=self.ref('dossier.txt')
        with self.assertRaisesRegex(ValueError,'slots'):self.prepare()
    def test_different_prompt_by_arm_refused(self):
        self.spec['tasks'][0]['prompt_F']='different'
        with self.assertRaisesRegex(ValueError,'unrecognized'):self.prepare()
    def test_changed_source_refused(self):
        (self.src/'paper.txt').write_text('changed')
        with self.assertRaisesRegex(ValueError,'byte mismatch'):self.prepare()
    def test_synthetic_flag_required(self):
        del self.spec['synthetic']
        with self.assertRaisesRegex(ValueError,'synthetic'):self.prepare()
    def test_no_api_required(self):
        self.spec['no_api']=False
        with self.assertRaisesRegex(ValueError,'manual'):self.prepare()
    def test_confirmatory_refused(self):
        self.spec['mode']='confirmatory'
        with self.assertRaisesRegex(ValueError,'development'):self.prepare()
    def test_duplicate_family_refused(self):
        t=copy.deepcopy(self.spec['tasks'][0]);t['task_id']='other';self.spec['tasks'].append(t)
        with self.assertRaisesRegex(ValueError,'lineage'):self.prepare()
    def test_path_traversal_refused(self):
        self.spec['tasks'][0]['material']['P']['context.txt']['path']='../secret'
        with self.assertRaises(ValueError):self.prepare()
    def test_symlink_refused(self):
        (self.src/'link.txt').symlink_to(self.src/'raw.txt')
        self.spec['tasks'][0]['material']['P']['context.txt']['path']='link.txt'
        with self.assertRaisesRegex(ValueError,'symlink'):self.prepare()
    def test_rubric_drift_refused(self):
        self.prepare();r=p.read(self.study/'rubric.json');r['version']='changed'
        (self.study/'rubric.json').write_text(json.dumps(r))
        with self.assertRaisesRegex(ValueError,'rubric drift'):p.bound_study(self.study)
    def test_reference_drift_refused(self):
        self.prepare();next((self.study/'private_references').rglob('reference.txt')).write_text('changed')
        with self.assertRaisesRegex(ValueError,'reference drift'):p.bound_study(self.study)
    def test_no_return_stays_pending(self):
        c=self.prepare();cap=p.capture(self.study,{'schema':'paper-capture/1','control_sha256':p.digest(c),
            'synthetic':True,'records':[]},self.src,self.base/'cap.json')
        self.assertTrue(all(r['status']=='not_run' for r in cap['records']))
    def test_fixture_end_to_end_not_a_measured_gain(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap)
        result=p.analyze(self.study,cap,m,g)
        self.assertEqual(result['result_class'],'no resolvable difference')
        self.assertEqual([result['interval'][x] for x in ('lower','upper')],[-1,1])
        self.assertFalse(result['promote_policy']);self.assertTrue(result['synthetic'])
    def test_missing_grade_not_zero(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap)
        result=p.analyze(self.study,cap,m,g[:-1]);self.assertEqual(result['status'],'incomplete')
        self.assertIsNone(result['paired_difference'])
    def test_same_grader_session_refused(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap)
        for x in g:x['grader_session_id']='same'
        with self.assertRaisesRegex(ValueError,'one session'):p.analyze(self.study,cap,m,g)
    def test_producer_cannot_self_grade(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap)
        jid=next(x['job_id'] for x in m['mapping'] if x['grader_pass']==g[0]['grader_pass'] and x['blind_id']==g[0]['blind_id'])
        g[0]['grader_session_id']=next(x['session_id'] for x in cap['records'] if x['job_id']==jid)
        with self.assertRaisesRegex(ValueError,'itself'):p.analyze(self.study,cap,m,g)
    def test_grade_hash_mismatch(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap);g[0]['artifact_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'artifact mismatch'):p.analyze(self.study,cap,m,g)
    def test_fabricated_quote_refused(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap);g[0]['evidence']['mechanism'][0]['quote']='not present'
        with self.assertRaisesRegex(ValueError,'match bytes'):p.analyze(self.study,cap,m,g)
    def test_unblinded_grade_refused(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap);g[0]['producer_blind']=False
        with self.assertRaisesRegex(ValueError,'unblinded'):p.analyze(self.study,cap,m,g)
    def test_disagreement_is_reported_and_needs_adjudication(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap);g[0]['scores']['mechanism']=1
        result=p.analyze(self.study,cap,m,g);self.assertEqual(result['status'],'incomplete')
        self.assertIn('disagreement_requires_adjudication',[x['reason'] for x in result['pending']])
    def test_rubric_tolerance_amendment_cannot_be_silent(self):
        self.r['agreement_tolerance']['minimum_exact']=.5
        with self.assertRaisesRegex(ValueError,'tolerance amendment'):p.validate_rubric(self.r)
    def test_adjudication_requires_third_session_and_bound_quotes(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap)
        target=m['mapping'][0]['job_id'];related=[]
        for x in g:
            row=next(z for z in m['mapping'] if z['grader_pass']==x['grader_pass'] and z['blind_id']==x['blind_id'])
            if row['job_id']==target:related.append(x)
        related.sort(key=lambda x:x['grader_pass']);related[0]['scores']['navigation']=1
        a={'job_id':target,'grade_hashes':[p.digest(x) for x in related],
           'reviewer_session_id':related[0]['grader_session_id'],'rationale':'Synthetic dispute only.',
           'scores':related[1]['scores'],'evidence':related[1]['evidence']}
        with self.assertRaisesRegex(ValueError,'third-session'):p.analyze(self.study,cap,m,g,[a])
        a['reviewer_session_id']='synthetic-third-reviewer'
        self.assertEqual(p.analyze(self.study,cap,m,g,[a])['status'],'complete')
        a['evidence']={}
        with self.assertRaisesRegex(ValueError,'item evidence'):p.analyze(self.study,cap,m,g,[a])
    def test_unsafe_output_vetoes_style_gain(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap)
        for x in g:x['severe_errors']=['Planted unsupported claim.']
        self.assertTrue(p.analyze(self.study,cap,m,g)['safety_veto'])
    def test_unknown_model_invalidates_inference(self):
        c=self.prepare();cap=self.capture(c)
        for r in cap['records']:r['model_snapshot']=None
        m,g=self.grades(c,cap);result=p.analyze(self.study,cap,m,g)
        self.assertEqual(result['result_class'],'invalid comparison')
    def test_walkthrough_is_not_worker_execution(self):
        c=self.prepare();cap=self.capture(c);cap['observation_kind']='artifact_walkthrough'
        m,g=self.grades(c,cap);result=p.analyze(self.study,cap,m,g)
        self.assertEqual(result['result_class'],'invalid comparison')
        self.assertIn('artifact_walkthrough_is_not_worker_execution',result['invalid_reasons'])
    def test_profile_drift_refused(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap);g[0]['profile']='long'
        with self.assertRaisesRegex(ValueError,'profile mismatch'):p.analyze(self.study,cap,m,g)
    def test_capture_answer_drift_refused(self):
        c=self.prepare();cap=self.capture(c);cap['records'][0]['answer']='mutated'
        with self.assertRaisesRegex(ValueError,'artifact drift'):p.graders(self.study,cap,self.base/'g')
    def test_duplicate_grader_map_refused(self):
        c=self.prepare();cap=self.capture(c);m,g=self.grades(c,cap);m['mapping'].append(m['mapping'][0])
        with self.assertRaisesRegex(ValueError,'duplicate grader map'):p.analyze(self.study,cap,m,g)
    def test_grader_packets_do_not_include_control_or_trace(self):
        c=self.prepare();cap=self.capture(c);self.grades(c,cap)
        for i in (1,2):
            with zipfile.ZipFile(self.base/'graders'/f'grader_{i}.zip') as z:
                blob=b'\n'.join(z.read(n) for n in z.namelist())
                self.assertNotIn(b'synthetic-producer',blob)
                self.assertNotIn(b'private_control',blob)
                self.assertNotIn(b'SYNTHETIC controller fixture',blob)
    def test_ordinal_agreement(self):
        a=p.agreement([0,1,2,2],[0,2,2,2]);self.assertEqual(a['exact_agreement'],.75)
        self.assertEqual(a['mean_absolute_difference'],.25)
    def test_degenerate_kappa_is_undefined(self):
        a=p.agreement([2,2],[2,2]);self.assertIsNone(a['cohen_kappa'])
    def test_interval_zero_variance_still_has_width(self):
        a=p.interval([0.,0.,0.,0.],.05);self.assertLess(a['lower'],0);self.assertGreater(a['upper'],0)
    def test_large_fixture_interval_can_resolve(self):
        a=p.interval([.5]*1000,.025);self.assertGreater(a['lower'],.125)
    def test_interval_rejects_nan_and_bools(self):
        for v in ([float('nan')],[True],[1.01]):
            with self.subTest(v=v),self.assertRaises(ValueError):p.interval(v,.05)
    def test_ledger_append_duplicate_and_tamper(self):
        row={'schema':'paper-score/1','scoring_kind':'synthetic','artifact_id':'a','artifact_sha256':'a'*64,
             'rubric_sha256':'b'*64,'round_id':'r1','grader_session_id':'g1',
             'scores':dict.fromkeys(p.ITEMS,1),'evidence':dict.fromkeys(p.ITEMS,{'locator':'fixture only'})}
        path=self.base/'ledger.jsonl';p.append_ledger(path,row)
        with self.assertRaisesRegex(ValueError,'duplicate'):p.append_ledger(path,row)
        path.write_text(path.read_text().replace('"artifact_id": "a"','"artifact_id": "b"'))
        row['grader_session_id']='g2'
        with self.assertRaisesRegex(ValueError,'chain broken'):p.append_ledger(path,row)
    def test_exact_qa_missing_wrong_and_abstaining(self):
        key={'schema':'paper-qa-key/1','questions':[{'id':'q1','accepted':['no']},{'id':'q2','accepted':[300000]},{'id':'q3','accepted':['computed']}]}
        answers={'schema':'paper-qa-answer/1','key_sha256':p.digest(key),'answers':{'q1':'no','q2':'abstain'}}
        result=p.grade_qa(key,answers);self.assertEqual(result['correct'],1)
        self.assertTrue(result['items'][1]['abstention']);self.assertTrue(result['items'][2]['missing'])
    def test_qa_bool_not_an_integer_answer(self):
        key={'schema':'paper-qa-key/1','questions':[{'id':'q','accepted':[1]}]}
        self.assertEqual(p.grade_qa(key,{'schema':'paper-qa-answer/1','key_sha256':p.digest(key),'answers':{'q':True}})['correct'],0)
    def test_native_lexical_check_is_diagnostic_only(self):
        a=p.lexical_preflight('A conditional result remains open.',[['conditional'],['proved']])
        self.assertEqual(a['groups_present'],[True,False]);self.assertIn('not reader',a['boundary'])
    def test_real_corpus_material_and_native_owner(self):
        src=ROOT/'paper/68/erdos-68-factorial-denominator-irrationality.tex'
        self.assertTrue(native.safe_file(ROOT,src.relative_to(ROOT).as_posix()).is_file())
        self.assertIn('299999',src.read_text())

if __name__=='__main__':unittest.main()
