"""Offline unit/contract tests. Passing these is not repository admission or Lean checking."""

import _test_bootstrap  # noqa: F401
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
import reader_study as study
import research_evidence as audit
import reader_trace_adapter as trace

H = 'a' * 64
G = 'b' * 64

def assistant(mid='m1', uid='u1', usage=None, tool='Bash'):
    return {'uuid': uid, 'type': 'assistant', 'timestamp': '2026-09-28T00:00:01Z',
            'message': {'role': 'assistant', 'id': mid, 'model': 'fixture-model',
                        'usage': usage if usage is not None else {'input_tokens': 3, 'output_tokens': 5},
                        'content': [{'type': 'tool_use', 'id': 't1', 'name': tool,
                                     'input': {'command': 'read-only fixture'}}]}}

class TraceTests(unittest.TestCase):
    def test_empty_unknown(self):
        r = trace.normalize([])
        self.assertIsNone(r['usage']['input_tokens']['total_if_complete'])
        self.assertIsNone(r['billed_usd'])
    def test_event_deduplication(self):
        a = assistant(); r = trace.normalize([a, copy.deepcopy(a)])
        self.assertEqual(r['assistant_messages'], 1)
        self.assertEqual(r['usage']['input_tokens']['total_if_complete'], 3)
        self.assertEqual(r['tool_counts']['Bash'], 1)
    def test_event_conflict(self):
        a = assistant(); b = copy.deepcopy(a); b['timestamp'] = '2026-09-28T00:00:02Z'
        with self.assertRaises(ValueError): trace.normalize([a, b])
    def test_message_split_deduplication(self):
        a = assistant(); b = assistant(uid='u2'); b['message']['usage']['output_tokens'] = 9
        r = trace.normalize([a, b])
        self.assertEqual(r['usage']['output_tokens']['total_if_complete'], 9)
    def test_missing_cache_is_not_zero(self):
        r = trace.normalize([assistant()])
        self.assertIsNone(r['usage']['cache_read_input_tokens']['total_if_complete'])
    def test_unidentified_assistant_prevents_complete_usage_total(self):
        identified = assistant(usage={'input_tokens': 10, 'output_tokens': 2})
        unidentified = assistant(mid=None, uid='u2', usage={'input_tokens': 5, 'output_tokens': 1})
        r = trace.normalize([identified, unidentified])
        self.assertEqual(r['usage']['input_tokens']['observed_subtotal'], 10)
        self.assertIsNone(r['usage']['input_tokens']['total_if_complete'])
        self.assertEqual(r['usage']['input_tokens']['messages_missing'], 1)
        self.assertEqual(r['unidentified_assistant_events'], 1)
    def test_iterations_not_added(self):
        a = assistant(usage={'input_tokens': 2, 'output_tokens': 4,
                             'iterations': [{'input_tokens': 2, 'output_tokens': 4}]})
        self.assertEqual(trace.normalize([a])['usage']['output_tokens']['total_if_complete'], 4)
    def test_failed_structured_attempt_is_not_final(self):
        r = trace.normalize([assistant(tool='StructuredOutput')])
        self.assertEqual(r['structured_output_attempt_count'], 1)
        self.assertEqual(r['structured_final_count'], 0)
    def test_accepted_final_attachment(self):
        accepted = {'uuid': 'a', 'type': 'attachment', 'timestamp': '2026-09-28T00:00:03Z',
                    'attachment': {'type': 'structured_output', 'data': {'answer': 'x'}}}
        r = trace.normalize([assistant(tool='StructuredOutput'), accepted])
        self.assertEqual(r['structured_final'], {'answer': 'x'})
        self.assertEqual(r['elapsed_to_first_accepted_structured_final_seconds'], 2)
    def test_multiple_accepted_finals_require_review(self):
        a = {'type': 'attachment', 'attachment': {'type': 'structured_output', 'data': {'answer': 'x'}}}
        b = copy.deepcopy(a); b['attachment']['data']['answer'] = 'y'
        self.assertIsNone(trace.normalize([a, b])['structured_final'])
    def test_hook_counts_without_content_exposure(self):
        r = trace.normalize([{'type': 'attachment', 'attachment': {'type': 'hook_additional_context', 'text': 'SECRET'}}])
        self.assertEqual(r['attachment_counts']['hook_additional_context'], 1)
        self.assertNotIn('SECRET', json.dumps(r))
    def test_invalid_usage(self):
        with self.assertRaises(ValueError): trace.normalize([assistant(usage={'input_tokens': -1})])

class MetricTests(unittest.TestCase):
    def row(self):
        return {'attempt_id': 'a', 'eligible': True, 'review': None,
                'received': None, 'landed': None, 'billed_usd': None}
    def test_empty_rates_unknown(self):
        r = audit.attempts([], '2026-09-28T00:00:00Z')
        self.assertIsNone(r['false_admission_rate_among_reviewed'])
        self.assertIsNone(r['qualified_insight_families_per_100_eligible_attempts'])
    def test_missing_review_retained(self):
        r = audit.attempts([self.row()], '2026-09-28T00:00:00Z')
        self.assertEqual(r['review_missing'], 1)
        self.assertFalse(r['insight_yield_complete_review'])
        self.assertIsNone(r['billed_usd_complete_total'])
    def test_companion_duplicate_id_refused(self):
        with self.assertRaises(ValueError): audit.attempts([self.row(), self.row()], '2026-09-28T00:00:00Z')
    def test_backfill_clock_refused(self):
        r = self.row(); r['received'] = {'clock_class': 'recorded_at', 'occurred_at': '2026-09-01T00:00:00Z'}
        with self.assertRaises(ValueError): audit.attempts([r], '2026-09-28T00:00:00Z')
    def test_right_censoring_retained(self):
        r = self.row(); r['received'] = {'clock_class': 'contemporaneous_occurrence',
            'occurred_at': '2026-09-27T00:00:00Z', 'evidence_sha256': H}
        out = audit.attempts([r], '2026-09-28T00:00:00Z')
        d = out['known_clock_durations_with_censor_flags'][0]
        self.assertEqual(d['seconds'], 86400); self.assertFalse(d['landed_by_cutoff'])
    def test_insight_requires_all_axes(self):
        r = self.row(); r['review'] = {'receipt_id': 'native', 'receipt_sha256': H, 'insight_qualified': True}
        with self.assertRaises(ValueError): audit.attempts([r], '2026-09-28T00:00:00Z')
    def test_duplicate_rejection_not_insight(self):
        r = self.row(); r['review'] = {'receipt_id': 'native', 'receipt_sha256': H,
            'corpus_relation': 'equivalent_restatement', 'admitted_as_progress': False}
        out = audit.attempts([r], '2026-09-28T00:00:00Z')
        self.assertEqual(out['qualified_insight_families_observed'], 0)
        self.assertEqual(out['false_admission_rate_among_known_duplicate_submissions'], 0)

class StudyTests(unittest.TestCase):
    def test_mcnemar_known(self):
        self.assertAlmostEqual(study.mcnemar_p(6, 0), .03125)
        self.assertEqual(study.mcnemar_p(0, 0), 1)
    def test_power_null_conservative(self):
        self.assertLessEqual(study.exact_power(30, 0, .4), .05 + 1e-12)
    def test_power_increases_with_sample(self):
        self.assertGreater(study.exact_power(80, .2, .4), study.exact_power(20, .2, .4))
    def test_small_tied_cohort_does_not_rule_out_useful_effect(self):
        c,e,g = self.cohort()
        for grade in g: grade['correct'] = True
        r = study.analyze(c,e,g,bootstrap=100)
        self.assertEqual(r['family_bootstrap_95_interval'], [0, 0])
        self.assertGreater(r['conservative_independent_family_95_interval'][1], .1)
        self.assertIsNone(r['minimum_useful_effect_ruled_out_by_interval'])
        self.assertEqual(r['analysis_role'], 'development_descriptive')
    def test_tied_bound_matches_closed_form(self):
        ci = study.conservative_difference_interval([0] * 352)
        self.assertAlmostEqual(ci[1], 1 - .025 ** (1 / 352))
        self.assertAlmostEqual(ci[0], -ci[1])
    def test_conservative_interval_rejects_invalid_difference(self):
        with self.assertRaises(ValueError): study.conservative_difference_interval([2])
    def test_power_invalid(self):
        with self.assertRaises(ValueError): study.exact_power(20, .5, .2)
    def spec(self, h):
        return {'schema': 'plectis-reader-study/1', 'mode': 'development', 'seed': 7,
            'model_snapshot': 'fixture-only', 'arms': ['P', 'F'], 'budget': {'seconds': 10},
            'tasks': [{'task_id': 'fixture', 'family_id': 'fixture-family', 'world': 'fixture-world',
            'kind': 'status', 'prompt': 'Synthetic I/O test only.', 'gold_sha256': G,
            'material': {a: [{'path': 'source.txt', 'sha256': h}] for a in ('P', 'F')}}]}
    def test_prepare_roundtrip(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp); src = base / 'source'; src.mkdir(); f = src / 'source.txt'; f.write_text('fixture')
            control = study.prepare(self.spec(study.sha(f.read_bytes())), src, base / 'out')
            self.assertEqual(len(control['jobs']), 2)
            for j in control['jobs']:
                study.verify_job(base / 'out/agent_jobs' / j['job_id'], j['job_spec_sha256'])
            self.assertNotIn('gold_sha256', (base / 'out/agent_jobs' / control['jobs'][0]['job_id'] / 'job.json').read_text())
    def test_source_hash_change_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            b = Path(tmp); src = b / 'source'; src.mkdir(); (src / 'source.txt').write_text('x')
            with self.assertRaises(ValueError): study.prepare(self.spec(H), src, b / 'out')
            self.assertFalse((b / 'out').exists())
    def test_rewritten_job_prompt_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp); src = base / 'source'; src.mkdir()
            (src / 'source.txt').write_text('x')
            control = study.prepare(self.spec(study.sha(b'x')), src, base / 'out')
            row = control['jobs'][0]; home = base / 'out/agent_jobs' / row['job_id']
            job = json.loads((home / 'job.json').read_text())
            job['prompt'] = 'changed after registration'
            (home / 'job.json').write_text(json.dumps(job))
            with self.assertRaisesRegex(ValueError, 'frozen control'):
                study.verify_job(home, row['job_spec_sha256'])
    def test_path_traversal(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError): study.safe_file(Path(tmp), '../source.txt')
    def test_symlink_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            b = Path(tmp); (b / 'real').write_text('x'); (b / 'link').symlink_to(b / 'real')
            with self.assertRaises(ValueError): study.safe_file(b, 'link')
    def test_answer_bearing_projection_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            b = Path(tmp); (b / 'theory_lab.json').write_text('{}')
            with self.assertRaises(ValueError): study.safe_file(b, 'theory_lab.json')
    def cohort(self):
        control = {'mode': 'development', 'jobs': []}; executions = []; grades = []
        for i in range(8):
            for arm in ['P', 'F']:
                jid = f'{i}{arm}'
                control['jobs'].append({'job_id': jid, 'task_id': f't{i}', 'family_id': f'f{i}',
                                       'world': 'w', 'arm': arm, 'gold_sha256': G})
                executions.append({'job_id': jid, 'status': 'completed', 'trace_sha256': H, 'answer': 'fixture'})
                grades.append({'job_id': jid, 'final': True, 'correct': arm == 'F', 'severe_error': False,
                    'rater_ids': ['rater1', 'rater2'], 'review_sha256': H, 'gold_sha256': G, 'trace_sha256': H})
        return control, executions, grades
    def test_paired_analysis(self):
        c,e,g = self.cohort(); r = study.analyze(c,e,g,bootstrap=100)
        self.assertEqual(r['paired_difference'], 1); self.assertEqual(r['families'], 8)
        self.assertIsNone(r['exact_mcnemar_two_sided_p'])
        self.assertIsNone(r['claim_threshold'])
    def test_confirmatory_primary_plan_reports_prespecified_inference(self):
        c,e,g = self.cohort(); c['mode'] = 'confirmatory'
        c['analysis_plan'] = copy.deepcopy(study.ANALYSIS_PLAN)
        r = study.analyze(c,e,g,bootstrap=100)
        self.assertEqual(r['analysis_role'], 'confirmatory_primary')
        self.assertAlmostEqual(r['exact_mcnemar_two_sided_p'], study.mcnemar_p(8, 0))
        self.assertEqual(r['claim_threshold'], .10)
    def test_secondary_confirmatory_contrast_is_descriptive(self):
        c,e,g = self.cohort(); c['mode'] = 'confirmatory'
        c['analysis_plan'] = copy.deepcopy(study.ANALYSIS_PLAN)
        for job in c['jobs']:
            if job['arm'] == 'P': job['arm'] = 'R'
        r = study.analyze(c,e,g,baseline='R',treatment='F',bootstrap=100)
        self.assertEqual(r['analysis_role'], 'secondary_descriptive_no_multiplicity_plan')
        self.assertIsNone(r['exact_mcnemar_two_sided_p'])
        self.assertIsNone(r['minimum_useful_effect_ruled_out_by_interval'])
    def test_confirmatory_plan_must_be_frozen(self):
        c,e,g = self.cohort(); c['mode'] = 'confirmatory'
        with self.assertRaisesRegex(ValueError, 'frozen F-P'):
            study.analyze(c,e,g,bootstrap=100)
    def test_confirmatory_prepare_requires_reviewed_primary_plan(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp); src = base / 'source'; src.mkdir()
            (src / 'source.txt').write_text('fixture')
            spec = self.spec(study.sha(b'fixture'))
            spec['mode'] = 'confirmatory'; spec['tasks'][0]['split'] = 'sealed_confirmatory'
            with self.assertRaisesRegex(ValueError, 'explicit fixed F-P'):
                study.prepare(spec, src, base / 'out')
            spec['analysis_plan'] = copy.deepcopy(study.ANALYSIS_PLAN)
            control = study.prepare(spec, src, base / 'out')
            self.assertEqual(control['analysis_plan'], study.ANALYSIS_PLAN)
    def test_identical_arms_refused(self):
        c,e,g = self.cohort()
        with self.assertRaisesRegex(ValueError, 'distinct'):
            study.analyze(c,e,g, baseline='F', treatment='F', bootstrap=100)
    def test_string_is_not_two_graders(self):
        c,e,g = self.cohort(); g[0]['rater_ids'] = 'ab'
        with self.assertRaisesRegex(ValueError, 'grader identities'):
            study.analyze(c,e,g, bootstrap=100)
    def test_duplicate_control_identity_refused(self):
        c,e,g = self.cohort(); c['jobs'].append(copy.deepcopy(c['jobs'][0]))
        with self.assertRaisesRegex(ValueError, 'duplicate job'):
            study.analyze(c,e,g, bootstrap=100)
    def test_unrun_not_silently_dropped(self):
        c,e,g = self.cohort(); e[0]['status'] = 'not_run'
        with self.assertRaises(ValueError): study.analyze(c,e,g,bootstrap=100)
    def test_pending_grade_refused(self):
        c,e,g = self.cohort(); g.pop()
        with self.assertRaises(ValueError): study.analyze(c,e,g,bootstrap=100)
    def test_timeout_scored_zero(self):
        c,e,g = self.cohort(); e[-1]['status'] = 'timeout'; g.pop()
        r = study.analyze(c,e,g,bootstrap=100)
        self.assertEqual(r['treatment_accuracy'], 7/8)
    def test_grade_trace_mismatch(self):
        c,e,g = self.cohort(); g[0]['trace_sha256'] = G
        with self.assertRaises(ValueError): study.analyze(c,e,g,bootstrap=100)
    def test_grade_gold_mismatch(self):
        c,e,g = self.cohort(); g[0]['gold_sha256'] = H
        with self.assertRaises(ValueError): study.analyze(c,e,g,bootstrap=100)
    def test_pseudoreplication_refused(self):
        c,e,g = self.cohort(); c['jobs'][2]['family_id'] = 'f0'
        with self.assertRaises(ValueError): study.analyze(c,e,g,bootstrap=100)

# This owner is registered in check_ci_release.py in ordinary and optimized Python.
from test_reader_paper_protocol import PaperProtocolTests

if __name__ == '__main__': unittest.main()
