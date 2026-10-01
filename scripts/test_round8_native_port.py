"""Offline regression for the staged native Round 8 port; no Lean/model calls."""
from __future__ import annotations
import hashlib
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

OVERLAY = Path(__file__).resolve().parents[1]
PUBLIC = Path(os.environ.get('PLECTIS_NATIVE_BASE', OVERLAY))


def file_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_cli(root: Path, *args: str, okay: bool = True):
    result = subprocess.run([sys.executable, '-B', str(root / 'scripts/benchmark_semantic_reasoning.py'),
                             *map(str, args)], capture_output=True, text=True, timeout=20)
    if okay and result.returncode:
        raise AssertionError(result.stderr or result.stdout)
    if not okay and not result.returncode:
        raise AssertionError('unsafe command was accepted')
    return result


class StagedNativePort(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'scripts').mkdir()
        for path in (OVERLAY / 'scripts').glob('*.py'):
            shutil.copyfile(path, self.root / 'scripts' / path.name)
        for name in ('reader_trace_adapter.py', 'relation_binding.py', 'relation_registry.py',
                     'run_kernel_probes.py', 'research_decision.py', 'research_record.py',
                     'contrast_ledger.py', 'lean_source.py', 'query_corpus.py',
                     'build_module_synopsis_index.py', 'validation_singleflight.py',
                     'lean_build_share.py', 'lean_package_share.py',
                     'coverage_build_targets.py'):
            shutil.copyfile(PUBLIC / 'scripts' / name, self.root / 'scripts' / name)
        source = OVERLAY / 'docs/research-commons/benchmarks/round8_candidate_development'
        target = self.root / 'docs/research-commons/benchmarks/round8_candidate_development'
        shutil.copytree(source, target)
        self.data = target

    def tearDown(self):
        self.temp.cleanup()

    def test_disclosed_bank_and_export_are_source_bound(self):
        result = json.loads(run_cli(self.root, 'restatement', 'candidate', 'validate').stdout)
        direct = subprocess.run([sys.executable, '-B',
                                 str(self.root / 'scripts/build_restatement_benchmark.py'),
                                 'candidate', 'validate'], capture_output=True, text=True, timeout=20)
        self.assertEqual(direct.returncode, 0, direct.stderr)
        self.assertEqual(json.loads(direct.stdout)['items'], 12)
        self.assertEqual((result['items'], result['dependence_clusters']), (12, 4))
        self.assertFalse(result['mathematical_gold'])
        self.assertFalse(result['current_source_files_checked'])
        row = json.loads((self.data / 'candidate_bank.jsonl').read_text().splitlines()[0])
        response = {'schema': 'plectis-relation-response/1', 'source_commit': row['source_commit'],
                    'answers': [{'task_id': row['task_id'], 'relation_label': 'unknown',
                                 'direction': 'unknown', 'supply_status': 'unknown',
                                 'assessment': 'unknown', 'reasoning': 'Needs independent review.',
                                 'evidence': [], 'unproved_obligations': [],
                                 'reverse_status': 'unestablished'}]}
        answer_path = self.root / 'response.json'
        answer_path.write_text(json.dumps(response))
        run_cli(self.root, 'restatement', 'candidate', 'parse-responses', answer_path)
        export = self.root / 'export'
        result = json.loads(run_cli(self.root, 'restatement', 'candidate',
                                    'export-review', answer_path, '--out', export).stdout)
        self.assertFalse(result['author_key_exported'])
        self.assertFalse(result['independence_verified'])
        manifest_sha = result['review_manifest_sha256']
        run_cli(self.root, 'restatement', 'candidate', 'verify-review-export', export,
                '--expected-manifest-sha256', manifest_sha)
        delivered = next((export / 'sources').glob('*.txt'))
        delivered.write_bytes(delivered.read_bytes() + b'\nchanged')
        run_cli(self.root, 'restatement', 'candidate', 'verify-review-export', export,
                '--expected-manifest-sha256', manifest_sha, okay=False)
        excerpt = self.data / 'sources/excerpts' / (row['source_handles'][0] + '.txt')
        excerpt.write_bytes(excerpt.read_bytes() + b'\nchanged')
        run_cli(self.root, 'restatement', 'candidate', 'parse-responses', answer_path, okay=False)
        run_cli(self.root, 'restatement', 'candidate', 'seal-gold', okay=False)

    def _prepared(self):
        source = self.root / 'material_source'; source.mkdir()
        (source / 'source.txt').write_text('Exact source text\n')
        digest = file_sha(source / 'source.txt')
        budget = {'wall_seconds': 5, 'max_model_requests': 2, 'max_tool_calls': 2,
                  'max_total_input_tokens': 100, 'max_total_output_tokens': 100,
                  'max_tool_response_bytes': 1000, 'max_total_tool_response_bytes': 2000,
                  'max_final_bytes': 2000}
        task = {'task_id': 'T01', 'family_id': 'F01', 'kind': 'restatement',
                'prompt': 'What does the exact source say?', 'gold_sha256': 'a' * 64,
                'world': 'test', 'split': 'disclosed_candidate_development',
                'material': {arm: [{'path': 'source.txt', 'sha256': digest}] for arm in ('P', 'F')}}
        spec = {'schema': 'plectis-reader-study/1', 'source_commit': '0268dd8bfb2a556a0c93078337d42c6d07138fa2',
                'mode': 'development', 'seed': 1, 'model_snapshot': 'SYNTHETIC_TEST',
                'arms': ['P', 'F'], 'budget': budget, 'tasks': [task]}
        spec_path = self.root / 'spec.json'; spec_path.write_text(json.dumps(spec))
        study = self.root / 'study'
        run_cli(self.root, 'study', 'prepare', '--spec', spec_path,
                '--source-root', source, '--out', study)
        control = study / 'private_control.json'
        return spec_path, control, json.loads(control.read_text())

    def test_inventory_and_controller_lifecycle_admission(self):
        spec, control, manifest = self._prepared()
        jobs = manifest['jobs']; first = jobs[0]
        job_home = control.parent / 'agent_jobs' / first['job_id']
        run_cli(self.root, 'study', 'verify-job', job_home,
                '--expected-spec-sha256', first['job_spec_sha256'])
        (job_home / 'material/answer_key.json').write_text('leak')
        run_cli(self.root, 'study', 'verify-job', job_home,
                '--expected-spec-sha256', first['job_spec_sha256'], okay=False)
        (job_home / 'material/answer_key.json').unlink()
        bridge = self.root / 'bridge.py'
        bridge.write_text('import json,sys\njson.load(sys.stdin)\nprint(json.dumps({"request_admitted_within_limits":True,"usage":{"input_tokens":1,"output_tokens":2,"cache_read_input_tokens":0,"cache_creation_input_tokens":0},"provider_run_id":"synthetic-bridge","final":{"answer":"The source says exact source text.","citations":["source.txt:1"],"abstention":False,"confidence":0.5}}))\n')
        deployment = self.root / 'deployment.json'
        deployment.write_text(json.dumps({'model_snapshot': 'SYNTHETIC_TEST',
                                          'client_command': [sys.executable, '-B', str(bridge)]}))
        paths = []
        for job in jobs:
            out = self.root / job['job_id']
            run_cli(self.root, 'study', 'execute', '--control', control, '--spec', spec,
                    '--expected-control-sha256', file_sha(control),
                    '--expected-spec-sha256', file_sha(spec), '--job-id', job['job_id'],
                    '--deployment', deployment, '--out', out, '--synthetic')
            receipt = out / 'receipt.json'
            self.assertEqual(json.loads(receipt.read_text())['status'], 'completed')
            paths.append({'job_id': job['job_id'], 'controller_receipt_path': out.name + '/receipt.json',
                          'controller_receipt_sha256': file_sha(receipt)})
        index = self.root / 'index.json'; index.write_text(json.dumps(paths))
        capture = self.root / 'capture'
        result = json.loads(run_cli(self.root, 'study', 'capture', '--control', control,
                                    '--spec', spec, '--expected-control-sha256', file_sha(control),
                                    '--expected-spec-sha256', file_sha(spec), '--index', index,
                                    '--out', capture, '--synthetic').stdout)
        self.assertEqual(result['executions'], 2)
        self.assertTrue((capture / 'executions.json').is_file())
        run_cli(self.root, 'study', 'capture', '--control', control, '--spec', spec,
                '--expected-control-sha256', file_sha(control), '--expected-spec-sha256', file_sha(spec),
                '--index', index, '--out', self.root / 'real_capture', okay=False)
        # Recompute trace/receipt/index hashes after each semantic mutation so
        # refusal reaches lifecycle accounting, not merely a stale digest.
        first_trace = self.root / jobs[0]['job_id'] / 'trace.jsonl'
        first_receipt = self.root / jobs[0]['job_id'] / 'receipt.json'
        original_trace = first_trace.read_bytes(); original_receipt = first_receipt.read_bytes()
        original_index = index.read_bytes()
        def altered_capture(label, mutate):
            rows = [json.loads(line) for line in original_trace.decode().splitlines()]
            receipt_obj = json.loads(original_receipt)
            rows = mutate(rows, receipt_obj)
            first_trace.write_text('\n'.join(json.dumps(row) for row in rows) + '\n')
            receipt_obj['raw_trace_sha256'] = file_sha(first_trace)
            first_receipt.write_text(json.dumps(receipt_obj))
            altered = copy.deepcopy(paths)
            altered[0]['controller_receipt_sha256'] = file_sha(first_receipt)
            index.write_text(json.dumps(altered))
            run_cli(self.root, 'study', 'capture', '--control', control, '--spec', spec,
                    '--expected-control-sha256', file_sha(control),
                    '--expected-spec-sha256', file_sha(spec), '--index', index,
                    '--out', self.root / label, '--synthetic', okay=False)
            first_trace.write_bytes(original_trace); first_receipt.write_bytes(original_receipt)
            index.write_bytes(original_index)
        def bad_response_index(rows, receipt_obj):
            next(row for row in rows if row.get('type') == 'provider_response')['index'] = 2
            return rows
        def missing_response(rows, receipt_obj):
            return [row for row in rows if row.get('type') != 'provider_response']
        def missing_assistant(rows, receipt_obj):
            return [row for row in rows if row.get('type') != 'assistant']
        def altered_usage(rows, receipt_obj):
            next(row for row in rows if row.get('type') == 'assistant')['message']['usage']['output_tokens'] = 3
            receipt_obj['reported_usage']['output_tokens'] = 3
            return rows
        altered_capture('wrong_index', bad_response_index)
        altered_capture('missing_response', missing_response)
        altered_capture('missing_usage_identity', missing_assistant)
        altered_capture('usage_mismatch', altered_usage)
        paths[1]['controller_receipt_path'] = paths[0]['controller_receipt_path']
        paths[1]['controller_receipt_sha256'] = paths[0]['controller_receipt_sha256']
        index.write_text(json.dumps(paths))
        run_cli(self.root, 'study', 'capture', '--control', control, '--spec', spec,
                '--expected-control-sha256', file_sha(control), '--expected-spec-sha256', file_sha(spec),
                '--index', index, '--out', self.root / 'reused_capture', '--synthetic', okay=False)
        trace = self.root / jobs[0]['job_id'] / 'trace.jsonl'
        lines = trace.read_text().splitlines()
        self.assertEqual(json.loads(lines[-1])['type'], 'controller_stop')
        trace.write_text('\n'.join(lines[:-1]) + '\n')
        receipt_path = self.root / jobs[0]['job_id'] / 'receipt.json'
        receipt = json.loads(receipt_path.read_text())
        receipt['raw_trace_sha256'] = file_sha(trace)
        receipt_path.write_text(json.dumps(receipt))
        paths[0]['controller_receipt_sha256'] = file_sha(receipt_path)
        paths[1]['controller_receipt_path'] = jobs[1]['job_id'] + '/receipt.json'
        paths[1]['controller_receipt_sha256'] = file_sha(self.root / paths[1]['controller_receipt_path'])
        index.write_text(json.dumps(paths))
        run_cli(self.root, 'study', 'capture', '--control', control, '--spec', spec,
                '--expected-control-sha256', file_sha(control), '--expected-spec-sha256', file_sha(spec),
                '--index', index, '--out', self.root / 'tampered_capture', '--synthetic', okay=False)

    def test_empty_control_cohort_refused_before_execute_or_capture(self):
        spec, control, manifest = self._prepared()
        manifest['jobs'] = []
        control.write_text(json.dumps(manifest))
        index = self.root / 'empty_index.json'; index.write_text('[]')
        run_cli(self.root, 'study', 'capture', '--control', control, '--spec', spec,
                '--expected-control-sha256', file_sha(control),
                '--expected-spec-sha256', file_sha(spec), '--index', index,
                '--out', self.root / 'empty_capture', '--synthetic', okay=False)
        run_cli(self.root, 'study', 'execute', '--control', control, '--spec', spec,
                '--expected-control-sha256', file_sha(control),
                '--expected-spec-sha256', file_sha(spec), '--job-id', 'any',
                '--deployment', self.root / 'nonexistent_deployment.json',
                '--out', self.root / 'empty_execute', '--synthetic', okay=False)

    def test_historical_parser_authenticated_before_execution(self):
        import importlib.util
        from unittest import mock
        path = OVERLAY / 'scripts/restatement_candidate_support.py'
        spec = importlib.util.spec_from_file_location('staged_candidates', path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        checkout = self.root / 'historical'; (checkout / 'scripts').mkdir(parents=True)
        sentinel = self.root / 'parser_executed'
        parser = checkout / 'scripts/relation_registry.py'
        parser.write_text(f'open({str(sentinel)!r}, "w").write("unsafe")\n')
        class Result:
            def __init__(self, code=0, stdout=b''):
                self.returncode = code; self.stdout = stdout
        for mode, message in [('wrong_head', 'frozen commit'),
                              ('dirty', 'tracked differences'),
                              ('untracked', 'frozen Git inventory'),
                              ('wrong_blob', 'parser bytes differ')]:
            def fake_git(argv, **kwargs):
                command = argv[3]
                if command == 'rev-parse':
                    return Result(stdout=('0' * 40 if mode == 'wrong_head' else module.COMMIT) + '\n')
                if command == 'diff':
                    return Result(code=1 if mode == 'dirty' else 0)
                if command == 'ls-files':
                    return Result(stdout=b'' if mode == 'untracked' else b'scripts/relation_registry.py\0')
                if command == 'show':
                    return Result(stdout=b'not the checked-out parser')
                raise AssertionError(argv)
            with self.subTest(mode=mode), mock.patch.object(module.subprocess, 'run', side_effect=fake_git):
                with self.assertRaisesRegex(module.Invalid, message):
                    module.validate_sources(checkout, {})
                self.assertFalse(sentinel.exists())

    def test_bridge_json_refuses_ambiguous_values(self):
        import importlib.util
        path = OVERLAY / 'scripts/reader_study.py'
        spec = importlib.util.spec_from_file_location('staged_reader_study', path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        with self.assertRaisesRegex(ValueError, 'duplicate JSON key'):
            module._strict_json('{"status":"completed","status":"invalid_output"}')
        with self.assertRaisesRegex(ValueError, 'nonfinite'):
            module._strict_json('{"confidence":1e999}')


if __name__ == '__main__':
    unittest.main()
