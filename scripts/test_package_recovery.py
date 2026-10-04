#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Failed return packaging preserves bytes and gives a safe new-output retry."""
from __future__ import annotations

import argparse
import contextlib
import io
import json
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

import continue_research as c


ROOT = Path(__file__).resolve().parents[1]


def run(argv):
    result = subprocess.run(argv, cwd=ROOT, env=c.child_environment(), capture_output=True, text=True, timeout=30)
    if result.returncode:
        raise AssertionError((argv, result.stdout, result.stderr))
    return result


class PackageRecoveryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = tempfile.TemporaryDirectory(prefix='public-package-session-')
        base = Path(cls.fixture.name)
        cls.sessions = base / "session root's spaces"
        cli = [sys.executable, str(ROOT / 'scripts/continue_research.py'), '--sessions-root', str(cls.sessions)]
        run([*cli, 'start', '--session', 'package_recovery', '--area', 'navigation',
             '--starting-path', 'scripts/agent_entry.py', '--validation-plan', 'Replay contributor paraphrases',
             '--repository-origin', 'https://github.com/wcook04/plectis-erdos',
             '--frontier', 'fixture/router', '--intent', 'Improve the contributor journey',
             '--stop-condition', 'Stop after a bounded comparison', '--contributor', 'Fixture Contributor',
             '--model-system', 'not_used', '--provider', 'not_used', '--allow-dirty'])
        run([sys.executable, str(ROOT / 'scripts/proof_workbench.py'), '--sessions-root', str(cls.sessions),
             'close', '--session', 'package_recovery', '--outcome', 'open', '--summary', 'Bounded proposal ready for review'])
        manifest = json.loads((cls.sessions / 'package_recovery/continuation.json').read_text())
        returned = json.loads((ROOT / 'scripts/fixtures/research_returns/valid_inconclusive.json').read_text())
        returned['record_kind'] = 'submitted_return'
        returned['repository'].update(starting_commit=manifest['starting_commit'], origin=manifest['repository_origin'])
        returned['frontier'] = {'track': 'architecture', 'area': 'navigation', 'handle': 'fixture/router',
                                'bounded_question': manifest['frontier']['intent'], 'stop_condition': manifest['frontier']['stop_condition'],
                                'starting_paths': ['scripts/agent_entry.py']}
        returned['result'].update(claim_ceiling='architecture_proposal', surviving_boundary='Routing proposal; no mathematical claim.')
        returned['evidence'][0]['command'] = 'python3 scripts/test_agent_entry.py'
        cls.return_path = base / "return's record.json"
        cls.return_path.write_text(json.dumps(returned))

    @classmethod
    def tearDownClass(cls):
        cls.fixture.cleanup()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='package-owned-by-test-')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.output = self.base / "package's output"
        self.args = argparse.Namespace(sessions_root=self.sessions, session='package_recovery', return_json=self.return_path,
                                       route_memory_receipt=None, replay=False, output=self.output)

    def argv(self, output=None):
        return ['--sessions-root', str(self.sessions), 'package', '--session', 'package_recovery',
                '--return-json', str(self.return_path), '--output', str(output or self.output)]

    def retry(self, recovery):
        inspection = subprocess.run(shlex.split(recovery['inspection_command']), capture_output=True, text=True, timeout=10)
        self.assertEqual(inspection.returncode, 0, inspection.stderr)
        args = c.build_parser().parse_args(shlex.split(recovery['retry_command'])[2:])
        result = c.cmd_package(args)
        self.assertTrue(result['valid'])
        self.assertNotEqual(args.output, self.output)
        self.assertTrue((args.output / 'package.json').is_file())

    def test_untouched_write_failure_retains_bytes_and_gives_new_output_retry(self):
        original = c._write_package_file
        def fail(path, data):
            if path == self.output / 'session/continuation.json':
                raise OSError('ordinary disk failure')
            return original(path, data)
        with mock.patch.object(c, '_write_package_file', fail), self.assertRaises(SystemExit) as caught:
            c.cmd_package(self.args)
        self.assertIn('Output was retained', str(caught.exception))
        self.assertIn('Retry:', str(caught.exception))
        retained = (self.output / 'return.json').read_bytes()
        retry = str(caught.exception).split(' Retry: ', 1)[1]
        parsed = c.build_parser().parse_args(shlex.split(retry)[2:])
        self.assertTrue(c.cmd_package(parsed)['valid'])
        self.assertEqual((self.output / 'return.json').read_bytes(), retained)
        with self.assertRaises(SystemExit) as existing:
            c.cmd_package(self.args)
        self.assertIn('already exists', str(existing.exception))
        self.assertEqual((self.output / 'return.json').read_bytes(), retained)

    def test_partial_write_bytes_are_retained(self):
        original = c._write_package_file
        partial = b'partially emitted bytes\n'
        protected = self.output / 'session/continuation.json'
        def fail(path, data):
            if path == protected:
                with path.open('xb') as stream:
                    stream.write(partial)
                raise OSError('failure after a partial write')
            return original(path, data)
        with mock.patch.object(c, '_write_package_file', fail), self.assertRaises(SystemExit):
            c.cmd_package(self.args)
        self.assertEqual(protected.read_bytes(), partial)
        self.assertTrue((self.output / 'return.json').is_file())
        self.assertFalse((self.output / 'package.json').exists())

    def test_changed_replaced_unemitted_and_linked_expected_names_are_preserved(self):
        for mode in ('changed', 'replaced', 'unemitted', 'symlink'):
            with self.subTest(mode=mode):
                out = self.base / mode
                self.args.output = out
                original = c._write_package_file
                protected = out / ('session/route.json' if mode == 'unemitted' else 'return.json')
                payload = b'operator-owned bytes must remain identical\n'
                outside = self.base / (mode + '-outside')
                def fail(path, data):
                    if path == out / 'session/continuation.json':
                        if mode == 'replaced':
                            (out / 'return.json').rename(out / 'original-return.json')
                        if mode == 'symlink':
                            Path.write_bytes(outside, payload)
                            protected.unlink()
                            protected.symlink_to(outside)
                        else:
                            Path.write_bytes(protected, payload)
                        raise OSError('fail after external change')
                    return original(path, data)
                with mock.patch.object(c, '_write_package_file', fail), self.assertRaises(SystemExit):
                    c.cmd_package(self.args)
                self.assertEqual(protected.read_bytes(), payload)
                if mode == 'replaced':
                    self.assertTrue((out / 'original-return.json').exists())
                if mode == 'symlink':
                    self.assertTrue(protected.is_symlink())
                    self.assertEqual(outside.read_bytes(), payload)

    def test_unowned_expected_entry_is_never_overwritten(self):
        original = c._write_package_file
        protected = self.output / 'session/continuation.json'
        payload = b'another writer created this expected entry first\n'
        def race(path, data):
            result = original(path, data)
            if path == self.output / 'return.json':
                protected.parent.mkdir()
                protected.write_bytes(payload)
            return result
        with mock.patch.object(c, '_write_package_file', race), self.assertRaises(SystemExit):
            c.cmd_package(self.args)
        self.assertEqual(protected.read_bytes(), payload)
        self.assertFalse((self.output / 'package.json').exists())

    def test_interrupt_main_returns_honest_nonzero_json_and_retry_preserves_partial(self):
        original = c._write_package_file
        def interrupt(path, data):
            if path == self.output / 'session/continuation.json':
                raise KeyboardInterrupt
            return original(path, data)
        stdout = io.StringIO()
        with mock.patch.object(c, '_write_package_file', interrupt), contextlib.redirect_stdout(stdout):
            code = c.main(self.argv())
        result = json.loads(stdout.getvalue())
        self.assertNotEqual(code, 0)
        self.assertFalse(result['valid'])
        self.assertTrue(result['interrupted'])
        self.assertFalse(result['recovery']['package_complete'])
        retained = (self.output / 'return.json').read_bytes()
        self.retry(result['recovery'])
        self.assertEqual((self.output / 'return.json').read_bytes(), retained)

    def test_complete_published_package_survives_lost_receipt(self):
        original = c._write_package_file
        def interrupt(path, data):
            result = original(path, data)
            if path == self.output / 'package.json':
                raise KeyboardInterrupt
            return result
        stdout = io.StringIO()
        with mock.patch.object(c, '_write_package_file', interrupt), contextlib.redirect_stdout(stdout):
            code = c.main(self.argv())
        result = json.loads(stdout.getvalue())
        self.assertNotEqual(code, 0)
        self.assertFalse(result['valid'])
        self.assertTrue(result['recovery']['package_complete'])
        self.assertIsNone(result['recovery']['retry_command'])
        before = {p.relative_to(self.output): p.read_bytes() for p in self.output.rglob('*') if p.is_file()}
        manifest = json.loads(before[Path('package.json')])
        for row in manifest['files']:
            self.assertEqual(c._sha256(before[Path(row['path'])]), row['sha256'])
        with self.assertRaises(SystemExit):
            c.cmd_package(self.args)
        self.assertEqual(before, {p.relative_to(self.output): p.read_bytes() for p in self.output.rglob('*') if p.is_file()})

    def test_manifest_existence_does_not_prove_completion(self):
        original = c._write_package_file
        for mode in ('bad_bytes', 'extra', 'symlink'):
            with self.subTest(mode=mode):
                out = self.base / mode
                self.args.output = out
                def interrupt(path, data):
                    result = original(path, data)
                    if path == out / 'package.json':
                        if mode == 'bad_bytes':
                            Path.write_bytes(out / 'return.json', b'changed after publication\n')
                        elif mode == 'extra':
                            Path.write_bytes(out / 'unowned.txt', b'unowned bytes\n')
                        else:
                            (out / 'return.json').rename(out / 'outside-return.json')
                            (out / 'return.json').symlink_to(out / 'outside-return.json')
                        raise KeyboardInterrupt
                    return result
                with mock.patch.object(c, '_write_package_file', interrupt):
                    result = c.cmd_package(self.args)
                self.assertFalse(result['recovery']['package_complete'])
                self.assertTrue((out / 'package.json').exists())
                self.assertTrue(result['recovery']['retry_command'])

    def test_actual_sigint_keeps_partial_bytes_and_emits_recovery(self):
        ready = self.base / 'ready'
        driver = self.base / 'interrupt_driver.py'
        driver.write_text("import sys,time\nfrom pathlib import Path\nfrom unittest import mock\n"
                          f"sys.path.insert(0,{str(Path(__file__).parent)!r})\n"
                          "import test_package_recovery as t\nc=t.c\noriginal=c._write_package_file\n"
                          f"output=Path({str(self.output)!r});ready=Path({str(ready)!r})\n"
                          "def pause(path,data):\n result=original(path,data)\n if path==output/'return.json':\n"
                          "  ready.write_text('written')\n  time.sleep(30)\n return result\n"
                          "with mock.patch.object(c,'_write_package_file',pause): raise SystemExit(c.main(sys.argv[1:]))\n")
        child = subprocess.Popen([sys.executable, str(driver), *self.argv()], cwd=ROOT, env=c.child_environment(),
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 10
            while not ready.exists() and child.poll() is None and time.monotonic() < deadline:
                time.sleep(.02)
            self.assertTrue(ready.exists())
            child.send_signal(signal.SIGINT)
            stdout, stderr = child.communicate(timeout=10)
            self.assertNotEqual(child.returncode, 0, (stdout, stderr))
            result = json.loads(stdout)
            self.assertTrue(result['interrupted'])
            self.assertFalse(result['valid'])
            self.assertFalse(result['recovery']['package_complete'])
            self.assertTrue((self.output / 'return.json').is_file())
            self.assertFalse((self.output / 'package.json').exists())
        finally:
            if child.poll() is None:
                child.kill()
                child.wait()


if __name__ == '__main__':
    unittest.main()
