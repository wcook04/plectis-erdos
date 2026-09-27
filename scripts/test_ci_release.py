#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression checks for local/GitHub parity and complete failure reporting."""
import contextlib
import io
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import check_ci_release as release
import check_release


class ReleaseParityTests(unittest.TestCase):
    def test_current_registry_and_both_entrypoints(self):
        self.assertEqual(release.registry_errors(), [])
        source = (release.ROOT / '.github/workflows/lean.yml').read_text()
        self.assertEqual(release.workflow_errors(source), [])
        self.assertEqual(check_release.late_check_commands()['github_release_contracts'],
                         [check_release.sys.executable, str(release.ROOT / 'scripts/check_ci_release.py')])
        self.assertIn(('scripts/test_corpus_orientation.py',), release.COMMANDS)
        self.assertIn(('-m', 'unittest', 'scripts.test_formal_conjectures_crosswalk', '-v'), release.COMMANDS)
        self.assertIn(('-O', 'scripts/test_expert_handoffs.py'), release.COMMANDS)

    def test_github_only_check_and_missing_shared_gate_are_rejected(self):
        source = (release.ROOT / '.github/workflows/lean.yml').read_text()
        extra = source + '\n      - name: Escaped test\n        run: python3 scripts/test_new.py\n'
        self.assertTrue(release.workflow_errors(extra))
        self.assertTrue(release.workflow_errors(source.replace('run: python3 scripts/check_release.py',
                                                              'run: echo looks-green')))
        self.assertTrue(release.workflow_errors(source.replace('  release-surfaces:', '  renamed:')))
        self.assertTrue(release.workflow_errors(source + '\n      - run: echo accidental-gate\n'))

    def test_real_failure_does_not_hide_other_failures_or_successes(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'bad.py').write_text('raise SystemExit(7)\n')
            (root / 'ok.py').write_text("from pathlib import Path; Path('reached').touch()\n")
            (root / 'optimized.py').write_text('raise SystemExit(0 if __debug__ else 9)\n')
            commands = (('bad.py',), ('ok.py',), ('-O', 'optimized.py'), ('missing.py',))
            with contextlib.redirect_stdout(io.StringIO()):
                result = release.run_suite(commands, root=root, timeout=10)
            self.assertEqual(result['completed'], 4)
            self.assertEqual(result['failed'], 3)
            self.assertTrue((root / 'reached').exists())
            self.assertEqual([r['exit_code'] for r in result['results']], [7, 0, 9, 2])

    def test_timeout_is_failure_and_next_gate_runs(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'wait.py').write_text('import time; time.sleep(20)\n')
            (root / 'ok.py').write_text('raise SystemExit(0)\n')
            with contextlib.redirect_stdout(io.StringIO()):
                result = release.run_suite((('wait.py',),), root=root, timeout=.2)
                next_result = release.run_suite((('ok.py',),), root=root, timeout=10)
            self.assertEqual(result['status'], 'failed')
            self.assertTrue(result['results'][0]['timed_out'])
            self.assertEqual(next_result['status'], 'passed')

    def test_registry_refuses_missing_duplicate_and_recursive_gates(self):
        for commands in ((('absent.py',),), (('scripts/check_release.py',),),
                         (('scripts/test_ci_release.py',),) * 2):
            self.assertTrue(release.registry_errors(commands))

    def test_admission_job_allows_local_deadline_and_setup(self):
        import check_push
        import re
        source = (release.ROOT / '.github/workflows/lean.yml').read_text()
        body = source.split('  change_scope:\n', 1)[1].split('\n  build:', 1)[0]
        minutes = int(re.search(r'timeout-minutes: (\d+)', body).group(1))
        self.assertGreaterEqual(minutes * 60, check_push.PREFLIGHT_TIMEOUT_SECONDS + 120)

    def test_actions_annotation_cannot_create_another_command(self):
        value = release.escape_annotation('bad%\n::warning::surprise\r')
        self.assertEqual(value, 'bad%25%0A::warning::surprise%0D')


if __name__ == '__main__':
    unittest.main()
