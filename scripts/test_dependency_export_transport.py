import importlib.util
import sys
import unittest
from pathlib import Path
from subprocess import CompletedProcess
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
PUBLIC = HERE
sys.path.insert(0, str(PUBLIC))
spec = importlib.util.spec_from_file_location('export_fix', HERE / 'build_lean_dependency_index.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
DATA = 'AIW_NODE\tErdosProblems.test\tErdosProblems.Test\nAIW_INTERNAL_OMISSION\tErdosProblems.test\t0\n'

class TransportTests(unittest.TestCase):
    def test_transport_path_reaches_clean_subprocess_environment(self):
        with patch.object(m.singleflight, 'command_environment', return_value={'PATH': '/safe/bin'}), \
             patch.object(m.subprocess, 'run') as child:
            m.run(['lean', 'export.lean'], dependency_export_path=Path('/tmp/exact.tsv'))
        options = child.call_args.kwargs
        self.assertEqual(options['env']['AIW_LEAN_DEPENDENCY_TSV'], '/tmp/exact.tsv')
        self.assertTrue(options['env']['PATH'].endswith('/safe/bin'))
        self.assertNotIn('dependency_export_path', options)

    def test_success_matches_existing_parser_and_cleans_file(self):
        paths = []
        def run(*args, **kwargs):
            p = kwargs['dependency_export_path']; paths.append(p)
            p.write_text(DATA)
            return CompletedProcess(args, 0, 'unrelated diagnostic\n', '')
        with patch.object(m, 'run', run):
            self.assertEqual(m.export_environment(), m.parse_environment_output(DATA))
        self.assertFalse(paths[0].exists())

    def test_nonzero_does_not_parse_partial_file(self):
        def run(*args, **kwargs):
            kwargs['dependency_export_path'].write_text(DATA)
            return CompletedProcess(args, 1, '', 'failure\n')
        with patch.object(m, 'run', run), patch.object(m, 'parse_environment_output') as parser:
            with self.assertRaisesRegex(RuntimeError, 'exited 1'):
                m.export_environment()
            parser.assert_not_called()

    def test_missing_output_fails(self):
        with patch.object(m, 'run', return_value=CompletedProcess([], 0, DATA, '')):
            with self.assertRaisesRegex(RuntimeError, 'without its TSV file'):
                m.export_environment()

    def test_signal_preserves_exit_and_does_not_parse(self):
        with patch.object(m, 'run', return_value=CompletedProcess([], -15, '', '')), \
             patch.object(m, 'parse_environment_output') as parser:
            with self.assertRaises(SystemExit) as caught:
                m.export_environment()
            self.assertEqual(caught.exception.code, 143)
            parser.assert_not_called()

if __name__ == '__main__':
    unittest.main()
