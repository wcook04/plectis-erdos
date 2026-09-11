#!/usr/bin/env python3
"""Reading routes and source imports must survive publication changes."""
import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import build_problem_index as builder

class ProblemLibraryTests(unittest.TestCase):
    def test_papers_follow_identity_and_map_follows_source(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            files = {
                'lean/ErdosProblems/Erdos68/Main.lean': '/- import Bogus -/\nimport Shared.Base\n',
                'Shared/Base.lean': 'import Shared.Leaf\n',
                'Shared/Leaf.lean': 'def answer := 42\n',
                'paper/short.tex': 'short', 'short.pdf': 'pdf',
                'paper/long.tex': 'long', 'long.pdf': 'pdf',
            }
            for name, text in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            source = {'problems': [{'problem_id': 'erdos_68', 'erdos_number': 68,
                'directory': 'ErdosProblems/Erdos68', 'principal_module': 'ErdosProblems.Erdos68.Main'}]}
            paper = {'paper_id': 'fixed-id', 'title': 'Before', 'subject': 'Erdős #68',
                'form': 'Problem note', 'publication_state': 'active', 'local_source': 'paper/short.tex', 'local_pdf': 'short.pdf'}
            corpus = {'papers': [paper]}
            with patch.object(builder, 'ROOT', root):
                first = builder.problem_library(source, {}, corpus)['problems']['erdos_68']
                self.assertEqual(len(first['source_map']['nodes']), 3)
                self.assertEqual(len(first['source_map']['edges']), 2)
                changed = copy.deepcopy(corpus)
                changed['papers'][0]['title'] = 'After'
                changed['papers'].append({**paper, 'paper_id': 'long-id', 'form': 'Reasoning surface', 'local_source': 'paper/long.tex', 'local_pdf': 'long.pdf'})
                second = builder.problem_library(source, {}, changed)['problems']['erdos_68']
                self.assertEqual(first['papers'][0]['github'], second['papers'][0]['github'])
                self.assertEqual(second['paper_roles']['long'], ['long-id'])
                changed['papers'][1]['publication_state'] = 'retired'
                self.assertEqual(builder.problem_library(source, {}, changed)['problems']['erdos_68']['paper_roles']['long'], [])
                (root / 'Shared/Base.lean').write_text('def noImports := 1\n')
                third = builder.problem_library(source, {}, corpus)['problems']['erdos_68']
                self.assertEqual(len(third['source_map']['nodes']), 2)
                (root / 'short.pdf').unlink()
                with self.assertRaisesRegex(ValueError, 'missing or unsafe pdf'):
                    builder.problem_library(source, {}, corpus)

if __name__ == '__main__':
    unittest.main()
