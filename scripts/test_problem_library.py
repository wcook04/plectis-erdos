#!/usr/bin/env python3
"""Reading routes and source imports must survive publication changes."""
import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import build_problem_index as builder

class ProblemLibraryTests(unittest.TestCase):
    def test_card_regenerates_status_and_preserves_authored_surroundings(self):
        row = {"erdos_number": 68, "problem_id": "erdos_68", "question": "Exact question?",
               "claim_registration": {"programme_claim_id": "target", "programme_statement": "Old boundary."},
               "what_is_checked": ["A finite result."],
               "note": {"rendered_path": "paper/short.pdf", "source_path": "paper/short.tex"}}
        claims = {"external_verification_packet": {"boundary": "No implicit claim promotion."}}
        document = f"Authored preface\n{builder.CARD_BEGIN}\n{builder.CARD_END}\nAuthored conclusion\n"
        first = builder.update_programme_card(document, builder.render_programme_card({"problems": [row]}, claims))
        row["claim_registration"]["programme_statement"] = "New exact boundary."
        second = builder.update_programme_card(first, builder.render_programme_card({"problems": [row]}, claims))
        self.assertIn("New exact boundary.", second)
        self.assertNotIn("Old boundary.", second)
        self.assertTrue(second.startswith("Authored preface\n"))
        self.assertTrue(second.endswith("Authored conclusion\n"))
        self.assertEqual(second, builder.update_programme_card(second, builder.render_programme_card({"problems": [row]}, claims)))
        row["claim_registration"]["programme_claim_id"] = None
        with self.assertRaisesRegex(ValueError, "no registered programme boundary"):
            builder.render_programme_card({"problems": [row]}, claims)
        with self.assertRaisesRegex(ValueError, "one programme-card region"):
            builder.update_programme_card("missing region", "content")

    def test_registration_follows_claim_coordinates_not_library_names(self):
        modules = [{"path": "lean/ErdosProblems/Erdos68/Main.lean"}]
        claims = {"claims": [
            {"id": "target", "status": "open", "statement": "Exact target boundary.", "declarations": []},
            {"id": "matched", "declarations": [{"module": "ErdosProblems/Erdos68/Main.lean", "name": "a"}]},
            {"id": "elsewhere", "declarations": [{"module": "ErdosProblems/Erdos68/Other.lean", "name": "b"}]},
        ]}
        result = builder.claim_registration("target", modules, claims)
        self.assertEqual(result["registered_claim_ids"], ["matched"])
        self.assertEqual(result["programme_status"], "open")
        self.assertEqual(result["programme_statement"], "Exact target boundary.")
        claims["claims"].pop(1)
        self.assertEqual(builder.claim_registration("target", modules, claims)["state"], "programme_only")
        claims["claims"].pop(0)
        self.assertEqual(builder.claim_registration("target", modules, claims)["state"], "not_registered")
        self.assertEqual(builder.claim_registration("target", modules, None)["state"], "unknown")

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
