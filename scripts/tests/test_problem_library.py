#!/usr/bin/env python3
"""Reading routes and source imports must survive publication changes."""

import _test_bootstrap  # noqa: F401
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import build_problem_index as builder

class ProblemLibraryTests(unittest.TestCase):
    def test_question_inventory_has_one_reader_owner(self):
        row = {"erdos_number": 68, "question": "Before | correction?",
               "note": {"rendered_path": "paper/before.pdf"}}
        body = f"Authored context\n{builder.CARD_BEGIN}\n{builder.CARD_END}\nAuthored proof\n"
        old = builder.update_programme_card(body, builder.render_problem_questions({"problems": [row]}))
        row["question"] = "Corrected question?"
        row["note"]["rendered_path"] = "paper/current.pdf"
        current = builder.update_programme_card(old, builder.render_problem_questions({"problems": [row]}))
        self.assertNotIn("Before", current)
        self.assertNotIn("before.pdf", current)
        self.assertIn("../paper/current.pdf", current)
        self.assertTrue(current.endswith("Authored proof\n"))
        payload = builder.build(
            json.loads(builder.SOURCE.read_text()),
            {row["id"]: row for row in json.loads(builder.CONTRACT.read_text())["artifacts"]},
            json.loads(builder.CLAIMS.read_text()),
            json.loads(builder.CORPUS.read_text()),
        )
        for path in (builder.READING_GUIDE,):
            card = builder.render_problem_questions(payload, prose=path == builder.READING_GUIDE)
            self.assertEqual(path.read_text(), builder.update_programme_card(path.read_text(), card))

    def test_agent_menu_routes_status_to_owner_and_preserves_authored_surroundings(self):
        row = {"erdos_number": 68, "problem_id": "erdos_68", "question": "Exact question?",
               "claim_registration": {"programme_claim_id": "target", "programme_statement": "Old boundary."},
               "what_is_checked": ["A finite result."],
               "note": {"rendered_path": "paper/short.pdf", "source_path": "paper/short.tex"}}
        claims = {"external_verification_packet": {"boundary": "No implicit claim promotion."}}
        document = f"Authored preface\n{builder.CARD_BEGIN}\n{builder.CARD_END}\nAuthored conclusion\n"
        first = builder.update_programme_card(document, builder.render_programme_card({"problems": [row]}, claims))
        row["claim_registration"]["programme_statement"] = "New exact boundary."
        second = builder.update_programme_card(first, builder.render_programme_card({"problems": [row]}, claims))
        self.assertNotIn("New exact boundary.", second)
        self.assertNotIn("Old boundary.", second)
        self.assertNotIn("A finite result.", second)
        self.assertIn("../RESULTS.md#result-68", second)
        self.assertIn("../research-commons/CONTRIBUTE_BY_PAPER.md#problem-68", second)
        self.assertIn("python3 scripts/query_corpus.py --route erdos_68", second)
        self.assertIn("supplies no new claim status", second)
        self.assertEqual(first, second)
        row["erdos_number"], row["problem_id"] = 1049, "erdos_1049"
        moved = builder.update_programme_card(second, builder.render_programme_card({"problems": [row]}, claims))
        self.assertIn("../RESULTS.md#result-1049", moved)
        self.assertIn("--route erdos_1049", moved)
        self.assertNotIn("result-68", moved)
        self.assertTrue(second.startswith("Authored preface\n"))
        self.assertTrue(second.endswith("Authored conclusion\n"))
        self.assertEqual(moved, builder.update_programme_card(moved, builder.render_programme_card({"problems": [row]}, claims)))
        row["claim_registration"]["programme_claim_id"] = None
        with self.assertRaisesRegex(ValueError, "no registered programme boundary"):
            builder.render_programme_card({"problems": [row]}, claims)
        with self.assertRaisesRegex(ValueError, "one programme-card region"):
            builder.update_programme_card("missing region", "content")

    def test_problem_statuses_come_from_the_claim_record_and_vocabulary(self):
        source = json.loads(builder.SOURCE.read_text())
        payload = builder.build(
            source,
            {row["id"]: row for row in json.loads(builder.CONTRACT.read_text())["artifacts"]},
            json.loads(builder.CLAIMS.read_text()),
            json.loads(builder.CORPUS.read_text()),
        )
        statuses = {row["erdos_number"]: row["status"] for row in payload["problems"]}
        self.assertTrue(set(statuses.values()) <= set(source["status_vocabulary"]))
        self.assertEqual(statuses.pop(1041), "formal statement refuted")
        self.assertEqual(set(statuses.values()), {"open"})

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
