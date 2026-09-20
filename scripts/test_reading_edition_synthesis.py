#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep the original synthesis pair while admitting standalone theorem notes."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build_reading_edition as edition


class SynthesisReadingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.corpus = self.root / "corpus.json"
        self.rows = [
            self.row(edition.SYNTHESIS_NOTE_ID, "synthesis_paper"),
            self.row(edition.SYNTHESIS_RECORD_ID, "reasoning_surface"),
        ]

    def row(self, paper_id, publication_class):
        path = self.root / f"{paper_id}.md"
        path.write_text(f"# {paper_id}\n\nA mathematical statement.\n")
        return {
            "paper_id": paper_id,
            "publication_class": publication_class,
            "subject_kind": "synthesis",
            "publication_state": "pending_source_publication",
            "local_full_text": path.name,
            "local_pdf": f"paper/synthesis/{paper_id}.pdf",
            "title": paper_id,
            "question_this_paper_answers": "Which values occur?",
        }

    def load(self, rows):
        self.corpus.write_text(json.dumps({"papers": rows}))
        with patch.object(edition, "ROOT", self.root), patch.object(edition, "CORPUS", self.corpus):
            return edition.synthesis_papers()

    def test_original_pair_remains_in_order(self):
        rows = self.load(list(reversed(self.rows)))
        self.assertEqual([r["paper_id"] for r in rows], [r["paper_id"] for r in self.rows])

    def test_standalone_note_needs_no_fabricated_record(self):
        extra = self.row("factorial-gap-theorem", "synthesis_paper")
        rows = self.load([extra, *reversed(self.rows)])
        self.assertEqual([r["paper_id"] for r in rows],
                         [edition.SYNTHESIS_NOTE_ID, edition.SYNTHESIS_RECORD_ID, extra["paper_id"]])
        # Entry selection must identify the original pair, not use list order.
        rendered = edition.synthesis_entry(list(reversed(rows)))
        self.assertIn(f"Working record: [{edition.SYNTHESIS_RECORD_ID}]", rendered)
        self.assertIn("Further standalone synthesis notes", rendered)
        self.assertIn(f"[{extra['title']}]", rendered)

    def test_original_record_is_still_required(self):
        extra = self.row("factorial-gap-theorem", "synthesis_paper")
        with self.assertRaisesRegex(edition.ReadingEditionError, "missing original synthesis"):
            self.load([self.rows[0], extra])

    def test_unpaired_extra_record_is_not_silently_assigned(self):
        extra = self.row("unrelated-record", "reasoning_surface")
        with self.assertRaisesRegex(edition.ReadingEditionError, "standalone synthesis notes"):
            self.load([*self.rows, extra])


if __name__ == "__main__":
    unittest.main()
