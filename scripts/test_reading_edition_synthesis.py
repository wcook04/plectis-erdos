#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep one complete cross-problem paper in every reading edition."""

import json
from pathlib import Path
import tempfile
import unittest
from contextlib import ExitStack
from unittest.mock import patch

import build_reading_edition as edition


class SynthesisReadingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.corpus = self.root / "corpus.json"
        self.rows = [
            self.row(edition.SYNTHESIS_PAPER_ID, "synthesis_paper"),
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

    def test_one_paper_contains_the_complete_record(self):
        rows = self.load(self.rows)
        self.assertEqual([r["paper_id"] for r in rows], [edition.SYNTHESIS_PAPER_ID])
        rendered = edition.synthesis_entry(rows)
        self.assertIn("A mathematical statement.", rendered)
        self.assertNotIn("Working record:", rendered)

    def test_second_synthesis_is_rejected(self):
        extra = self.row("duplicate-record", "reasoning_surface")
        with self.assertRaisesRegex(edition.ReadingEditionError, "exactly one"):
            self.load([*self.rows, extra])

    def test_missing_or_wrong_canonical_paper_is_rejected(self):
        for rows in ([], [self.row("other-paper", "synthesis_paper")]):
            with self.subTest(rows=rows), self.assertRaisesRegex(edition.ReadingEditionError, "exactly one"):
                self.load(rows)

    def test_retired_predecessor_is_not_reintroduced(self):
        retired = self.row("old-record", "reasoning_surface")
        retired["publication_state"] = "retired"
        self.assertEqual(len(self.load([retired, *self.rows])), 1)


class ReadingLinkTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.text_dir = self.root / "docs/papers/full-text"
        self.text_dir.mkdir(parents=True)

    def test_relocated_links_preserve_fragments_queries_and_external_urls(self):
        original = (
            "[PDF](../../../paper/257/a%20record.pdf?raw=1#nameddest=section.3) "
            "[section](#sec:result) [web](https://example.org/paper.pdf) "
            "[mail](mailto:reader@example.org) [cdn](//example.org/paper.pdf)"
        )
        with patch.object(edition, "ROOT", self.root):
            rendered = edition.public_links(original, self.text_dir / "paper.md")
        self.assertIn(f"]({edition.BLOB}paper/257/a%20record.pdf?raw=1#nameddest=section.3)", rendered)
        for link in ("#sec:result", "https://example.org/paper.pdf",
                     "mailto:reader@example.org", "//example.org/paper.pdf"):
            self.assertIn(f"]({link})", rendered)

    def test_link_cannot_escape_the_public_repository(self):
        with patch.object(edition, "ROOT", self.root):
            with self.assertRaisesRegex(edition.ReadingEditionError, "outside the repository"):
                edition.public_links("[bad](../../../../private.pdf)", self.text_dir / "paper.md")

    def test_math_and_code_are_not_reinterpreted_as_links(self):
        for literal in (
            "$`b_k=[z^k](z;q)_infty`$", "$b_k=[z^k](z;q)_infty$",
            "$$b_k=[z^k](z;q)_infty$$", "`[example](local.md)`",
            "```math\nb_k=[z^k](z;q)_infty\n```",
            "~~~text\n[example](local.md)\n~~~",
        ):
            with self.subTest(literal=literal), patch.object(edition, "ROOT", self.root):
                rendered = edition.public_links(literal, self.text_dir / "paper.md")
            self.assertEqual(rendered, literal)
        with patch.object(edition, "ROOT", self.root):
            self.assertEqual(
                edition.public_links("[a `code` label](../../../paper/note.pdf)", self.text_dir / "paper.md"),
                f"[a `code` label]({edition.BLOB}paper/note.pdf)",
            )

    def test_all_editions_rebase_paper_links_and_scope_repeated_anchors(self):
        def row(paper_id, publication_class, problem=None):
            path = self.text_dir / f"{paper_id}.md"
            path.write_text(
                f'# {paper_id}\n\n<a id="sec:result"></a>\n'
                '[result](#sec:result) [PDF](../../../paper/257/record.pdf#nameddest=section.3)\n'
            )
            result = {
                "paper_id": paper_id, "publication_class": publication_class,
                "title": paper_id, "question_this_paper_answers": "Which values occur?",
                "local_full_text": path.relative_to(self.root).as_posix(),
                "local_pdf": "paper/257/record.pdf", "text_path": path,
            }
            if problem is not None:
                result["problem"] = problem
            return result

        papers = [row("short257", "problem_paper", 257),
                  row("long257", "reasoning_surface", 257)]
        synthesis = [row(edition.SYNTHESIS_PAPER_ID, "synthesis_paper")]
        out = self.root / "docs/reading-edition"
        out.mkdir()
        intro = out / "INTRODUCTION.md"
        intro.write_text("Read the mathematics.\n")
        complete_path = self.root / "downloaded-edition.md"
        with ExitStack() as stack:
            for name, value in (("ROOT", self.root), ("OUT", out),
                                ("INTRODUCTION", intro), ("WORKED_EXAMPLES", ())):
                stack.enter_context(patch.object(edition, name, value))
            stack.enter_context(patch.object(edition, "mathematical_papers", return_value=papers))
            stack.enter_context(patch.object(edition, "synthesis_papers", return_value=synthesis))
            stack.enter_context(patch.object(edition, "shared_instruction", return_value="Explore."))
            stack.enter_context(patch.object(edition, "fingerprint", return_value="fixture"))
            outputs = edition.build()
            edition.complete(complete_path)
        for text in (outputs[out / "plectis-reading-edition.md"],
                     outputs[out / "plectis-short-papers.md"], complete_path.read_text()):
            self.assertNotIn("](../../../", text)
            self.assertIn(f"]({edition.BLOB}paper/257/record.pdf#nameddest=section.3)", text)
            self.assertNotIn('id="sec:result"', text)
            self.assertIn('id="short257--sec:result"', text)
            self.assertIn("](#short257--sec:result)", text)


if __name__ == "__main__":
    unittest.main()
