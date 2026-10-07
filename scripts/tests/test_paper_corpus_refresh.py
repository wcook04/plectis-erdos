#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Paper-index refresh must be independent of manuscript conversion."""
from __future__ import annotations

import _test_bootstrap  # noqa: F401

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts/papers"))
import refresh_paper_corpus as owner
import refresh_projections


class PaperIndexRefreshTests(unittest.TestCase):
    def test_index_missing_stale_current_and_write_preserve_corpus(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            papers = root / "docs/papers"
            papers.mkdir(parents=True)
            record = {"paper_id": "one", "title": "One"}
            data = {"this_repository": "fixture", "papers": [record, {"paper_id": "untitled"}]}
            corpus = papers / "corpus.json"
            corpus.write_text(json.dumps(data))
            before = corpus.read_bytes()
            index = papers / "README.md"
            with patch.object(owner.renderer, "_convert", side_effect=AssertionError("conversion forbidden")), \
                 patch.object(owner.taxonomy, "build", side_effect=AssertionError("corpus mutation forbidden")), \
                 patch.object(owner.renderer, "_readme", return_value="# Current index\n") as render:
                self.assertEqual(owner.refresh(root, write=False, index_only=True)["status"], "stale")
                self.assertFalse(index.exists())
                index.write_text("old")
                self.assertEqual(owner.refresh(root, write=False, index_only=True)["changed"], ["docs/papers/README.md"])
                self.assertEqual(index.read_text(), "old")
                owner.refresh(root, write=True, index_only=True)
                self.assertEqual(index.read_text(), "# Current index\n")
                self.assertEqual(owner.refresh(root, write=False, index_only=True)["status"], "current")
                render.assert_called_with([record], "fixture", root)
            self.assertEqual(corpus.read_bytes(), before)
            self.assertEqual(sorted(p.name for p in papers.iterdir()), ["README.md", "corpus.json"])

    def test_compact_index_retains_every_paper_and_reading_route(self):
        root = Path(__file__).resolve().parents[2]
        data = json.loads((root / "docs/papers/corpus.json").read_text())
        records = [r for r in data["papers"] if r.get("title")]
        text = owner.renderer._readme(records, data["this_repository"], root)
        self.assertIn("../../paper/README.md", text)
        self.assertIn("../RESULTS.md", text)
        self.assertNotIn("### Ranked frontier", text)
        self.assertLess(len(text.split()), 4000)
        for record in records:
            self.assertIn("`" + record["paper_id"] + "`", text)
            self.assertIn(owner.renderer._relative_to_corpus(record["local_full_text"]), text)
            self.assertIn(owner.renderer._relative_to_corpus(record["local_source"]), text)
            if record.get("local_pdf"):
                self.assertIn(owner.renderer._relative_to_corpus(record["local_pdf"]), text)
            for entry in record.get("first_pass", {}).get("sections", []):
                self.assertIn(owner.renderer._section_link(record, entry), text)
        self.assertIn("not_authority_for", text)
        self.assertIn(owner.renderer.AUTHORITY_ORDER, text)

    def test_full_refresh_still_converts_native_manuscript(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            papers = root / "docs/papers"
            papers.mkdir(parents=True)
            source = root / "paper/one.tex"
            source.parent.mkdir()
            source.write_text("manuscript")
            record = {"paper_id": "one", "title": "Old", "relation_to_this_repository": "native",
                      "local_source": "paper/one.tex", "local_full_text": "docs/papers/full-text/one.md"}
            (papers / "corpus.json").write_text(json.dumps({"this_repository": "fixture", "papers": [record]}))
            converted = {"title": "New", "markdown": "Converted", "sections": [], "citations_rendered": 0}
            with patch.object(owner.renderer, "_convert", return_value=converted) as convert, \
                 patch.object(owner.renderer, "_readme", return_value="Index"), \
                 patch.object(owner.taxonomy, "build", side_effect=lambda corpus, root: corpus):
                owner.refresh(root, write=True)
                convert.assert_called_once_with(source, "one")
            self.assertEqual((papers / "full-text/one.md").read_text(), "Converted")
            self.assertEqual(json.loads((papers / "corpus.json").read_text())["papers"][0]["title"], "New")

    def test_pipeline_registers_lightweight_writer_and_checker_after_taxonomy(self):
        builder = "scripts/papers/refresh_paper_corpus.py"
        self.assertEqual(refresh_projections.BUILDERS.index(builder),
                         refresh_projections.BUILDERS.index("scripts/papers/build_publication_taxonomy.py") + 1)
        self.assertEqual(refresh_projections.WRITE_FLAGS[builder], ("--index-only", "--write"))
        self.assertEqual(refresh_projections.PREFLIGHT_CHECKS[builder], ("--index-only", "--check"))


if __name__ == "__main__":
    unittest.main()
