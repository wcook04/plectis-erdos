#!/usr/bin/env python3
"""Archive editions must remain distinct from changing paper source and PDFs."""
from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "docs/papers"))
import build_publication_taxonomy as taxonomy
import check_publication_taxonomy as checker


class ArchiveVersionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.corpus = json.loads((ROOT / taxonomy.CORPUS_REL).read_text())
        cls.source = json.loads((ROOT / taxonomy.ARCHIVE_REL).read_text())
        cls.paper_id = "erdos-257-mersenne-support-subseries"
        cls.version = cls.source["papers"][cls.paper_id][0]
        cls.paper = next(p for p in cls.corpus["papers"] if p["paper_id"] == cls.paper_id)

    def test_archive_does_not_replace_current_citation_or_review(self):
        record = taxonomy._project_paper(self.paper, [self.version])
        self.assertEqual(record["peer_review_state"], "not_externally_reviewed")
        self.assertEqual(record["preferred_citation"], taxonomy._preferred_citation(self.paper))
        self.assertIsNone(record["doi"])
        self.assertEqual(record["doi_absence_reason"], taxonomy.ARCHIVED_DOI_ABSENCE_REASON)
        self.assertEqual(record["archived_versions"][0]["relation_to_current_manuscript"],
                         "different_source_or_pdf")
        self.assertEqual(checker._check_paper(record), [])

    def test_source_or_pdf_change_invalidates_same_edition_label(self):
        paper = {**self.paper, "source_sha256": self.version["source_sha256"],
                 "pdf_sha256": self.version["pdf_sha256"]}
        self.assertEqual(taxonomy.archive_relation(paper, self.version), "same_source_and_pdf")
        for key in ("source_sha256", "pdf_sha256"):
            with self.subTest(key=key):
                changed = {**paper, key: "sha256:" + "0" * 64}
                record = taxonomy._project_paper(changed, [self.version])
                record["archived_versions"][0]["relation_to_current_manuscript"] = "same_source_and_pdf"
                self.assertTrue(any("relation disagrees" in error for error in checker._check_paper(record)))

    def test_float_version_bad_pin_and_review_promotion_are_rejected(self):
        for key, value in (("pdf_url", "https://aixiv.online/pdf/2609.02921"),
                           ("source_commit", "main"), ("source_sha256", "unknown"),
                           ("peer_review_state", "peer_reviewed")):
            with self.subTest(key=key):
                version = {**self.version, key: value}
                self.assertTrue(taxonomy.archive_version_errors(version))

    def test_unknown_paper_and_duplicate_version_are_rejected(self):
        for mode in ("unknown", "duplicate"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as directory:
                source = copy.deepcopy(self.source)
                if mode == "unknown":
                    source["papers"]["invented-paper"] = [self.version]
                else:
                    source["papers"][self.paper_id].append(self.version)
                path = Path(directory) / taxonomy.ARCHIVE_REL
                path.parent.mkdir(parents=True)
                path.write_text(json.dumps(source))
                with self.assertRaises(taxonomy.TaxonomyError):
                    taxonomy.build(self.corpus, Path(directory))

    def test_projection_is_idempotent(self):
        result = taxonomy.build(self.corpus, ROOT)
        self.assertEqual(taxonomy.build(result, ROOT), result)
        self.assertEqual(checker._check_summary(result, result["papers"]), [])


if __name__ == "__main__":
    unittest.main()
