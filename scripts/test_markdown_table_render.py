#!/usr/bin/env python3
"""Tests for content-addressed exceptions in the Markdown layout gate."""
from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts import check_markdown_table_render as checker


class ExactCopyGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        self.exact = self.root / "corpus" / "exact.md"
        self.sanitized = self.root / "corpus" / "sanitized.md"
        self.exact.parent.mkdir(parents=True)
        self.exact.write_text("| h |\n|---|\n| exact |\n", encoding="utf-8")
        self.sanitized.write_text("| h |\n|---|\n| sanitized |\n", encoding="utf-8")
        self.manifest = self.root / "manifest.json"
        self._write_manifest()

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    @staticmethod
    def _digest(path: Path) -> str:
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def _write_manifest(self) -> None:
        self.manifest.write_text(
            json.dumps(
                {
                    "files": [
                        {
                            "public_path": "corpus/exact.md",
                            "published_sha256": self._digest(self.exact),
                            "relation": "exact_copy",
                        },
                        {
                            "public_path": "corpus/sanitized.md",
                            "published_sha256": self._digest(self.sanitized),
                            "relation": "source_faithful_public_sanitized_copy",
                        },
                    ]
                }
            ),
            encoding="utf-8",
        )

    def verified(self) -> set[str]:
        return checker.verified_exact_copy_paths(
            str(self.root), (str(self.manifest),)
        )

    def test_only_digest_matching_exact_copy_is_verified(self) -> None:
        self.assertEqual(self.verified(), {str(self.exact.resolve())})

    def test_changed_exact_copy_loses_exception(self) -> None:
        self.exact.write_text("changed\n", encoding="utf-8")
        self.assertEqual(self.verified(), set())

    def test_verified_exact_copy_overflow_is_report_only(self) -> None:
        result = {
            "path": str(self.exact),
            "overflow_px": 40,
        }
        checker.apply_gate_exemptions([result], self.verified())
        self.assertTrue(result["overflow_gate_exempt"])
        self.assertEqual(result["gate_exemption"], "manifest_verified_exact_copy")

    def test_non_exact_copy_overflow_remains_fatal(self) -> None:
        result = {
            "path": str(self.sanitized),
            "overflow_px": 40,
        }
        checker.apply_gate_exemptions([result], self.verified())
        self.assertFalse(result["overflow_gate_exempt"])


if __name__ == "__main__":
    unittest.main()
