#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the source-attribution re-anchor tool on temporary Git repositories."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().with_name("reanchor_source_attributions.py")
REGISTRY = "docs/research-commons/source-attributions.json"
PAPER = "paper/fixture/test.tex"
NOTES = "docs/primary-sources/fixture/alpha-source-closure.md"
LEAN = "lean/Fixture/Test.lean"
ENVIRONMENT = {
    **os.environ,
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_AUTHOR_NAME": "Fixture",
    "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
    "GIT_COMMITTER_NAME": "Fixture",
    "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
}
PAPER_LINES = [
    "\\section{Introduction}",
    "Opening sentence of the fixture paper.",
    "The bound follows from \\cite[Thm.~2]{alpha,beta} in general.",
    *(f"Filler line {number}." for number in range(4, 18)),
    "\\begin{thebibliography}{9}",
    "\\bibitem{alpha} A. Author, \\emph{Alpha}.",
    "Journal of Alpha 1 (2001).",
    "\\bibitem{gamma} G. Author, \\emph{Gamma}.",
    "Journal of Gamma 3 (2003).",
    "\\end{thebibliography}",
]
BETA_ITEM = ["\\bibitem{beta} B. Author, \\emph{Beta}.", "Journal of Beta 2 (2002)."]
REFLOWED_CITATION = ["The bound, in a sharper form due to the authors,", "follows from \\cite[Thm.~2]{beta, alpha} in general."]
NOTE_LINES = ["# Alpha source closure", "Theorem 2 of Alpha is stated on page 5.", "The remaining text is context."]
LEAN_LINES = ["import Mathlib", "/-", "Following Alpha, Theorem 2.", "-/", "theorem fixture : True := trivial"]


def digest(lines: list[str], start: int, end: int) -> str:
    return "sha256:" + hashlib.sha256(("\n".join(lines[start - 1:end]) + "\n").encode()).hexdigest()


def fixture_registry() -> dict:
    return {
        "schema": "research-source-attributions/1",
        "scope": {"statement": "fixture"},
        "sources": [
            {
                "id": "alpha",
                "kind": "literature",
                "title": "Alpha",
                "authors": ["A. Author"],
                "source_locators": [{
                    "url": "https://example.org/alpha", "locator": "Theorem 2", "evidence_path": NOTES,
                    "line_start": 2, "line_end": 2, "excerpt_sha256": digest(NOTE_LINES, 2, 2),
                }],
                "artifact_links": [
                    {"path": PAPER, "line_start": 3, "line_end": 3, "excerpt_sha256": digest(PAPER_LINES, 3, 3)},
                    {"path": PAPER, "line_start": 19, "line_end": 21, "expected_text": "\\bibitem{alpha}",
                     "excerpt_sha256": digest(PAPER_LINES, 19, 21)},
                ],
                "relation": "Fixture citation.",
                "verification_state": "source_verified",
            },
            {
                "id": "gamma",
                "kind": "literature",
                "title": "Gamma",
                "authors": ["G. Author"],
                "source_locators": [{"url": "https://example.org/gamma", "locator": "Lemma 1"}],
                "artifact_links": [
                    {"path": PAPER, "line_start": 21, "line_end": 23, "expected_text": "\\bibitem{gamma}",
                     "excerpt_sha256": digest(PAPER_LINES, 21, 23)},
                ],
                "relation": "Fixture citation.",
                "verification_state": "bibliography_only",
            },
        ],
        "lean_reviews": [{
            "path": LEAN, "line_start": 3, "line_end": 3, "excerpt_sha256": digest(LEAN_LINES, 3, 3),
            "context": {"line_start": 2, "line_end": 4, "excerpt_sha256": digest(LEAN_LINES, 2, 4)},
            "disposition": "reviewed_citation_or_comparison", "source_ids": ["alpha"], "reason": "Fixture review.",
        }],
    }


class ReanchorSourceAttributionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="reanchor-fixture-"))
        self.addCleanup(shutil.rmtree, self.root, True)
        self.git("init", "-q")
        self.write(PAPER, PAPER_LINES)
        self.write(NOTES, NOTE_LINES)
        self.write(LEAN, LEAN_LINES)
        self.save_registry(fixture_registry())
        self.commit()

    def git(self, *args: str) -> None:
        subprocess.run(["git", *args], cwd=self.root, env=ENVIRONMENT, check=True, capture_output=True)

    def commit(self) -> None:
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "fixture")

    def write(self, relative: str, lines: list[str]) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def lines(self, relative: str) -> list[str]:
        return (self.root / relative).read_text(encoding="utf-8").splitlines()

    def save_registry(self, data: dict) -> None:
        path = self.root / REGISTRY
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    def registry(self) -> dict:
        return json.loads((self.root / REGISTRY).read_text(encoding="utf-8"))

    def registry_bytes(self) -> bytes:
        return (self.root / REGISTRY).read_bytes()

    @staticmethod
    def links(data: dict, source_id: str) -> list[dict]:
        return next(source for source in data["sources"] if source["id"] == source_id)["artifact_links"]

    def reanchor(self, *args: str, expect: int = 0) -> str:
        run = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.root), "--base", "HEAD", *args],
            cwd=self.root, env=ENVIRONMENT, capture_output=True, text=True, check=False,
        )
        self.assertEqual(run.returncode, expect, run.stdout + run.stderr)
        return run.stdout

    def assert_anchored(self, row: dict, relative: str) -> None:
        lines = self.lines(relative)
        self.assertEqual(row["excerpt_sha256"], digest(lines, row["line_start"], row["line_end"]))
        if "expected_text" in row:
            self.assertIn(row["expected_text"], "\n".join(lines[row["line_start"] - 1:row["line_end"]]))

    def test_lines_inserted_above_bibitems_move_spans_with_unchanged_digests(self) -> None:
        before = self.registry()
        self.write(PAPER, PAPER_LINES[:17] + ["Inserted line one.", "Inserted line two."] + PAPER_LINES[17:])
        output = self.reanchor("--write")
        after = self.registry()
        for source_id, index in (("alpha", 1), ("gamma", 0)):
            old, new = self.links(before, source_id)[index], self.links(after, source_id)[index]
            self.assertEqual((new["line_start"], new["line_end"]), (old["line_start"] + 2, old["line_end"] + 2))
            self.assertEqual(new["excerpt_sha256"], old["excerpt_sha256"])
            self.assert_anchored(new, PAPER)
        self.assertEqual(self.links(after, "alpha")[0], self.links(before, "alpha")[0])
        self.assertIn("moved 2, recomputed 0, unresolved 0", output)

    def test_edited_bibitem_body_recomputes_digest_and_keeps_expected_text(self) -> None:
        before = self.registry()
        lines = list(PAPER_LINES)
        lines[19] = "Journal of Alpha 1 (2001), second edition."
        self.write(PAPER, lines)
        output = self.reanchor("--write")
        after = self.registry()
        old, new = self.links(before, "alpha")[1], self.links(after, "alpha")[1]
        self.assertEqual((new["line_start"], new["line_end"]), (19, 21))
        self.assertNotEqual(new["excerpt_sha256"], old["excerpt_sha256"])
        self.assertEqual(new["expected_text"], old["expected_text"])
        self.assert_anchored(new, PAPER)
        self.assertIn("[bibitem]", output)
        self.assertEqual(self.links(after, "gamma"), self.links(before, "gamma"))

    def test_new_bibitem_between_anchored_spans_ends_earlier_span_on_the_new_item(self) -> None:
        before = self.registry()
        self.write(PAPER, PAPER_LINES[:20] + BETA_ITEM + PAPER_LINES[20:])
        output = self.reanchor("--write")
        after = self.registry()
        alpha = self.links(after, "alpha")[1]
        self.assertEqual((alpha["line_start"], alpha["line_end"]), (19, 21))
        self.assertEqual(self.lines(PAPER)[alpha["line_end"] - 1], BETA_ITEM[0])
        self.assertNotEqual(alpha["excerpt_sha256"], self.links(before, "alpha")[1]["excerpt_sha256"])
        self.assert_anchored(alpha, PAPER)
        gamma, old_gamma = self.links(after, "gamma")[0], self.links(before, "gamma")[0]
        self.assertEqual((gamma["line_start"], gamma["line_end"]), (23, 25))
        self.assertEqual(gamma["excerpt_sha256"], old_gamma["excerpt_sha256"])
        self.assertIn("[bibitem]", output)

    def test_edited_citation_line_is_repointed_at_the_line_carrying_its_keys(self) -> None:
        lines = list(PAPER_LINES)
        lines[2:3] = REFLOWED_CITATION
        self.write(PAPER, lines)
        output = self.reanchor("--write")
        cite = self.links(self.registry(), "alpha")[0]
        self.assertEqual((cite["line_start"], cite["line_end"]), (4, 4))
        self.assert_anchored(cite, PAPER)
        self.assert_anchored(self.links(self.registry(), "alpha")[1], PAPER)
        self.assertIn("[cite]", output)

    def test_rerun_after_write_is_a_no_op(self) -> None:
        lines = PAPER_LINES[:20] + BETA_ITEM + PAPER_LINES[20:]
        lines[2:3] = REFLOWED_CITATION
        self.write(PAPER, lines)
        self.reanchor("--write")
        written = self.registry_bytes()
        output = self.reanchor("--write")
        self.assertEqual(self.registry_bytes(), written)
        self.assertIn("moved 0, recomputed 0, unresolved 0; registry unchanged", output)

    def test_second_edit_after_a_write_is_mapped_from_the_base_registry_row(self) -> None:
        lines = list(PAPER_LINES)
        lines[2:3] = REFLOWED_CITATION
        self.write(PAPER, lines)
        self.reanchor("--write")
        lines = ["% first inserted line", "% second inserted line"] + lines
        lines[5] = "follows from \\cite[Thm.~2]{beta, alpha} in full generality."
        self.write(PAPER, lines)
        self.reanchor("--write")
        data = self.registry()
        cite = self.links(data, "alpha")[0]
        self.assertEqual((cite["line_start"], cite["line_end"]), (6, 6))
        self.assert_anchored(cite, PAPER)
        for source_id, index in (("alpha", 1), ("gamma", 0)):
            self.assert_anchored(self.links(data, source_id)[index], PAPER)

    def test_lean_review_and_its_context_move_with_unchanged_digests(self) -> None:
        before = self.registry()["lean_reviews"][0]
        self.write(LEAN, LEAN_LINES[:1] + ["", "-- A helper comment inserted above the review."] + LEAN_LINES[1:])
        output = self.reanchor("--write")
        review = self.registry()["lean_reviews"][0]
        self.assertEqual((review["line_start"], review["line_end"]), (5, 5))
        self.assertEqual((review["context"]["line_start"], review["context"]["line_end"]), (4, 6))
        self.assertEqual(review["excerpt_sha256"], before["excerpt_sha256"])
        self.assertEqual(review["context"]["excerpt_sha256"], before["context"]["excerpt_sha256"])
        self.assert_anchored(review, LEAN)
        self.assert_anchored(review["context"], LEAN)
        self.assertIn("moved 2, recomputed 0, unresolved 0", output)

    def test_edited_reviewed_lean_comment_is_unresolved(self) -> None:
        lines = list(LEAN_LINES)
        lines[2] = "Following Alpha, Theorem 3."
        self.write(LEAN, lines)
        before = self.registry_bytes()
        output = self.reanchor("--write", expect=1)
        self.assertIn("re-read it and restamp the review", output)
        self.assertEqual(self.registry_bytes(), before)

    def test_rows_in_untouched_files_are_left_alone(self) -> None:
        before = self.registry()
        clean = self.reanchor("--write")
        self.assertIn("current 6, moved 0, recomputed 0, unresolved 0; registry unchanged", clean)
        self.write(PAPER, ["% an inserted comment line"] + PAPER_LINES)
        self.reanchor("--write")
        after = self.registry()
        self.assertEqual(after["lean_reviews"], before["lean_reviews"])
        self.assertEqual(after["sources"][0]["source_locators"], before["sources"][0]["source_locators"])
        self.assertNotEqual(after["sources"][0]["artifact_links"], before["sources"][0]["artifact_links"])

    def test_unresolvable_citation_anchor_exits_one_and_writes_nothing(self) -> None:
        lines = list(PAPER_LINES)
        lines[2] = "The bound follows from the literature in general."
        self.write(PAPER, lines)
        before = self.registry_bytes()
        output = self.reanchor("--write", expect=1)
        self.assertIn("UNRESOLVED alpha.artifact_links[0]", output)
        self.assertIn("cites alpha, beta", output)
        self.assertEqual(self.registry_bytes(), before)

    def test_edited_prose_with_expected_text_is_refound_and_fails_when_gone(self) -> None:
        data = self.registry()
        self.links(data, "gamma").append({
            "path": PAPER, "line_start": 2, "line_end": 2, "expected_text": "fixture paper",
            "excerpt_sha256": digest(PAPER_LINES, 2, 2),
        })
        self.save_registry(data)
        self.commit()
        base_registry = self.registry_bytes()
        lines = list(PAPER_LINES)
        lines[1:2] = ["A new first remark.", "Opening sentence, now longer, of the fixture paper."]
        self.write(PAPER, lines)
        output = self.reanchor("--write")
        row = self.links(self.registry(), "gamma")[1]
        self.assertEqual((row["line_start"], row["line_end"]), (3, 3))
        self.assert_anchored(row, PAPER)
        self.assertIn("[expected]", output)
        (self.root / REGISTRY).write_bytes(base_registry)
        lines[2] = "Opening sentence, now longer, of the document."
        self.write(PAPER, lines)
        output = self.reanchor("--write", expect=1)
        self.assertIn("expected_text is gone", output)
        self.assertEqual(self.registry_bytes(), base_registry)

    def test_write_refuses_a_registry_that_does_not_round_trip(self) -> None:
        (self.root / REGISTRY).write_text(json.dumps(self.registry(), indent=4) + "\n", encoding="utf-8")
        before = self.registry_bytes()
        self.write(PAPER, ["% an inserted comment line"] + PAPER_LINES)
        self.reanchor("--write", expect=2)
        self.assertEqual(self.registry_bytes(), before)

    def test_patch_resolves_find_links_to_exact_bibitem_spans(self) -> None:
        self.write(PAPER, PAPER_LINES[:20] + BETA_ITEM + PAPER_LINES[20:])
        patch = self.root / "patch.json"
        patch.write_text(json.dumps([{
            "id": "beta", "kind": "literature", "title": "Beta", "authors": ["B. Author"],
            "relation": "Fixture citation.", "verification_state": "bibliography_only",
            "artifact_links": [{"path": PAPER, "find": "\\bibitem{beta}", "span": "bibitem", "expected_text": "\\bibitem{beta}"}],
        }]), encoding="utf-8")
        output = self.reanchor("--write", "--patch", str(patch))
        beta = self.links(self.registry(), "beta")[0]
        self.assertEqual((beta["line_start"], beta["line_end"]), (21, 23))
        self.assert_anchored(beta, PAPER)
        self.assertIn("added beta with 1 artifact links", output)


if __name__ == "__main__":
    unittest.main()
