#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise the paper-to-skill release boundary with an independent small corpus."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import sync_writing_skill as owner

SCRIPT = Path(__file__).with_name("sync_writing_skill.py")
GUIDE = "writing-a-good-mathematical-paper"
COMPANION = "writing-mathematics-from-reviewed-revisions"
SKILL = "skills/public-mathematical-writing/SKILL.md"
MANIFEST = "docs/papers/exposition-method/version.json"
CORPUS = "docs/papers/corpus.json"
REFERENCES = (
    "skills/public-mathematical-writing/references/writing-guide.md",
    "skills/public-mathematical-writing/references/worked-companion.md",
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class WritingSkillSyncTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.files = {
            SKILL: ("skill", b"# Writing skill\n\nExplain the estimate's purpose.\n"),
            "docs/papers/exposition-method/README.md": ("guidance", b"Method records.\n"),
            f"paper/exposition/{GUIDE}.tex": ("compact_guide_source", b"Guide manuscript.\n"),
            f"paper/exposition/{GUIDE}.pdf": ("compact_guide_pdf", b"%PDF guide fixture\n"),
            f"paper/exposition/{COMPANION}.tex": ("companion_source", b"Companion manuscript.\n\\input{parts/lesson}\n"),
            f"paper/exposition/{COMPANION}.pdf": ("companion_pdf", b"%PDF companion fixture\n"),
            "paper/exposition/parts/lesson.tex": ("companion_input", b"A worked revision.\n"),
            "paper/paper-house-style.sty": ("shared_input", b"A shared style.\n"),
        }
        for relative, (_, data) in self.files.items():
            self.put(relative, data)
        self.put(f"docs/papers/full-text/{GUIDE}.md", b"# Guide\n\nExplain why the estimate is needed.\n")
        self.put(f"docs/papers/full-text/{COMPANION}.md", b"# Companion\n\nA complete worked revision.\n")
        self.rows = [self.paper(GUIDE), self.paper(COMPANION)]
        self.manifest = {
            "schema": "exposition-method-version/1", "version": "fixture",
            "required_roles": sorted({role for role, _ in self.files.values()}),
            "files": [{"path": relative, "role": role, "sha256": digest(data)}
                      for relative, (role, data) in self.files.items()],
        }
        self.reconcile()

    def put(self, relative, data):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def paper(self, paper_id):
        source = f"paper/exposition/{paper_id}.tex"
        pdf = f"paper/exposition/{paper_id}.pdf"
        full_text = f"docs/papers/full-text/{paper_id}.md"
        inputs = [source, "paper/paper-house-style.sty"]
        if paper_id == COMPANION:
            inputs.append("paper/exposition/parts/lesson.tex")
        inputs.extend(getattr(self, "extra_inputs", {}).get(paper_id, ()))
        # Known fixture inputs certify the receipt independently of the
        # production input-discovery helper used by the exporter and checker.
        input_record = "\n".join(
            f"{relative}=sha256:{digest((self.root / relative).read_bytes())}"
            for relative in sorted(inputs)
        ) + "\n"
        source_digest = "sha256:" + digest((self.root / source).read_bytes())
        pdf_digest = "sha256:" + digest((self.root / pdf).read_bytes())
        return {
            "paper_id": paper_id, "title": paper_id,
            "local_source": source, "source_sha256": source_digest,
            "local_pdf": pdf, "pdf_sha256": pdf_digest,
            "local_full_text": full_text,
            "full_text_sha256": "sha256:" + digest((self.root / full_text).read_bytes()),
            "full_text_source_sha256": source_digest,
            "full_text_pdf_sha256": pdf_digest,
            "full_text_inputs_sha256": "sha256:" + digest(input_record.encode()),
            "copyright": "Fixture Author", "licence": "CC-BY-4.0",
        }

    def save(self):
        self.put(MANIFEST, (json.dumps(self.manifest, indent=2) + "\n").encode())
        self.put(CORPUS, (json.dumps({"papers": self.rows}, indent=2) + "\n").encode())

    def refresh_bindings(self):
        for row in self.manifest["files"]:
            row["sha256"] = digest((self.root / row["path"]).read_bytes())
        self.rows = [self.paper(GUIDE), self.paper(COMPANION)]

    def reconcile(self, disposition="updated"):
        # This fixture implements the public digest format, without asking the
        # owner being tested to certify its own input or its review record.
        inputs = [{key: row[key] for key in ("path", "sha256", "role")}
                  for row in self.manifest["files"]
                  if row["role"] in ("compact_guide_source", "compact_guide_input",
                                     "companion_source", "companion_input")]
        inputs.sort(key=lambda row: (row["path"], row["role"], row["sha256"]))
        encoded = json.dumps(inputs, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
        self.manifest["paper_skill_review"] = {
            "paper_inputs_sha256": digest(encoded),
            "skill_sha256": digest((self.root / SKILL).read_bytes()),
            "disposition": disposition,
            "reason": "The current instructions cover the reviewed changes.",
        }
        self.save()

    def run_owner(self, mode, expected=0):
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.root), mode],
            capture_output=True, text=True, check=False, timeout=30,
        )
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def reference_bytes(self):
        return {(self.root / relative).name: (self.root / relative).read_bytes()
                for relative in REFERENCES if (self.root / relative).exists()}

    def revised_pair(self):
        for paper_id in (GUIDE, COMPANION):
            self.put(f"docs/papers/full-text/{paper_id}.md", f"# Revised {paper_id}\n".encode())
        self.refresh_bindings()
        self.reconcile()

    def test_preparation_failure_preserves_both_previous_references(self):
        self.run_owner("--write")
        before = self.reference_bytes()
        self.revised_pair()
        original_write = Path.write_bytes

        def failed_write(path, data):
            if path.name == "worked-companion.md.new":
                raise OSError("simulated full disk")
            return original_write(path, data)

        with patch.object(Path, "write_bytes", failed_write):
            with self.assertRaisesRegex(OSError, "simulated full disk"):
                owner.sync(self.root, write=True)
        self.assertEqual(self.reference_bytes(), before)
        self.assertFalse(list((self.root / REFERENCES[0]).parent.glob(".writing-skill-sync-*")))

    def test_second_promotion_failure_restores_the_previous_pair(self):
        self.run_owner("--write")
        before = self.reference_bytes()
        self.revised_pair()
        original_replace = owner.os.replace

        def failed_replace(source, destination):
            if Path(source).name == "worked-companion.md.new":
                raise OSError("simulated promotion failure")
            return original_replace(source, destination)

        with patch.object(owner.os, "replace", failed_replace):
            with self.assertRaisesRegex(OSError, "simulated promotion failure"):
                owner.sync(self.root, write=True)
        self.assertEqual(self.reference_bytes(), before)
        self.assertFalse(list((self.root / REFERENCES[0]).parent.glob(".writing-skill-sync-*")))

    def test_failed_initial_pair_install_removes_the_partial_reference(self):
        original_replace = owner.os.replace

        def failed_replace(source, destination):
            if Path(source).name == "worked-companion.md.new":
                raise OSError("simulated promotion failure")
            return original_replace(source, destination)

        with patch.object(owner.os, "replace", failed_replace):
            with self.assertRaises(OSError):
                owner.sync(self.root, write=True)
        self.assertEqual(self.reference_bytes(), {})

    def test_failed_restore_retains_and_identifies_recovery_files(self):
        self.run_owner("--write")
        before = self.reference_bytes()
        self.revised_pair()
        original_replace = owner.os.replace

        def failed_replace(source, destination):
            if Path(source).name in {"worked-companion.md.new", "writing-guide.md.old"}:
                raise OSError("simulated unavailable destination")
            return original_replace(source, destination)

        with patch.object(owner.os, "replace", failed_replace):
            with self.assertRaisesRegex(OSError, "recovery files retained at") as caught:
                owner.sync(self.root, write=True)
        backup = next((self.root / REFERENCES[0]).parent.glob(".writing-skill-sync-*"))
        self.assertIn(str(backup), str(caught.exception))
        for name, payload in before.items():
            self.assertEqual((backup / f"{name}.old").read_bytes(), payload)

    def test_successful_pair_refresh_preserves_unowned_references(self):
        self.run_owner("--write")
        self.revised_pair()
        extra = (self.root / REFERENCES[0]).parent / "user-notes.md"
        extra.write_bytes(b"user notes\n")
        self.run_owner("--write")
        self.run_owner("--check")
        self.assertEqual(extra.read_bytes(), b"user notes\n")

    def assert_refusal_preserves_outputs(self, message):
        before = self.reference_bytes()
        result = self.run_owner("--write", expected=2)
        self.assertIn(message, result.stderr)
        self.assertIn("Reconcile both writing papers", result.stderr)
        self.assertIn("refresh_paper_corpus.py --write", result.stderr)
        self.assertEqual(self.reference_bytes(), before)

    def test_initial_sync_and_check_preserve_entire_text_and_provenance(self):
        self.run_owner("--write")
        self.run_owner("--check")
        for paper_id, relative in zip((GUIDE, COMPANION), REFERENCES):
            result = (self.root / relative).read_bytes()
            original = (self.root / f"docs/papers/full-text/{paper_id}.md").read_bytes()
            self.assertTrue(result.endswith(original))
            # REUSE-IgnoreStart
            self.assertIn(b"SPDX-License-Identifier: CC-BY-4.0", result)
            self.assertIn(b"SPDX-FileCopyrightText: Fixture Author", result)
            # REUSE-IgnoreEnd
            self.assertIn(b"Generated by scripts/sync_writing_skill.py", result)
            self.assertIn(f"https://github.com/wcook04/plectis-erdos/blob/main/paper/exposition/{paper_id}.tex".encode(), result)
            self.assertIn(f"https://github.com/wcook04/plectis-erdos/blob/main/paper/exposition/{paper_id}.pdf".encode(), result)
            self.assertIn(f"Full-text SHA256: sha256:{digest(original)}".encode(), result)

    def test_paper_edit_without_current_manifest_writes_nothing(self):
        self.run_owner("--write")
        relative = f"paper/exposition/{GUIDE}.tex"
        self.put(relative, b"Changed mathematical guidance.\n")
        self.assert_refusal_preserves_outputs(f"stale file hash: {relative}")

    def test_current_bindings_cannot_bypass_stale_paper_review(self):
        self.run_owner("--write")
        self.put("paper/exposition/parts/lesson.tex", b"A new procedure for a revision.\n")
        self.refresh_bindings()
        self.save()
        self.assert_refusal_preserves_outputs("stale paper_skill_review.paper_inputs_sha256")

    def add_unlisted_inputs(self, paper_id, *, nested=False):
        source = f"paper/exposition/{paper_id}.tex"
        stem = f"new-guidance-{paper_id}"
        new_input = f"paper/exposition/parts/{stem}.tex"
        self.put(source, (self.root / source).read_bytes() + f"\\input{{parts/{stem}}}\n".encode())
        self.put(new_input, b"New writing procedure.\n")
        if not hasattr(self, "extra_inputs"):
            self.extra_inputs = {}
        self.extra_inputs[paper_id] = [new_input]
        if nested:
            inner = "paper/exposition/parts/nested/decision.sty"
            self.put(new_input, b"\\include{nested/decision.sty}\n")
            self.put(inner, b"A nested writing decision.\n")
            self.extra_inputs[paper_id].append(inner)
        self.refresh_bindings()
        self.reconcile()
        return new_input

    def check_unlisted_include_with_fresh_exporter_receipts(self, paper_id):
        self.run_owner("--write")
        relative = self.add_unlisted_inputs(paper_id)
        self.assert_refusal_preserves_outputs("manuscript inputs missing from semantic review")
        self.assertIn(relative, self.run_owner("--check", expected=2).stderr)

    def test_unlisted_companion_include_is_rejected_with_fresh_exporter_receipts(self):
        self.check_unlisted_include_with_fresh_exporter_receipts(COMPANION)

    def test_unlisted_guide_include_is_rejected_with_fresh_exporter_receipts(self):
        self.check_unlisted_include_with_fresh_exporter_receipts(GUIDE)

    def test_included_guidance_cannot_be_exempted_by_assigning_shared_input(self):
        self.run_owner("--write")
        relative = self.add_unlisted_inputs(COMPANION)
        self.manifest["files"].append({
            "path": relative, "role": "shared_input",
            "sha256": digest((self.root / relative).read_bytes()),
        })
        self.reconcile()
        self.assert_refusal_preserves_outputs("manuscript inputs missing from semantic review")

    def test_nested_include_requires_semantic_coverage_even_with_non_tex_extension(self):
        self.run_owner("--write")
        relative = self.add_unlisted_inputs(COMPANION, nested=True)
        self.manifest["files"].append({
            "path": relative, "role": "companion_input",
            "sha256": digest((self.root / relative).read_bytes()),
        })
        self.reconcile()
        self.assert_refusal_preserves_outputs("parts/nested/decision.sty")

    def test_registered_new_input_edit_requires_new_skill_review_for_each_paper(self):
        for paper_id, role in ((GUIDE, "compact_guide_input"), (COMPANION, "companion_input")):
            with self.subTest(paper=paper_id):
                relative = self.add_unlisted_inputs(paper_id)
                existing = next((row for row in self.manifest["files"] if row["path"] == relative), None)
                if existing is None:
                    self.manifest["files"].append({"path": relative, "role": role,
                                                  "sha256": digest((self.root / relative).read_bytes())})
                else:
                    existing["role"] = role
                self.reconcile()
                self.run_owner("--write")
                self.put(relative, f"Changed procedure for {paper_id}.\n".encode())
                self.refresh_bindings()
                self.save()
                self.assert_refusal_preserves_outputs("stale paper_skill_review.paper_inputs_sha256")
                self.reconcile()
                self.run_owner("--write")
                self.run_owner("--check")

    def test_skill_edit_requires_manifest_and_review_refresh(self):
        self.run_owner("--write")
        self.put(SKILL, b"# Revised writing skill\n")
        self.assert_refusal_preserves_outputs(f"stale file hash: {SKILL}")
        self.refresh_bindings()
        self.save()
        self.assert_refusal_preserves_outputs("stale paper_skill_review.skill_sha256")

    def test_reconciled_manuscript_regenerates_changed_reference(self):
        self.run_owner("--write")
        before = self.reference_bytes()
        self.put(f"paper/exposition/{GUIDE}.tex", b"A new guide procedure.\n")
        self.put(f"paper/exposition/{GUIDE}.pdf", b"%PDF rebuilt guide\n")
        self.put(f"docs/papers/full-text/{GUIDE}.md", b"# Guide\n\nA new complete writing procedure.\n")
        self.put(SKILL, b"# Writing skill\n\nApply the new procedure.\n")
        self.refresh_bindings()
        self.reconcile()
        self.run_owner("--write")
        after = self.reference_bytes()
        self.assertNotEqual(before["writing-guide.md"], after["writing-guide.md"])
        self.assertEqual(before["worked-companion.md"], after["worked-companion.md"])
        self.assertIn(b"A new complete writing procedure.", after["writing-guide.md"])
        self.run_owner("--check")

    def test_stale_or_missing_reference_is_rejected_without_repair(self):
        self.run_owner("--write")
        self.put(REFERENCES[0], b"Hand-edited text.\n")
        self.run_owner("--check", expected=1)
        self.assertEqual((self.root / REFERENCES[0]).read_bytes(), b"Hand-edited text.\n")
        (self.root / REFERENCES[1]).unlink()
        self.run_owner("--check", expected=1)
        self.assertFalse((self.root / REFERENCES[1]).exists())

    def test_every_manifest_file_hash_is_validated_before_any_write(self):
        self.put("docs/papers/exposition-method/README.md", b"An unrecorded supporting edit.\n")
        self.assert_refusal_preserves_outputs("stale file hash: docs/papers/exposition-method/README.md")
        self.assertFalse((self.root / "skills/public-mathematical-writing/references").exists())

    def test_corpus_source_and_pdf_hashes_are_required(self):
        for field in ("source_sha256", "pdf_sha256"):
            with self.subTest(field=field):
                original = self.rows[1][field]
                self.rows[1][field] = "sha256:" + "0" * 64
                self.save()
                self.assert_refusal_preserves_outputs(f"stale {field.split('_')[0]} hash for {COMPANION}")
                self.rows[1][field] = original

    def test_corresponding_source_and_pdf_paths_cannot_be_substituted(self):
        for field in ("local_source", "local_pdf"):
            with self.subTest(field=field):
                original = self.rows[1][field]
                self.rows[1][field] = self.rows[0][field]
                self.save()
                self.assert_refusal_preserves_outputs(f"incorrect {field.split('_')[1]} path")
                self.rows[1][field] = original

    def test_missing_review_requires_explicit_reconciliation(self):
        self.manifest.pop("paper_skill_review")
        self.save()
        self.assert_refusal_preserves_outputs("missing paper_skill_review")

    def test_review_requires_valid_disposition_and_reason(self):
        for field, value in (("disposition", "copied"), ("reason", "  ")):
            with self.subTest(field=field):
                self.reconcile()
                self.manifest["paper_skill_review"][field] = value
                self.save()
                self.assert_refusal_preserves_outputs(f"paper_skill_review.{field}")

    def test_verified_unchanged_and_manifest_order_are_supported(self):
        self.reconcile("verified_unchanged")
        self.manifest["files"].reverse()
        self.save()
        self.run_owner("--write")
        self.run_owner("--check")

    def test_shared_style_is_hashed_but_excluded_from_semantic_review_digest(self):
        self.run_owner("--write")
        before = self.manifest["paper_skill_review"].copy()
        self.put("paper/paper-house-style.sty", b"A typography adjustment.\n")
        self.assert_refusal_preserves_outputs("stale file hash: paper/paper-house-style.sty")
        self.refresh_bindings()
        self.save()
        self.run_owner("--write")
        self.assertEqual(self.manifest["paper_skill_review"], before)

    def test_missing_full_text_or_duplicate_paper_never_writes_partial_references(self):
        (self.root / f"docs/papers/full-text/{COMPANION}.md").unlink()
        self.assert_refusal_preserves_outputs("missing generated full text")
        self.put(f"docs/papers/full-text/{COMPANION}.md", b"Recovered full text.\n")
        self.rows.append(self.rows[1].copy())
        self.save()
        self.assert_refusal_preserves_outputs("expected exactly one paper row")

    def test_manuscript_licence_is_retained(self):
        self.rows[1]["licence"] = "Apache-2.0"
        self.save()
        self.assert_refusal_preserves_outputs("must retain its CC-BY-4.0 manuscript licence")

    def test_full_text_receipts_are_mandatory_and_bound_to_source_and_pdf(self):
        self.run_owner("--write")
        fields = ("full_text_sha256", "full_text_source_sha256", "full_text_pdf_sha256",
                  "full_text_inputs_sha256")
        for field in fields:
            original = self.rows[1][field]
            for mutation in (None, "sha256:" + "0" * 64):
                with self.subTest(field=field, mutation=mutation):
                    if mutation is None:
                        self.rows[1].pop(field)
                    else:
                        self.rows[1][field] = mutation
                    self.save()
                    self.assert_refusal_preserves_outputs(f"missing or stale {field}")
                    self.rows[1][field] = original

    def test_hand_edited_generated_markdown_cannot_receive_current_provenance(self):
        self.run_owner("--write")
        self.put(f"docs/papers/full-text/{COMPANION}.md", b"A hand-edited stale mirror.\n")
        self.assert_refusal_preserves_outputs("missing or stale full_text_sha256")

    def test_include_only_edit_requires_new_export_even_after_semantic_review(self):
        self.run_owner("--write")
        self.put("paper/exposition/parts/lesson.tex", b"A newly reviewed companion procedure.\n")
        # Reconcile the manifest and skill review, but leave the last exporter
        # receipts untouched. Top-level source, PDF and Markdown remain equal.
        for row in self.manifest["files"]:
            row["sha256"] = digest((self.root / row["path"]).read_bytes())
        self.reconcile()
        self.assert_refusal_preserves_outputs("missing or stale full_text_inputs_sha256")


if __name__ == "__main__":
    unittest.main()
