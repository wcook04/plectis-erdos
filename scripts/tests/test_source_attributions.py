#!/usr/bin/env python3
"""Focused tests for the source-attribution projection."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import build_source_attributions as subject

WITHHELD = "A mathematician (name withheld pending confirmation)"


def correspondence(row: dict, **overrides) -> dict:
    """Turn the fixture's public source into a private-correspondence row."""
    row.update({
        "id":"correspondence-001","kind":"correspondence","title":"Advice on the public exposition",
        "authors":[WITHHELD],"urls":[],
        "source_locators":[{"locator":"Private correspondence; public implementation linked below"}],
        "identity_disclosure":"withheld_pending_confirmation","confirmation_status":"not_confirmed",
        "verification_state":"implemented_advice","received_on":"2026-09-17",
        "ledger":{"told":"A reader said the opening used names that meant nothing on a first reading.","changed":"The opening now uses ordinary words and says what the hypothesis excludes."},
    })
    row.update(overrides)
    return row


class SourceAttributionTests(unittest.TestCase):
    def fixture(self) -> tuple[Path, Path]:
        temporary = Path(tempfile.mkdtemp())
        (temporary / "docs/papers").mkdir(parents=True)
        (temporary / "docs/research-commons").mkdir(parents=True)
        (temporary / "paper").mkdir()
        (temporary / "lean").mkdir()
        tex = temporary / "paper/test.tex"
        tex.write_text(
            "Text \\citep[see][p.~3]{Alpha, Beta}.\n"
            "More \\citet{\nAlpha}.\n"
            "\\begin{thebibliography}{9}\n"
            "\\bibitem[Alias]{Alpha} A. Author. https://example.org/a\n"
            "\\bibitem{Unused} U. Writer.\n"
            "\\end{thebibliography}\n", encoding="utf-8"
        )
        lean = temporary / "lean/Test.lean"
        lean.write_text(
            'def notAComment := "https://example.org/a Author Alpha"\n'
            "-- Author, following https://example.org/a and Alpha\n"
            "/- Unused is only a lexical candidate. -/\n", encoding="utf-8"
        )
        (temporary / "docs/papers/corpus.json").write_text(json.dumps({
            "papers": [{"paper_id":"paper-one","local_source":"paper/test.tex"}]
        }), encoding="utf-8")
        registry = temporary / "docs/research-commons/source-attributions.json"
        registry.write_text(json.dumps({
            "schema":"research-source-attributions/1", "scope":{"statement":"fixture"},
            "sources":[{
                "id":"alpha", "kind":"literature", "title":"Alpha source",
                "authors":["Alice Author"], "urls":["https://example.org/a"],
                "problems":["249"],
                "source_locators":[{"url":"https://example.org/a","locator":"Theorem 1"}],
                "artifact_links":[{"path":"paper/test.tex","line_start":1,"line_end":1}],
                "relation":"Cited input only; no endorsement.",
                "verification_state":"source_verified",
                "bibliography_keys":[{"path":"paper/test.tex","key":"Alpha"}]
            }]
        }), encoding="utf-8")
        return temporary, registry

    def build(self):
        root, registry = self.fixture()
        with patch.object(subject.lean_source, "library_source_paths", return_value=[root / "lean/Test.lean"]):
            return root, subject.build(root, registry, root / "docs/papers/corpus.json")

    def test_multiline_multiple_keys_and_optional_qualifiers(self):
        _root, result = self.build()
        uses = result["paper_inventory"]["citation_usages"]
        self.assertEqual([row["key"] for row in uses], ["Alpha", "Beta", "Alpha"])
        self.assertEqual(uses[-1]["line_start"], 2)
        self.assertEqual(uses[-1]["line_end"], 3)
        self.assertEqual(result["paper_inventory"]["unmatched_citation_keys"], [{"paper_id":"paper-one","key":"Beta"}])

    def test_bibliography_definitions_remain_distinct_from_usage(self):
        _root, result = self.build()
        bibliography = result["paper_inventory"]["bibliography_entries"]
        self.assertEqual({row["key"] for row in bibliography}, {"Alpha", "Unused"})
        self.assertTrue(all(row["kind"] == "bibliography_entry" for row in bibliography))
        self.assertEqual(result["coverage"]["bibliography_without_curated_link_count"], 1)

    def test_lean_candidates_are_comment_only_and_overlap_deduplicated(self):
        _root, result = self.build()
        candidates = result["lean_inventory"]["lexical_candidates"]
        self.assertEqual([row["line_start"] for row in candidates], [2, 3])
        self.assertEqual(candidates[0]["classification"], "lexical_candidate_not_attribution")
        keys = [(m["token"],m["match_kind"]) for m in candidates[0]["matches"]]
        self.assertEqual(len(keys), len(set(keys)))
        self.assertIn(("https://example.org/a", "explicit_url"), keys)
        self.assertIn(("alpha", "bibliography_key"), keys)

    def test_path_escape_and_bad_range_fail(self):
        root, registry = self.fixture()
        data=json.loads(registry.read_text())
        data["sources"][0]["artifact_links"][0]["path"]="../secret"
        registry.write_text(json.dumps(data))
        with self.assertRaises(subject.AttributionError):
            subject.build(root, registry, root/"docs/papers/corpus.json")

    def test_duplicate_ids_and_dangling_bibliography_binding_fail(self):
        root, registry = self.fixture(); data=json.loads(registry.read_text())
        data["sources"].append(dict(data["sources"][0]))
        registry.write_text(json.dumps(data))
        with self.assertRaisesRegex(subject.AttributionError,"duplicate source id"):
            subject.build(root, registry, root/"docs/papers/corpus.json")
        data["sources"]=data["sources"][:1]
        data["sources"][0]["bibliography_keys"][0]["path"]="paper/missing.tex"
        registry.write_text(json.dumps(data))
        with self.assertRaisesRegex(subject.AttributionError,"dangling bibliography"):
            subject.build(root, registry, root/"docs/papers/corpus.json")

    def test_private_correspondence_is_anonymous_and_has_no_evidence_path(self):
        root, registry = self.fixture(); data=json.loads(registry.read_text())
        row=correspondence(data["sources"][0],verification_state="source_verified")
        registry.write_text(json.dumps(data))
        with patch.object(subject.lean_source,"library_source_paths",return_value=[]):
            result=subject.build(root,registry,root/"docs/papers/corpus.json")
        self.assertNotIn("evidence_path",json.dumps(result["sources"]))
        row["source_locators"][0].update({"evidence_path":"paper/test.tex","line_start":1,"line_end":1})
        registry.write_text(json.dumps(data))
        with self.assertRaisesRegex(subject.AttributionError,"must stay outside"):
            subject.build(root,registry,root/"docs/papers/corpus.json")

    def test_human_view_links_sources_artifacts_and_complete_index(self):
        _root, result=self.build()
        before = subject.canonical(result)
        rendered=subject.markdown(result).decode()
        self.assertEqual(subject.canonical(result), before)
        self.assertTrue(result["paper_inventory"]["citation_usages"])
        for source in result["sources"]:
            self.assertIn(f'<a id="source-{subject.anchor_id(source["id"])}"></a>', rendered)
            self.assertIn(source["id"], rendered)
            for author in source["authors"]:
                self.assertIn(subject.md_escape(author), rendered)
        self.assertIn("[Alpha source](https://example.org/a)",rendered)
        self.assertIn("[Theorem 1](https://example.org/a)",rendered)
        self.assertIn("../../paper/test.tex#L1-L1",rendered)
        self.assertNotIn("Paper citation usages:",rendered)
        self.assertIn("[source-attribution-index.json](source-attribution-index.json)",rendered)
        self.assertIn("python3 scripts/build_source_attributions.py --query",rendered)
        self.assertIn("../../paper/test.tex#L1-L1",rendered)
        self.assertLess(rendered.index("## Sources and exact uses"),rendered.index("## Coverage requiring review"))

    def test_human_view_keeps_correspondence_anonymous(self):
        root,registry=self.fixture(); data=json.loads(registry.read_text()); correspondence(data["sources"][0])
        registry.write_text(json.dumps(data))
        with patch.object(subject.lean_source,"library_source_paths",return_value=[]): result=subject.build(root,registry,root/"docs/papers/corpus.json")
        rendered=subject.markdown(result).decode()
        self.assertIn(WITHHELD,rendered)
        self.assertIn("Private correspondence; public implementation linked below",rendered)
        self.assertIn("CREDIT_LEDGER.md#credit-correspondence-001",rendered)
        self.assertNotIn("mailto:",rendered)

    def build_with(self, data: dict) -> dict:
        root,registry=self.fixture(); registry.write_text(json.dumps(data))
        with patch.object(subject.lean_source,"library_source_paths",return_value=[]):
            return subject.build(root,registry,root/"docs/papers/corpus.json")

    def fixture_data(self) -> dict:
        _root,registry=self.fixture(); return json.loads(registry.read_text())

    def test_credit_ledger_lists_advice_newest_first_with_its_trace(self):
        data=self.fixture_data(); first=correspondence(data["sources"][0])
        second=correspondence(json.loads(json.dumps(first)),id="correspondence-002",title="A prior-art pointer",received_on="2026-08-05",bibliography_keys=[])
        data["sources"].append(second)
        ledger=subject.credit_ledger(self.build_with(data))
        self.assertEqual(ledger["schema"],subject.CREDIT_LEDGER_SCHEMA)
        self.assertEqual([entry["id"] for entry in ledger["entries"]],["correspondence-001","correspondence-002"])
        entry=ledger["entries"][0]
        self.assertEqual(entry["naming"]["state"],"withheld_pending_confirmation")
        self.assertEqual(entry["role"],"mathematician")
        self.assertEqual(entry["artifacts"][0]["path"],"paper/test.tex")
        self.assertEqual(ledger["counts"],{"entries":2,"withheld_pending_confirmation":2,"named_with_permission":0,"anonymous_by_request":0})
        rendered=subject.credit_ledger_markdown(ledger).decode()
        self.assertIn('<a id="credit-correspondence-001"></a>',rendered)
        self.assertIn("## 17 September 2026: Advice on the public exposition",rendered)
        self.assertIn("withheld until they confirm (credited as a mathematician)",rendered)
        self.assertIn("../../paper/test.tex#L1-L1",rendered)
        self.assertLess(rendered.index("17 September 2026"),rendered.index("5 August 2026"))

    def test_named_correspondent_needs_a_confirmation_date_and_their_name(self):
        data=self.fixture_data()
        correspondence(data["sources"][0],identity_disclosure="named_with_permission",confirmation_status="confirmed",authors=["Ada Lovelace"])
        with self.assertRaisesRegex(subject.AttributionError,"confirmed_on"):
            self.build_with(data)
        data["sources"][0]["confirmed_on"]="2026-09-01"
        with self.assertRaisesRegex(subject.AttributionError,"precedes"):
            self.build_with(data)
        data["sources"][0]["confirmed_on"]="2026-10-01"
        entry=subject.credit_ledger(self.build_with(data))["entries"][0]
        self.assertEqual(entry["credited_as"],"Ada Lovelace")
        self.assertIn("Ada Lovelace, named with their permission on 1 October 2026.",subject.credit_ledger_markdown(subject.credit_ledger(self.build_with(data))).decode())
        data["sources"][0]["authors"]=[WITHHELD]
        with self.assertRaisesRegex(subject.AttributionError,"public name"):
            self.build_with(data)

    def test_withheld_or_anonymous_entries_keep_a_neutral_label(self):
        data=self.fixture_data()
        correspondence(data["sources"][0],authors=["Ada Lovelace"])
        with self.assertRaisesRegex(subject.AttributionError,"neutral label"):
            self.build_with(data)
        correspondence(data["sources"][0],identity_disclosure="anonymous_by_request",confirmation_status="declined",authors=["A researcher (anonymous at their request)"])
        entry=subject.credit_ledger(self.build_with(data))["entries"][0]
        self.assertEqual(entry["naming"]["display"],"Anonymous at their request.")
        correspondence(data["sources"][0],identity_disclosure="anonymous_by_request",confirmation_status="not_confirmed",authors=["A researcher (anonymous at their request)"])
        with self.assertRaisesRegex(subject.AttributionError,"naming state"):
            self.build_with(data)
        correspondence(data["sources"][0],confirmed_on="2026-10-01")
        with self.assertRaisesRegex(subject.AttributionError,"confirmed_on applies only"):
            self.build_with(data)

    def test_ledger_lines_are_short_dated_and_link_free(self):
        data=self.fixture_data(); row=correspondence(data["sources"][0])
        row["received_on"]="17 September"
        with self.assertRaisesRegex(subject.AttributionError,"received_on"):
            self.build_with(data)
        correspondence(row); row["ledger"]["told"]="See https://example.org/private for what they said."
        with self.assertRaisesRegex(subject.AttributionError,"without links"):
            self.build_with(data)
        correspondence(row); row["ledger"]={"told":"x"*300,"changed":"Short."}
        with self.assertRaisesRegex(subject.AttributionError,"at most"):
            self.build_with(data)
        correspondence(row); del row["ledger"]["changed"]
        with self.assertRaisesRegex(subject.AttributionError,"ledger"):
            self.build_with(data)

    def test_implementing_commits_are_full_hashes_and_link_publicly(self):
        data=self.fixture_data(); row=correspondence(data["sources"][0],implemented_in=["e062d93"])
        with self.assertRaisesRegex(subject.AttributionError,"commit hashes"):
            self.build_with(data)
        row["implemented_in"]=["a"*40]
        ledger=subject.credit_ledger(self.build_with(data))
        self.assertEqual(ledger["entries"][0]["commits"],[{"sha":"a"*40,"url":subject.PUBLIC_COMMIT_URL+"a"*40}])
        self.assertIn(f"- **Commits:** [aaaaaaaaaa]({subject.PUBLIC_COMMIT_URL}{'a'*40})",subject.credit_ledger_markdown(ledger).decode())

    def test_markdown_artifacts_link_to_the_plain_view(self):
        root,registry=self.fixture(); (root/"docs/NOTE.md").write_text("one\ntwo\n",encoding="utf-8")
        data=json.loads(registry.read_text()); correspondence(data["sources"][0],artifact_links=[{"path":"docs/NOTE.md","line_start":2,"line_end":2}])
        registry.write_text(json.dumps(data))
        with patch.object(subject.lean_source,"library_source_paths",return_value=[]): result=subject.build(root,registry,root/"docs/papers/corpus.json")
        self.assertIn("(../../docs/NOTE.md?plain=1#L2-L2)",subject.credit_ledger_markdown(subject.credit_ledger(result)).decode())

    def test_naming_fields_belong_only_to_private_correspondence(self):
        data=self.fixture_data(); data["sources"][0]["received_on"]="2026-09-17"
        with self.assertRaisesRegex(subject.AttributionError,"only to private correspondence"):
            self.build_with(data)

    def test_shared_url_retains_all_candidates_without_arbitrary_binding(self):
        root,registry=self.fixture(); data=json.loads(registry.read_text())
        second=dict(data["sources"][0]); second.update({"id":"alpha-second","title":"Second source sharing URL","authors":["Bob Author"],"bibliography_keys":[]})
        data["sources"].append(second); registry.write_text(json.dumps(data))
        with patch.object(subject.lean_source,"library_source_paths",return_value=[root/"lean/Test.lean"]): result=subject.build(root,registry,root/"docs/papers/corpus.json")
        url_match=next(m for c in result["lean_inventory"]["lexical_candidates"] for m in c["matches"] if m["match_kind"]=="explicit_url")
        self.assertEqual(url_match["source_ids"],["alpha","alpha-second"])
        self.assertIsNone(url_match["source_id"])

    def test_generic_bibliography_tokens_do_not_create_lean_noise(self):
        root,registry=self.fixture()
        paper=root/"paper/test.tex"; paper.write_text(paper.read_text()+"\\bibitem{lean} Generic infrastructure.\n")
        lean=root/"lean/Test.lean"; lean.write_text("-- lean theorem proof mathlib main\n")
        with patch.object(subject.lean_source,"library_source_paths",return_value=[lean]): result=subject.build(root,registry,root/"docs/papers/corpus.json")
        self.assertEqual(result["lean_inventory"]["lexical_candidates"],[])

    def test_url_fragments_distinguish_posts_on_one_public_thread(self):
        self.assertNotEqual(
            subject.normalized_url("https://forum.example/thread#post-1"),
            subject.normalized_url("https://forum.example/thread#post-2"),
        )

    def test_nonbibliographic_lean_review_closes_candidate_and_digest_drift_fails(self):
        root,registry=self.fixture(); data=json.loads(registry.read_text()); lean=root/"lean/Test.lean"
        data["lean_reviews"]=[{"path":"lean/Test.lean","line_start":3,"line_end":3,"excerpt_sha256":subject.excerpt_digest(lean,3,3),"disposition":"not_bibliographic","source_ids":[],"reason":"Generic lexical overlap, not a source citation."}]
        registry.write_text(json.dumps(data))
        with patch.object(subject.lean_source,"library_source_paths",return_value=[lean]): result=subject.build(root,registry,root/"docs/papers/corpus.json")
        reviewed=next(c for c in result["lean_inventory"]["lexical_candidates"] if c["line_start"]==3)
        self.assertEqual(reviewed["review_status"],"reviewed")
        self.assertEqual(result["lean_inventory"]["awaiting_review_count"],1)
        data["lean_reviews"][0]["excerpt_sha256"]="sha256:"+"0"*64; registry.write_text(json.dumps(data))
        with self.assertRaisesRegex(subject.AttributionError,"excerpt_sha256"):
            subject.build(root,registry,root/"docs/papers/corpus.json")

    def test_lean_review_source_ids_must_be_known(self):
        root,registry=self.fixture(); data=json.loads(registry.read_text()); lean=root/"lean/Test.lean"
        data["lean_reviews"]=[{"path":"lean/Test.lean","line_start":2,"line_end":2,"excerpt_sha256":subject.excerpt_digest(lean,2,2),"disposition":"reviewed_citation_or_comparison","source_ids":["missing"],"reason":"Explicit source use."}]
        registry.write_text(json.dumps(data))
        with self.assertRaisesRegex(subject.AttributionError,"known sources"):
            subject.build(root,registry,root/"docs/papers/corpus.json")

    def test_old_style_arxiv_and_nested_lean_comments_are_candidates(self):
        text="/- outer\n  /- nested arXiv:math/0603053 -/\n  DOI:10.1000/example\n-/\ndef x := 1\n"
        comments=list(subject.comment_lines(text))
        self.assertEqual([line for line,_ in comments],[1,2,3,4])
        joined=" ".join(comment for _,comment in comments)
        self.assertIn("arXiv:math/0603053",subject.REF_RE.findall(joined))
        self.assertIn("DOI:10.1000/example",subject.REF_RE.findall(joined))

    def test_correspondence_rejects_email_or_local_path_hidden_in_relation(self):
        root,registry=self.fixture(); data=json.loads(registry.read_text())
        row=correspondence(data["sources"][0],relation="Implemented advice from hidden@example.org.")
        registry.write_text(json.dumps(data))
        with self.assertRaisesRegex(subject.AttributionError,"private address"):
            subject.build(root,registry,root/"docs/papers/corpus.json")
        row["relation"]="Evidence was stored at /Users/private/mail.txt."
        registry.write_text(json.dumps(data))
        with self.assertRaisesRegex(subject.AttributionError,"local path"):
            subject.build(root,registry,root/"docs/papers/corpus.json")

    def test_lean_review_context_digest_detects_surrounding_comment_change(self):
        root,registry=self.fixture(); data=json.loads(registry.read_text()); lean=root/"lean/Test.lean"
        review={"path":"lean/Test.lean","line_start":2,"line_end":2,"excerpt_sha256":subject.excerpt_digest(lean,2,2),"disposition":"reviewed_citation_or_comparison","source_ids":["alpha"],"reason":"Explicit source link.","context":{"line_start":1,"line_end":2,"excerpt_sha256":subject.excerpt_digest(lean,1,2)}}
        data["lean_reviews"]=[review]; registry.write_text(json.dumps(data))
        with patch.object(subject.lean_source,"library_source_paths",return_value=[lean]): subject.build(root,registry,root/"docs/papers/corpus.json")
        lines=lean.read_text().splitlines(); lines[0]='def changedContext := "same candidate below"'; lean.write_text("\n".join(lines)+"\n")
        with self.assertRaisesRegex(subject.AttributionError,"context.*excerpt_sha256"):
            subject.build(root,registry,root/"docs/papers/corpus.json")


if __name__ == "__main__": unittest.main()
