#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression checks for the content-addressed semantic-corpus fast path."""

from __future__ import annotations

import copy
import argparse
import contextlib
import io
import json
import hashlib
import tempfile
from pathlib import Path
from unittest.mock import patch

import build_semantic_corpus as builder
import check_cold_clone_comprehension as cold_clone
import query_semantic as query


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    roles = [{"module": module, "id": str(index), "label": "λ, nested }"}
             for index, module in enumerate(("A.lean", "A.lean", "B.lean", "a/C.lean"))]
    ranges = builder.declaration_role_module_ranges(roles)
    role_bytes = json.dumps(roles, ensure_ascii=False, separators=(",", ":")).encode()
    for needle in ("A", "a.lean", "B.lean", "missing"):
        require(query.indexed_module_roles(role_bytes, ranges, needle) ==
                [row for row in roles if needle.casefold() in row["module"].casefold()],
                "module range selection changed substring or case semantics")
    for field, value in (("start", 0), ("end", len(role_bytes)), ("count", 0)):
        broken = copy.deepcopy(ranges)
        broken[0][field] = value
        require(query.indexed_module_roles(role_bytes, broken, "A") is None,
                f"module range accepted invalid {field}")
    require(query.indexed_module_roles(role_bytes, ranges[:-1], "A") is None,
            "module ranges accepted incomplete coverage")
    require(query.indexed_module_roles(b"[]", [], "A") == [], "empty role array failed")
    require(query.indexed_module_roles(role_bytes, ranges, ("A.lean", "B.lean")) == roles[:3],
            "multiple module filters changed selection order")
    require(query.indexed_module_roles(role_bytes, ranges, ()) == [],
            "empty module selection decoded unrelated roles")
    citation_corpus = {"declaration_roles": [
        {"module": "Erdos249257/Shared.lean", "declaration": "A.one"},
        {"module": "ErdosProblems/Other/Shared.lean", "declaration": "B.two"},
        {"module": "Erdos249257/Different.lean", "declaration": "C.three"},
    ]}
    complete = query.paper_citation_role_index(citation_corpus)
    selected = query.paper_citation_role_index(citation_corpus, frozenset({"Shared.lean"}))
    require(selected == {key: rows for key, rows in complete.items()
                         if key[0].endswith("Shared.lean")},
            "paper selection changed full or shortened module aliases")
    require(query.paper_citation_role_index(citation_corpus, frozenset()) == {},
            "citation index cache leaked across selected manuscript modules")
    # Citation selection affects priority, never the universe of backlog candidates.
    backlog_roles = [
        {"id": module, "module": module, "declaration": "Namespace.same",
         "interpretation_tier": "source_structural_family", "statement_node": "structural"}
        for module in ("Erdos249257/Cited.lean", "Erdos249257/Uncited.lean")
    ]
    backlog = {"declaration_roles": backlog_roles, "statement_nodes": [], "zones": []}
    atlas = {"declarations": [{"id": role["id"], "line": 1, "kind": "theorem",
                               "signature": "True"} for role in backlog_roles]}
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        (root / "paper").mkdir()
        (root / "paper" / "selected.tex").write_text(
            r"\lref{Cited.lean}{1}{same}", encoding="utf-8")
        for paper in (None, "SELECTED", "missing"):
            args = argparse.Namespace(paper=paper, problem=None, limit=40)
            output = io.StringIO()
            with patch.object(query, "ROOT", root), patch.object(
                query, "load_declaration_atlas", return_value=atlas
            ), contextlib.redirect_stdout(output):
                query.cmd_structural_backlog(backlog, args)
            result = json.loads(output.getvalue())
            require(result["module_backlog_count"] == 2,
                    "paper selection removed uncited structural candidates")
            selected_counts = {row["module"]: row["paper_selected_role_count"]
                               for row in result["results"]}
            require(selected_counts == {"Erdos249257/Cited.lean": int(paper != "missing"),
                                        "Erdos249257/Uncited.lean": 0},
                    "short citation names escaped their module or paper filter")
    module_fixture = {"schema": "test", "declaration_roles": roles,
                      "declaration_role_module_ranges": ranges}
    module_text = builder.render(module_fixture)
    module_receipt = {
        "output_digest": "sha256:" + hashlib.sha256(module_text.encode()).hexdigest(),
        "top_level_fields": builder.top_level_field_spans(module_fixture, module_text),
    }
    module_result = query.indexed_query_corpus(module_text.encode(), module_receipt, "A")
    require(module_result["declaration_roles"] == [row for row in roles if "a" in row["module"].casefold()],
            "canonical module index changed selected rows")
    require(query.indexed_query_corpus(module_text.replace("A.lean", "X.lean").encode(), module_receipt, "A") is None,
            "module index escaped canonical output digest binding")
    fixture = {"schema": "test", "summary": {"label": "λ and \\\"quotes"},
               "declaration_roles": [{"nested": [1, 2], "text": "}, unexpected"}],
               "frontier": {"open": True}}
    text = builder.render(fixture)
    raw = text.encode("utf-8")
    indexed = {"output_digest": "sha256:" + hashlib.sha256(raw).hexdigest(),
               "top_level_fields": builder.top_level_field_spans(fixture, text)}
    expected = {key: value for key, value in fixture.items() if key != "declaration_roles"}
    require(query.indexed_query_corpus(raw, indexed) == expected, "indexed fields changed content")
    for field, value in (("start", 0), ("end", len(raw) + 1), ("key", "wrong"), ("sha256", "bad")):
        changed = copy.deepcopy(indexed)
        changed["top_level_fields"][1][field] = value
        require(query.indexed_query_corpus(raw, changed) is None, f"index accepted changed {field}")
    require(query.indexed_query_corpus(raw.replace(b"true", b"null"), indexed) is None,
            "index accepted changed corpus bytes")
    changed = copy.deepcopy(indexed)
    changed["top_level_fields"].pop()
    require(query.indexed_query_corpus(raw, changed) is None, "index accepted missing field")
    require(query.indexed_query_corpus(raw, []) is None, "index accepted malformed receipt")
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        (root / "docs").mkdir()
        corpus_path = root / "docs" / "semantic_corpus.json"
        corpus_path.write_bytes(raw)
        receipt_path = root / "docs" / "semantic_corpus_check.json"
        receipt_path.write_text(json.dumps(indexed))
        with patch.object(query, "ROOT", root), patch.object(query, "CORPUS", corpus_path):
            for include_roles in (False, True):
                query.load.cache_clear()
                with patch.object(query, "semantic_input_fingerprint", return_value="changed"):
                    try:
                        query.load(include_roles)
                    except SystemExit as error:
                        require("stale" in str(error), "stale-input diagnostic changed")
                    else:
                        raise AssertionError("indexed loader skipped source freshness")
            receipt_path.write_text("{}")
            query.load.cache_clear()
            with patch.object(query, "semantic_input_fingerprint", return_value=None):
                require(query.load(False) == fixture, "unusable index did not fall back to full JSON")
    query.load.cache_clear()
    receipt = json.loads(
        builder.safe_read_text(builder.TRACKED_CHECK_RECEIPT)
    )
    inputs = {
        "input_fingerprint": receipt["input_fingerprint"],
        "output_digest": receipt["output_digest"],
        "surface_digests": receipt["surface_digests"],
    }
    require(builder.receipt_matches(receipt, **inputs), "exact receipt was rejected")

    mutations = {
        "input fingerprint": ("input_fingerprint", "sha256:changed"),
        "output digest": ("output_digest", "sha256:changed"),
        "surface digest": ("surface_digests", {"docs/RESULTS.md": "sha256:changed"}),
    }
    for label, (field, value) in mutations.items():
        changed = dict(inputs)
        changed[field] = value
        require(
            not builder.receipt_matches(receipt, **changed),
            f"receipt accepted changed {label}",
        )

    public = receipt["summary"]["public_semantic_census"]
    census = cold_clone.semantic_census_from_public(copy.deepcopy(public))
    require(
        census["nonrecurring_total"] == public["nonrecurring"]["total"],
        "compact receipt lost the public nonrecurring census",
    )
    require(
        census["demand_equivalent_total"] == public["demand_equivalent_total"],
        "compact receipt lost the demand-equivalence census",
    )
    print("semantic corpus check receipt: exact-match and mutation checks pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
