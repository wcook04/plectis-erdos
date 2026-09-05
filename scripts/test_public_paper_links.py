#!/usr/bin/env python3
"""Focused tests for the rendered public-paper link auditor."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("check_public_paper_links.py")
SPEC = importlib.util.spec_from_file_location("check_public_paper_links", MODULE_PATH)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def test_without_fragment_preserves_query() -> None:
    assert MODULE.without_fragment("https://example.test/a?q=1#L42") == "https://example.test/a?q=1"


def test_offline_audit_rejects_local_and_missing_cross_pdf(monkeypatch) -> None:
    monkeypatch.setattr(MODULE, "contract_pdfs", lambda: [MODULE.ROOT / "one.pdf"])
    monkeypatch.setattr(
        MODULE,
        "pdf_links",
        lambda _paths: [
            MODULE.LinkOccurrence("one.pdf", 2, "uri", "file:///Users/will/private.txt"),
            MODULE.LinkOccurrence("one.pdf", 3, "cross_pdf", "absent.pdf"),
        ],
    )
    receipt = MODULE.audit(network=False, jobs=1, timeout=1.0)
    assert not receipt["ok"]
    assert receipt["local_uri_rows"][0]["page"] == 2
    assert receipt["missing_cross_pdf_rows"][0]["target"] == "absent.pdf"


def test_network_classification_distinguishes_broken_and_access_control(monkeypatch) -> None:
    monkeypatch.setattr(MODULE, "contract_pdfs", lambda: [MODULE.ROOT / "one.pdf"])
    monkeypatch.setattr(
        MODULE,
        "pdf_links",
        lambda _paths: [
            MODULE.LinkOccurrence("one.pdf", 1, "uri", "https://example.test/gone#page=2"),
            MODULE.LinkOccurrence("one.pdf", 2, "uri", "https://example.test/blocked"),
        ],
    )
    monkeypatch.setattr(
        MODULE,
        "run_network",
        lambda _urls, jobs, timeout: [
            MODULE.NetworkResult("https://example.test/gone", 404, "", "Not Found"),
            MODULE.NetworkResult("https://example.test/blocked", 403, "", "Forbidden"),
            MODULE.NetworkResult("https://example.test/timeout", 0, "", "TimeoutError"),
        ],
    )
    receipt = MODULE.audit(network=True, jobs=2, timeout=1.0)
    assert not receipt["ok"]
    assert [row["status"] for row in receipt["broken_network_rows"]] == [404]
    assert [row["status"] for row in receipt["inconclusive_network_rows"]] == [403, 0]


def test_named_destination_is_checked_literally(monkeypatch, tmp_path) -> None:
    from types import SimpleNamespace

    target = tmp_path / "target.pdf"
    target.touch()
    monkeypatch.setattr(MODULE, "ROOT", tmp_path)
    monkeypatch.setattr(MODULE, "_load_pdf_reader", lambda: lambda _path: SimpleNamespace(
        pages=[object()], named_destinations={"systems-trust": object()}
    ))
    rows = [
        MODULE.LinkOccurrence("source.pdf", 1, "cross_pdf", "target.pdf", "systems-trust"),
        MODULE.LinkOccurrence("source.pdf", 2, "cross_pdf", "target.pdf", "nameddest=systems-trust"),
    ]
    missing, invalid = MODULE.cross_pdf_destinations(rows, [target])
    assert not missing
    assert [row["page"] for row in invalid] == [2]
    assert invalid[0]["destination"] == "nameddest=systems-trust"


def test_remote_page_targets_are_zero_based_and_must_be_shipped(monkeypatch, tmp_path) -> None:
    from types import SimpleNamespace

    folder = tmp_path / "papers"
    folder.mkdir()
    target = folder / "target.pdf"
    target.touch()
    unshipped = folder / "draft.pdf"
    unshipped.touch()
    monkeypatch.setattr(MODULE, "ROOT", tmp_path)
    monkeypatch.setattr(MODULE, "_load_pdf_reader", lambda: lambda _path: SimpleNamespace(
        pages=[object(), object()], named_destinations={}
    ))
    rows = [MODULE.LinkOccurrence("papers/source.pdf", i + 1, "cross_pdf", "target.pdf", value)
            for i, value in enumerate([0, 1, 2, -1, None])]
    rows.append(MODULE.LinkOccurrence("papers/source.pdf", 6, "cross_pdf", "draft.pdf", 0))
    missing, invalid = MODULE.cross_pdf_destinations(rows, [target])
    assert [row.page for row in missing] == [6]
    assert [row["destination"] for row in invalid] == [2, -1, None]


def test_pdf_extraction_keeps_remote_destination_and_file_spec(monkeypatch, tmp_path) -> None:
    from types import SimpleNamespace

    class Ref:
        def __init__(self, obj):
            self.obj = obj

        def get_object(self):
            return self.obj

    actions = [
        {"/S": "/GoToR", "/F": Ref({"/F": "fallback.pdf", "/UF": "target.pdf"}),
         "/D": "systems-trust"},
        {"/S": "/GoToR", "/F": "target.pdf", "/D": [0, "/Fit"]},
    ]
    page = {"/Annots": [Ref({"/A": Ref(action)}) for action in actions]}
    monkeypatch.setattr(MODULE, "ROOT", tmp_path)
    source = tmp_path / "source.pdf"
    source.touch()
    monkeypatch.setattr(MODULE, "_load_pdf_reader", lambda: lambda _path: SimpleNamespace(pages=[page]))
    rows = MODULE.pdf_links([source])
    assert [(row.target, row.destination) for row in rows] == [
        ("target.pdf", "systems-trust"), ("target.pdf", 0)
    ]
