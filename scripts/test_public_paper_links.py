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
