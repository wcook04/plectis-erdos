#!/usr/bin/env python3
"""Audit hyperlinks embedded in every PDF in the publication contract.

The default pass is offline: it rejects host-local URI targets and checks that
every cross-PDF link names a shipped sibling file.  ``--network`` additionally
requests every distinct public HTTP target after removing its fragment.  The
network pass deliberately reports access-denied responses separately from
broken targets; a publisher can inspect those sites without treating bot
blocking as proof that a citation is dead.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import ssl
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "docs" / "publication_contract.json"
LOCAL_URI_MARKERS = ("file://", "localhost", "127.0.0.1", "/Users/", "/tmp/", "/var/")
INCONCLUSIVE_HTTP_CODES = frozenset({401, 403, 405, 406, 418, 429})


@dataclass(frozen=True)
class LinkOccurrence:
    pdf: str
    page: int
    kind: str
    target: str


@dataclass(frozen=True)
class NetworkResult:
    url: str
    status: int
    final_url: str
    error: str


def _load_pdf_reader():
    try:
        from pypdf import PdfReader
    except ModuleNotFoundError as exc:  # pragma: no cover - environment boundary
        raise RuntimeError(
            "pypdf is required to inspect rendered link annotations; run this "
            "check in the paper-build environment"
        ) from exc
    return PdfReader


def contract_pdfs() -> list[Path]:
    payload = json.loads(CONTRACT.read_text(encoding="utf-8"))
    paths: list[Path] = []
    for artifact in payload.get("artifacts", []):
        rendered = artifact.get("rendered_path")
        if rendered:
            paths.append(ROOT / rendered)
    return paths


def pdf_links(paths: Iterable[Path]) -> list[LinkOccurrence]:
    PdfReader = _load_pdf_reader()
    rows: list[LinkOccurrence] = []
    for path in paths:
        if not path.is_file():
            raise FileNotFoundError(f"publication PDF is missing: {path.relative_to(ROOT)}")
        for page_number, page in enumerate(PdfReader(str(path)).pages, start=1):
            for annotation_ref in page.get("/Annots") or []:
                annotation = annotation_ref.get_object()
                action_ref = annotation.get("/A")
                if not action_ref:
                    continue
                action = action_ref.get_object()
                uri = action.get("/URI")
                if uri:
                    rows.append(
                        LinkOccurrence(str(path.relative_to(ROOT)), page_number, "uri", str(uri))
                    )
                if action.get("/S") == "/GoToR" and action.get("/F"):
                    rows.append(
                        LinkOccurrence(
                            str(path.relative_to(ROOT)),
                            page_number,
                            "cross_pdf",
                            str(action.get("/F")),
                        )
                    )
    return rows


def without_fragment(url: str) -> str:
    split = urllib.parse.urlsplit(url)
    return urllib.parse.urlunsplit((split.scheme, split.netloc, split.path, split.query, ""))


def check_url(url: str, *, timeout: float) -> NetworkResult:
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": "Mozilla/5.0 (compatible; plectis-public-paper-link-audit/1.0)",
            "Range": "bytes=0-1023",
        },
        method="GET",
    )
    try:
        with urllib.request.urlopen(
            request, timeout=timeout, context=ssl.create_default_context()
        ) as response:
            response.read(1)
            return NetworkResult(url, int(response.status), response.geturl(), "")
    except urllib.error.HTTPError as exc:
        return NetworkResult(url, int(exc.code), exc.geturl(), str(exc.reason))
    except Exception as exc:  # network failures must be represented in the receipt
        return NetworkResult(url, 0, "", f"{type(exc).__name__}: {exc}")


def run_network(urls: Iterable[str], *, jobs: int, timeout: float) -> list[NetworkResult]:
    distinct = sorted({without_fragment(url) for url in urls})
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = [executor.submit(check_url, url, timeout=timeout) for url in distinct]
        return sorted((future.result() for future in concurrent.futures.as_completed(futures)), key=lambda row: row.url)


def audit(*, network: bool, jobs: int, timeout: float) -> dict:
    links = pdf_links(contract_pdfs())
    uri_rows = [row for row in links if row.kind == "uri"]
    cross_rows = [row for row in links if row.kind == "cross_pdf"]
    local_uri_rows = [
        row for row in uri_rows if any(marker in row.target for marker in LOCAL_URI_MARKERS)
    ]
    missing_cross_rows = [row for row in cross_rows if not (ROOT / row.target).is_file()]

    network_rows = run_network(
        (row.target for row in uri_rows), jobs=jobs, timeout=timeout
    ) if network else []
    broken = [
        row
        for row in network_rows
        if not 200 <= row.status < 400 and row.status not in INCONCLUSIVE_HTTP_CODES
    ]
    inconclusive = [row for row in network_rows if row.status in INCONCLUSIVE_HTTP_CODES]
    ok = not local_uri_rows and not missing_cross_rows and not broken
    return {
        "schema": "public_paper_link_audit_v1",
        "ok": ok,
        "network_checked": network,
        "pdf_count": len(contract_pdfs()),
        "annotation_count": len(links),
        "uri_annotation_count": len(uri_rows),
        "distinct_public_target_count": len({without_fragment(row.target) for row in uri_rows}),
        "cross_pdf_annotation_count": len(cross_rows),
        "local_uri_rows": [asdict(row) for row in local_uri_rows],
        "missing_cross_pdf_rows": [asdict(row) for row in missing_cross_rows],
        "broken_network_rows": [asdict(row) for row in broken],
        "inconclusive_network_rows": [asdict(row) for row in inconclusive],
        "network_ok_count": sum(200 <= row.status < 400 for row in network_rows),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--network", action="store_true", help="request every distinct HTTP target")
    parser.add_argument("--jobs", type=int, default=16)
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    try:
        receipt = audit(network=args.network, jobs=args.jobs, timeout=args.timeout)
    except (FileNotFoundError, RuntimeError, json.JSONDecodeError) as exc:
        print(f"check_public_paper_links: {exc}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(receipt, indent=2, sort_keys=True))
    else:
        print(
            "public paper links: "
            f"{receipt['pdf_count']} PDFs, {receipt['uri_annotation_count']} URI annotations, "
            f"{receipt['distinct_public_target_count']} distinct public targets, "
            f"{receipt['cross_pdf_annotation_count']} cross-PDF links"
        )
        if receipt["broken_network_rows"]:
            for row in receipt["broken_network_rows"]:
                print(f"BROKEN {row['status']} {row['url']} {row['error']}")
        if receipt["inconclusive_network_rows"]:
            print(
                "inconclusive access-controlled targets: "
                f"{len(receipt['inconclusive_network_rows'])}"
            )
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
