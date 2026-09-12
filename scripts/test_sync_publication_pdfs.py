#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""PDF sync must not accept an old destination when a rebuild is required."""

from __future__ import annotations

import hashlib
import io
import json
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

import sync_publication_pdfs as sync


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def write_fixture(root: Path, source: str, fragment: str, published: bytes) -> dict:
    source_path = "paper/68/example.tex"
    fragment_path = "paper/68/fragment.tex"
    storage_path = "paper/68/example.pdf"
    sty = "paper/paper-house-style.sty"
    (root / "docs").mkdir()
    (root / "paper/68").mkdir(parents=True)
    (root / source_path).write_text(source, encoding="utf-8")
    (root / fragment_path).write_text(fragment, encoding="utf-8")
    (root / sty).write_text("% house style\n", encoding="utf-8")
    (root / storage_path).write_bytes(published)
    artifact = {
        "id": "example",
        "source_path": source_path,
        "source_content_digest": sha256_bytes(source.encode("utf-8")),
        "rendered_path": "example.pdf",
        "rendered_content_digest": sha256_bytes(published),
        "storage_path": storage_path,
        "source_input_closure_digest": "",
    }
    artifact["source_input_closure_digest"] = sync.source_input_closure_digest(root, artifact)
    contract = {"artifacts": [artifact]}
    (root / "docs/publication_contract.json").write_text(
        json.dumps(contract, indent=2) + "\n", encoding="utf-8"
    )
    return artifact


def test_cli_argument_boundary() -> None:
    """Help and invalid arguments must exit before the mutating main function."""
    with patch.object(sync, "main") as runner:
        with redirect_stdout(io.StringIO()):
            try:
                sync.cli(["--help"])
            except SystemExit as error:
                require(error.code == 0, f"--help exited with {error.code}")
            else:
                raise AssertionError("--help did not exit through argparse")
        runner.assert_not_called()

    with patch.object(sync, "main") as runner:
        with redirect_stderr(io.StringIO()):
            try:
                sync.cli(["--unsupported"])
            except SystemExit as error:
                require(error.code == 2, f"unsupported argument exited with {error.code}")
            else:
                raise AssertionError("unsupported argument was accepted")
        runner.assert_not_called()


def test_imported_main_root_contract() -> None:
    """Fixtures may still invoke ``main(root=...)`` without CLI parsing."""
    with tempfile.TemporaryDirectory(prefix="pdf-sync-main-root-") as raw:
        root = Path(raw)
        write_fixture(
            root,
            "\\input{fragment}\nhello\n",
            "fragment body\n",
            b"old-published-pdf",
        )
        with redirect_stdout(io.StringIO()):
            code = sync.main(root=root)
        require(code == 0, "imported main(root=...) fixture contract failed")


def main() -> int:
    test_cli_argument_boundary()
    test_imported_main_root_contract()

    with tempfile.TemporaryDirectory(prefix="pdf-sync-rebuild-") as raw:
        root = Path(raw)
        source = "\\input{fragment}\nhello\n"
        artifact = write_fixture(root, source, "fragment body\n", b"old-published-pdf")
        (root / "paper/example.pdf").unlink(missing_ok=True)
        (root / artifact["source_path"]).write_text(
            source + "% changed top-level\n", encoding="utf-8"
        )
        code, message = sync.synchronize_publication_pdfs(
            root,
            json.loads((root / "docs/publication_contract.json").read_text(encoding="utf-8")),
        )
        require(code == 1, f"changed top-level source was accepted without rebuild: {message}")
        require("cannot substitute" in message, message)
        require((root / artifact["storage_path"]).read_bytes() == b"old-published-pdf", message)

    with tempfile.TemporaryDirectory(prefix="pdf-sync-fragment-") as raw:
        root = Path(raw)
        source = "\\input{fragment}\nhello\n"
        artifact = write_fixture(root, source, "fragment body\n", b"old-published-pdf")
        (root / "paper/68/fragment.tex").write_text("changed fragment\n", encoding="utf-8")
        code, message = sync.synchronize_publication_pdfs(
            root,
            json.loads((root / "docs/publication_contract.json").read_text(encoding="utf-8")),
        )
        require(code == 1, f"changed TeX fragment was accepted without rebuild: {message}")
        require("cannot substitute" in message, message)

    with tempfile.TemporaryDirectory(prefix="pdf-sync-shared-") as raw:
        root = Path(raw)
        source = "\\input{fragment}\nhello\n"
        artifact = write_fixture(root, source, "fragment body\n", b"old-published-pdf")
        (root / "paper/paper-house-style.sty").write_text("% changed shared sty\n", encoding="utf-8")
        code, message = sync.synchronize_publication_pdfs(
            root,
            json.loads((root / "docs/publication_contract.json").read_text(encoding="utf-8")),
        )
        require(code == 1, f"changed shared resource was accepted without rebuild: {message}")
        require("cannot substitute" in message, message)

    with tempfile.TemporaryDirectory(prefix="pdf-sync-reuse-") as raw:
        root = Path(raw)
        source = "\\input{fragment}\nhello\n"
        artifact = write_fixture(root, source, "fragment body\n", b"old-published-pdf")
        code, message = sync.synchronize_publication_pdfs(
            root,
            json.loads((root / "docs/publication_contract.json").read_text(encoding="utf-8")),
        )
        require(code == 0, f"unchanged approved record was rejected: {message}")
        require("reused" in message, message)
        require((root / artifact["storage_path"]).read_bytes() == b"old-published-pdf", message)

    with tempfile.TemporaryDirectory(prefix="pdf-sync-copy-") as raw:
        root = Path(raw)
        source = "\\input{fragment}\nhello\n"
        artifact = write_fixture(root, source, "fragment body\n", b"old-published-pdf")
        (root / "paper/example.pdf").write_bytes(b"fresh-build-output")
        code, message = sync.synchronize_publication_pdfs(
            root,
            json.loads((root / "docs/publication_contract.json").read_text(encoding="utf-8")),
        )
        require(code == 0, f"fresh build output was not copied: {message}")
        require((root / artifact["storage_path"]).read_bytes() == b"fresh-build-output", message)
        require(sync.is_temporary_build_pdf("paper/example.pdf"), "build output location drifted")
        require(
            not sync.is_temporary_build_pdf("paper/68/example.pdf"),
            "nested storage was treated as temporary build output",
        )

    with tempfile.TemporaryDirectory(prefix="pdf-sync-atomic-plan-") as raw:
        root = Path(raw)
        (root / "paper/68").mkdir(parents=True)
        first_destination = root / "paper/68/first.pdf"
        first_destination.write_bytes(b"published-first")
        (root / "paper/first.pdf").write_bytes(b"fresh-first")
        contract = {
            "artifacts": [
                {
                    "id": "first",
                    "rendered_path": "first.pdf",
                    "storage_path": "paper/68/first.pdf",
                },
                {
                    "id": "missing",
                    "rendered_path": "missing.pdf",
                    "storage_path": "paper/69/missing.pdf",
                },
            ]
        }
        code, message = sync.synchronize_publication_pdfs(root, contract)
        require(code == 1, f"missing later artifact was accepted: {message}")
        require(
            first_destination.read_bytes() == b"published-first",
            "an earlier PDF was copied before the full artifact set validated",
        )
        require(
            not (root / "paper/69").exists(),
            "validation failure created a later destination directory",
        )

    makefile = (sync.ROOT / "paper" / "Makefile").read_text(encoding="utf-8")
    require(
        "tectonic -o . -Z search-path=. $<" in makefile,
        "nested paper sources must compile into paper/<stem>.pdf via tectonic outdir/search-path",
    )

    print(
        "test_sync_publication_pdfs: CLI arguments fail before mutation; "
        "missing rebuild fails atomically; verified reuse and fresh build copy "
        "remain distinct"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
