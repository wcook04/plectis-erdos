#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Copy Makefile PDF output into each artifact's storage_path.

Build output is the designated Makefile location ``paper/<hosted-stem>.pdf``.
Those copies are temporary; published artifacts live at ``storage_path``.

A missing build output is not a success just because an older destination
PDF still exists. Verified unchanged-artifact reuse is a separate mode: the
complete relevant source inputs and the published PDF must still match the
approved build record.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
CONTRACT = ROOT / "docs" / "publication_contract.json"
PAPER = ROOT / "paper"
BUILD_OUTPUT_DIR = PAPER
TEX_INPUT_RE = re.compile(r"\\(?:input|include)\{([^}]+)\}")
SHARED_PAPER_RESOURCES = (
    "paper/paper-house-style.sty",
    "paper/problem-note-preamble.tex",
    "paper/module-aliases.tex",
)


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def is_temporary_build_pdf(relative: str) -> bool:
    """Makefile VPATH output: ``paper/<basename>.pdf``, never a nested storage path."""
    parts = Path(relative).parts
    return len(parts) == 2 and parts[0] == "paper" and parts[1].endswith(".pdf")


def build_output_pdf(root: Path, artifact: dict[str, Any]) -> Path:
    stem = Path(artifact["rendered_path"]).stem
    return root / "paper" / f"{stem}.pdf"


def _resolve_tex_input(source_file: Path, paper_dir: Path, raw: str) -> Path | None:
    name = raw.strip()
    if not name or name.startswith("*"):
        return None
    candidates = []
    raw_path = Path(name)
    if not raw_path.suffix:
        candidates.extend((source_file.parent / f"{name}.tex", paper_dir / f"{name}.tex"))
    candidates.extend((source_file.parent / name, paper_dir / name))
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    return None


def manuscript_input_paths(root: Path, source_relative: str) -> list[str]:
    """Top-level manuscript plus TeX fragments and shared paper resources."""
    paper_dir = root / "paper"
    source = root / source_relative
    found: dict[str, Path] = {}
    if source.is_file():
        found[source_relative] = source
        queue = [source]
        seen = {source.resolve()}
        while queue:
            current = queue.pop()
            try:
                text = current.read_text(encoding="utf-8")
            except (OSError, UnicodeError):
                continue
            for match in TEX_INPUT_RE.finditer(text):
                resolved = _resolve_tex_input(current, paper_dir, match.group(1))
                if resolved is None:
                    continue
                identity = resolved.resolve()
                if identity in seen:
                    continue
                seen.add(identity)
                try:
                    relative = resolved.resolve().relative_to(root.resolve()).as_posix()
                except ValueError:
                    continue
                found[relative] = resolved
                queue.append(resolved)
    for shared in SHARED_PAPER_RESOURCES:
        path = root / shared
        if path.is_file():
            found[shared] = path
    return sorted(found)


def source_input_closure_digest(root: Path, artifact: dict[str, Any]) -> str:
    records: list[str] = []
    for relative in manuscript_input_paths(root, artifact["source_path"]):
        records.append(f"{relative}={sha256_bytes((root / relative).read_bytes())}")
    return sha256_bytes(("\n".join(records) + "\n").encode("utf-8"))


def verified_reuse(root: Path, artifact: dict[str, Any], dest: Path) -> tuple[bool, str]:
    """Legitimate no-op: complete inputs and published PDF still match the record."""
    if not dest.is_file():
        return False, "published destination is missing"
    expected_pdf = artifact.get("rendered_content_digest")
    if not expected_pdf or sha256_bytes(dest.read_bytes()) != expected_pdf:
        return False, "published PDF does not match the approved rendered digest"
    source = root / artifact["source_path"]
    expected_source = artifact.get("source_content_digest")
    if not source.is_file() or not expected_source:
        return False, "approved source record is missing"
    if sha256_bytes(source.read_bytes()) != expected_source:
        return False, "manuscript source does not match the approved source digest"
    current_closure = source_input_closure_digest(root, artifact)
    recorded_closure = artifact.get("source_input_closure_digest")
    extras = [
        path
        for path in manuscript_input_paths(root, artifact["source_path"])
        if path != artifact["source_path"]
    ]
    if recorded_closure:
        if current_closure != recorded_closure:
            return False, "complete source inputs drifted from the approved build record"
        return True, "verified unchanged-artifact reuse"
    if extras:
        return False, (
            "supporting TeX inputs or shared resources exist, but no approved "
            "source_input_closure_digest is recorded"
        )
    return True, "verified unchanged-artifact reuse"


def synchronize_publication_pdfs(root: Path, contract: dict[str, Any]) -> tuple[int, str]:
    reused: list[str] = []
    copy_plan: list[tuple[str, Path, Path]] = []
    for artifact in contract["artifacts"]:
        artifact_id = artifact.get("id", "<unknown>")
        storage = artifact["storage_path"]
        built = build_output_pdf(root, artifact)
        dest = root / storage
        if built.is_file():
            copy_plan.append((artifact_id, built, dest))
            continue
        ok, reason = verified_reuse(root, artifact, dest)
        if ok:
            reused.append(artifact_id)
            continue
        return (
            1,
            (
                f"missing required build output for {artifact_id}: "
                f"{built.as_posix()} ({reason}); "
                "the existing destination PDF cannot substitute"
            ),
        )
    for _, built, dest in copy_plan:
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(built, dest)
    if reused and not copy_plan:
        return 0, "publication PDFs reused from approved unchanged-artifact record"
    return 0, "publication PDFs synchronized to storage_path"


def build_parser() -> argparse.ArgumentParser:
    """Parse the intentionally argument-free synchronization command."""
    return argparse.ArgumentParser(description=__doc__)


def main(root: Path | None = None) -> int:
    checkout = root or ROOT
    contract = json.loads((checkout / "docs" / "publication_contract.json").read_text(encoding="utf-8"))
    code, message = synchronize_publication_pdfs(checkout, contract)
    stream = sys.stderr if code else sys.stdout
    print(message, file=stream)
    return code


def cli(argv: list[str] | None = None) -> int:
    """Validate CLI arguments before loading the contract or copying PDFs."""
    build_parser().parse_args(argv)
    return main()


if __name__ == "__main__":
    raise SystemExit(cli())
