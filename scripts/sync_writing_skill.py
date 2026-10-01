#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Bundle the two writing papers into their portable skill after reconciliation.

The authored exposition-method version manifest must bind every listed file,
the paper corpus must bind the current manuscripts and PDFs, and
``paper_skill_review`` must bind the current paper inputs and SKILL.md. This
records a review; it cannot determine whether the instructions are adequate.
Procedure changes require updated instructions. ``verified_unchanged`` is for
non-procedural changes whose recorded reason explains why no instruction changed.

The paper-input digest is SHA256 of UTF-8 compact JSON: selected manifest rows
reduced to {path, sha256, role}, sorted by (path, role, sha256), with sorted object
keys, ensure_ascii=True and separators=(",", ":"). Only compact_guide_source,
companion_source and companion_input participate; shared style is excluded.

This owner copies existing generated Markdown without exporting or rewriting it.
Exporter receipts must bind that Markdown to its byte digest, current source,
PDF and complete manuscript input closure, including included TeX and style.
Refresh that text with docs/papers/refresh_paper_corpus.py after rebuilding changed
PDFs, then reconcile the manifest before running this script with --write.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import tempfile
from pathlib import Path

from sync_publication_pdfs import source_input_closure_digest

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "docs/papers/exposition-method/version.json"
CORPUS = "docs/papers/corpus.json"
SKILL = "skills/public-mathematical-writing/SKILL.md"
PAPER_INPUT_ROLES = frozenset({"compact_guide_source", "companion_source", "companion_input"})
PAPERS = (
    ("writing-a-good-mathematical-paper", "compact_guide_source", "compact_guide_pdf", "writing-guide.md"),
    ("writing-mathematics-from-reviewed-revisions", "companion_source", "companion_pdf", "worked-companion.md"),
)
REPAIR = (
    "Reconcile both writing papers with skills/public-mathematical-writing/SKILL.md; "
    "update instructions for procedure changes, or record verified_unchanged with a reason "
    "for non-procedural changes. Rebuild changed PDFs using paper/Makefile, run "
    "python3 docs/papers/refresh_paper_corpus.py --write "
    "--paper writing-a-good-mathematical-paper --paper writing-mathematics-from-reviewed-revisions, "
    "then update all version.json file hashes and paper_skill_review digests before "
    "python3 scripts/sync_writing_skill.py --write."
)


class WritingSkillError(ValueError):
    pass


def fail(message: str) -> None:
    raise WritingSkillError(f"{message}\n{REPAIR}")


def safe_path(root: Path, relative: str) -> Path:
    if not isinstance(relative, str) or not relative or "\\" in relative:
        fail(f"invalid repository path: {relative!r}")
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts or path.as_posix() != relative:
        fail(f"invalid repository path: {relative!r}")
    current = root
    for part in path.parts:
        current /= part
        if current.is_symlink():
            fail(f"symlink in repository path: {relative}")
    return current


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_json(root: Path, relative: str) -> dict:
    path = safe_path(root, relative)
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        fail(f"cannot read {relative}: {error}")
    if not isinstance(value, dict):
        fail(f"{relative} must contain a JSON object")
    return value


def paper_inputs_sha256(files: list[dict]) -> str:
    rows = [{key: row[key] for key in ("path", "sha256", "role")}
            for row in files if row["role"] in PAPER_INPUT_ROLES]
    rows.sort(key=lambda row: (row["path"], row["role"], row["sha256"]))
    return sha256(json.dumps(rows, sort_keys=True, separators=(",", ":"),
                             ensure_ascii=True).encode("utf-8"))


def validated_manifest(root: Path) -> dict:
    manifest = load_json(root, MANIFEST)
    if manifest.get("schema") != "exposition-method-version/1":
        fail(f"{MANIFEST}: unsupported or missing schema")
    files = manifest.get("files")
    required = manifest.get("required_roles")
    if not isinstance(files, list) or not files:
        fail(f"{MANIFEST}: files must be a nonempty list")
    if not isinstance(required, list) or not required or any(
        not isinstance(role, str) or not role.strip() for role in required
    ):
        fail(f"{MANIFEST}: required_roles must be a nonempty list of roles")
    seen, roles = set(), set()
    for row in files:
        if not isinstance(row, dict):
            fail(f"{MANIFEST}: every file entry must be an object")
        relative, expected, role = row.get("path"), row.get("sha256"), row.get("role")
        path = safe_path(root, relative)
        if relative in seen:
            fail(f"{MANIFEST}: duplicate file entry: {relative}")
        seen.add(relative)
        if not isinstance(role, str) or not role.strip():
            fail(f"{MANIFEST}: missing role for {relative}")
        roles.add(role)
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            fail(f"{MANIFEST}: invalid sha256 for {relative}")
        if not path.is_file():
            fail(f"{MANIFEST}: missing listed file: {relative}")
        if sha256(path.read_bytes()) != expected:
            fail(f"{MANIFEST}: stale file hash: {relative}")
    needed = set(required) | {"skill", "companion_input"}
    needed.update(role for _, source_role, pdf_role, _ in PAPERS for role in (source_role, pdf_role))
    if needed - roles:
        fail(f"{MANIFEST}: missing required file roles: {sorted(needed - roles)}")
    skill_rows = [row for row in files if row["role"] == "skill"]
    if len(skill_rows) != 1 or skill_rows[0]["path"] != SKILL:
        fail(f"{MANIFEST}: the skill role must bind exactly {SKILL}")
    review = manifest.get("paper_skill_review")
    if not isinstance(review, dict):
        fail(f"{MANIFEST}: missing paper_skill_review reconciliation record")
    if review.get("paper_inputs_sha256") != paper_inputs_sha256(files):
        fail(f"{MANIFEST}: stale paper_skill_review.paper_inputs_sha256")
    if review.get("skill_sha256") != skill_rows[0]["sha256"]:
        fail(f"{MANIFEST}: stale paper_skill_review.skill_sha256")
    if review.get("disposition") not in ("updated", "verified_unchanged"):
        fail(f"{MANIFEST}: paper_skill_review.disposition must be updated or verified_unchanged")
    if not isinstance(review.get("reason"), str) or not review["reason"].strip():
        fail(f"{MANIFEST}: paper_skill_review.reason must explain the reconciliation")
    return manifest


def build(root: Path) -> dict[Path, bytes]:
    """Validate all inputs, then prepare both reference payloads without writing."""
    manifest = validated_manifest(root)
    corpus = load_json(root, CORPUS)
    papers = corpus.get("papers")
    if not isinstance(papers, list) or any(not isinstance(row, dict) for row in papers):
        fail(f"{CORPUS}: papers must be a list of paper records")
    outputs = {}
    for paper_id, source_role, pdf_role, output_name in PAPERS:
        rows = [row for row in papers if row.get("paper_id") == paper_id]
        if len(rows) != 1:
            fail(f"{CORPUS}: expected exactly one paper row for {paper_id}")
        paper = rows[0]
        for kind, role, suffix in (("source", source_role, ".tex"), ("pdf", pdf_role, ".pdf")):
            relative = f"paper/exposition/{paper_id}{suffix}"
            bindings = [row for row in manifest["files"] if row["role"] == role]
            if len(bindings) != 1 or bindings[0]["path"] != relative:
                fail(f"{MANIFEST}: {role} must bind exactly {relative}")
            if paper.get(f"local_{kind}") != relative:
                fail(f"{CORPUS}: incorrect {kind} path for {paper_id}")
            if paper.get(f"{kind}_sha256") != "sha256:" + bindings[0]["sha256"]:
                fail(f"{CORPUS}: stale {kind} hash for {paper_id}; refresh the native paper corpus")
        text_relative = f"docs/papers/full-text/{paper_id}.md"
        if paper.get("local_full_text") != text_relative:
            fail(f"{CORPUS}: incorrect full-text path for {paper_id}")
        text_path = safe_path(root, text_relative)
        if not text_path.is_file():
            fail(f"missing generated full text: {text_relative}")
        if paper.get("licence") != "CC-BY-4.0":
            fail(f"{CORPUS}: {paper_id} must retain its CC-BY-4.0 manuscript licence")
        copyright_text = paper.get("copyright")
        if not isinstance(copyright_text, str) or not copyright_text.strip() or any(
            part in copyright_text for part in ("\n", "\r", "-->")
        ):
            fail(f"{CORPUS}: missing or invalid copyright for {paper_id}")
        body = text_path.read_bytes()
        body.decode("utf-8")
        text_bindings = {
            "full_text_sha256": "sha256:" + sha256(body),
            "full_text_source_sha256": paper["source_sha256"],
            "full_text_pdf_sha256": paper["pdf_sha256"],
            "full_text_inputs_sha256": source_input_closure_digest(
                root, {"source_path": paper["local_source"]}
            ),
        }
        for field, expected in text_bindings.items():
            if paper.get(field) != expected:
                fail(f"{CORPUS}: missing or stale {field} for {paper_id}; refresh the native paper corpus")
        # REUSE-IgnoreStart
        header = (
            f"<!-- SPDX-FileCopyrightText: {copyright_text} -->\n"
            "<!-- SPDX-License-Identifier: CC-BY-4.0 -->\n"
            f"<!-- Generated by scripts/sync_writing_skill.py from {text_relative};\n"
            f"     reconciled through {MANIFEST}. Do not edit by hand. -->\n"
            "<!-- Canonical public provenance:\n"
            f"     Manuscript: https://github.com/wcook04/plectis-erdos/blob/main/{paper['local_source']}\n"
            f"     PDF: https://github.com/wcook04/plectis-erdos/blob/main/{paper['local_pdf']}\n"
            f"     Generated text: https://github.com/wcook04/plectis-erdos/blob/main/{text_relative}\n"
            f"     Source SHA256: {paper['source_sha256']}\n"
            f"     PDF SHA256: {paper['pdf_sha256']}\n"
            f"     Full-text SHA256: {paper['full_text_sha256']}\n"
            f"     Full-text inputs SHA256: {paper['full_text_inputs_sha256']} -->\n\n"
        )
        # REUSE-IgnoreEnd
        output = safe_path(root, f"skills/public-mathematical-writing/references/{output_name}")
        outputs[output] = header.encode("utf-8") + body
    return outputs


def write_references(outputs: dict[Path, bytes]) -> None:
    if not outputs:
        return
    parent = next(iter(outputs)).parent
    parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".writing-skill-sync-", dir=parent))
    previous: dict[Path, Path | None] = {}
    installed: list[Path] = []
    retain_backup = False
    try:
        # Prepare the complete pair and recovery copies before replacing either
        # reference. Input validation alone cannot rule out filesystem failure.
        for path, payload in outputs.items():
            (staging / f"{path.name}.new").write_bytes(payload)
            backup = staging / f"{path.name}.old"
            if path.exists():
                shutil.copy2(path, backup)
                previous[path] = backup
            else:
                previous[path] = None
        try:
            for path in outputs:
                os.replace(staging / f"{path.name}.new", path)
                installed.append(path)
        except OSError as error:
            restore_errors = []
            for path in reversed(installed):
                try:
                    if previous[path] is None:
                        path.unlink()
                    else:
                        os.replace(previous[path], path)
                except OSError as restore_error:
                    restore_errors.append(f"{path.name}: {restore_error}")
            if restore_errors:
                retain_backup = True
                raise OSError(
                    f"reference refresh failed: {error}; restoration failed: "
                    f"{'; '.join(restore_errors)}; recovery files retained at {staging}"
                ) from error
            raise
    finally:
        if not retain_backup:
            shutil.rmtree(staging)


def sync(root: Path, *, write: bool) -> dict:
    root = root.resolve()
    outputs = build(root)
    changed = [str(path.relative_to(root)) for path, payload in outputs.items()
               if not path.is_file() or path.read_bytes() != payload]
    if write:
        write_references({path: outputs[path] for path in outputs
                          if str(path.relative_to(root)) in changed})
    return {"status": "written" if write else ("stale" if changed else "current"),
            "changed": changed, "semantic_review_verified": "recorded_reconciliation_only"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="sync references after input validation")
    mode.add_argument("--check", action="store_true", help="fail when references or reconciliation are stale")
    args = parser.parse_args(argv)
    try:
        result = sync(args.root, write=args.write)
    except (OSError, ValueError) as error:
        parser.exit(2, f"writing skill sync: {error}\n")
    print(json.dumps(result, indent=2))
    if args.check and result["changed"]:
        print("Run python3 scripts/sync_writing_skill.py --write after reconciling the writing skill.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
