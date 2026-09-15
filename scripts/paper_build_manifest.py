#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check that each published paper PDF was built from its committed TeX.

``docs/publication_contract.json`` pins a manuscript's ``.tex`` and its
``.pdf`` with two independent digests, and a restamp refreshes both after a
rebase whether or not anyone rebuilt the PDF. On 2026-09-15 a pull request
built its Erdos #243 PDFs, rebased its TeX onto a sibling merge, restamped
both digests and merged. The TeX carried the sibling's citations and the PDFs
lacked them.

``paper/build-manifest.json`` records the binding the two digests leave out.
For every artifact it stores the digest of each TeX input the PDF was compiled
from (the manuscript, every ``\\input`` fragment it reaches, and the shared
house style, preamble and alias table) together with the digest of the PDF
that build produced. ``scripts/sync_publication_pdfs.py`` writes a row when it
copies a build output that is at least as new as every input it records.

This check fails when a committed PDF differs from its recorded build, or when
a committed input differs from the input that build read. A TeX change
therefore reaches ``main`` only with a rebuilt PDF. ``check_publication_contract.py``
and ``check_release.py`` run the same function.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import posixpath
import re
import sys
from pathlib import Path
from typing import Any, Protocol

ROOT = Path(__file__).resolve().parent.parent
CONTRACT_PATH = "docs/publication_contract.json"
MANIFEST_PATH = "paper/build-manifest.json"
MANIFEST_SCHEMA = "plectis-erdos-paper-build-manifest/1"
MANIFEST_RULE = (
    "Each row records the TeX inputs a committed PDF was compiled from and the "
    "digest of that PDF. scripts/sync_publication_pdfs.py writes a row when it "
    "copies a fresh build output into storage. scripts/paper_build_manifest.py "
    "fails when a committed PDF or any committed input differs from its row."
)
TEX_INPUT_RE = re.compile(r"\\(?:input|include)\{([^}]+)\}")
SHARED_PAPER_RESOURCES = (
    "paper/paper-house-style.sty",
    "paper/problem-note-preamble.tex",
    "paper/module-aliases.tex",
)


class Reader(Protocol):
    def read_bytes(self, relative: str) -> bytes: ...


class WorktreeReader:
    """Read files below one checkout root, as a local build sees them."""

    def __init__(self, root: Path) -> None:
        self.root = root

    def read_bytes(self, relative: str) -> bytes:
        path = self.root / relative
        if not path.is_file():
            raise FileNotFoundError(relative)
        return path.read_bytes()


def sha256(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _read(reader: Reader, relative: str) -> bytes | None:
    try:
        return reader.read_bytes(relative)
    except (OSError, ValueError):
        return None


def storage_path(artifact: dict[str, Any]) -> str:
    storage = artifact.get("storage_path")
    if isinstance(storage, str) and storage.strip():
        return storage
    rendered = artifact.get("rendered_path")
    return rendered if isinstance(rendered, str) else ""


def build_stem(artifact: dict[str, Any]) -> str:
    """Makefile target stem: ``make -C paper <stem>.pdf`` builds this artifact."""
    rendered = artifact.get("rendered_path") or artifact.get("source_path") or ""
    return Path(str(rendered)).stem


def rebuild_instruction(artifact: dict[str, Any]) -> str:
    return (
        f"rebuild it with `make -C paper {build_stem(artifact)}.pdf`, record the "
        "build with `python3 scripts/sync_publication_pdfs.py`, then run "
        "`python3 scripts/check_publication_contract.py --restamp --apply`"
    )


def _input_candidates(including: str, raw: str) -> list[str]:
    """Paths a TeX ``\\input`` may name, in the order the PDF sync resolves them."""
    name = raw.strip()
    if not name or name.startswith("*"):
        return []
    names = [f"{name}.tex", name] if not posixpath.splitext(name)[1] else [name]
    candidates: list[str] = []
    for candidate_name in names:
        for base in (posixpath.dirname(including), "paper"):
            candidate = posixpath.normpath(posixpath.join(base, candidate_name))
            if posixpath.isabs(candidate) or candidate == ".." or candidate.startswith("../"):
                continue
            candidates.append(candidate)
    return candidates


def input_closure(reader: Reader, source_path: str) -> dict[str, bytes]:
    """Every file one manuscript's build reads, keyed by repository path."""
    closure: dict[str, bytes] = {}
    source = _read(reader, source_path)
    if source is not None:
        closure[source_path] = source
        queue = [source_path]
        while queue:
            current = queue.pop()
            try:
                text = closure[current].decode("utf-8")
            except UnicodeError:
                continue
            for match in TEX_INPUT_RE.finditer(text):
                for candidate in _input_candidates(current, match.group(1)):
                    if candidate in closure:
                        break
                    data = _read(reader, candidate)
                    if data is None:
                        continue
                    closure[candidate] = data
                    queue.append(candidate)
                    break
    for shared in SHARED_PAPER_RESOURCES:
        if shared not in closure:
            data = _read(reader, shared)
            if data is not None:
                closure[shared] = data
    return closure


def input_digests(reader: Reader, source_path: str) -> dict[str, str]:
    closure = input_closure(reader, source_path)
    return {path: sha256(closure[path]) for path in sorted(closure)}


def build_record(
    reader: Reader, artifact: dict[str, Any], rendered: bytes
) -> dict[str, Any]:
    """The row a fresh build of ``artifact`` producing ``rendered`` earns."""
    return {
        "inputs": input_digests(reader, artifact["source_path"]),
        "rendered_content_digest": sha256(rendered),
        "source_path": artifact["source_path"],
        "storage_path": storage_path(artifact),
    }


def empty_manifest() -> dict[str, Any]:
    return {"builds": {}, "rule": MANIFEST_RULE, "schema": MANIFEST_SCHEMA}


def load_manifest(reader: Reader) -> dict[str, Any] | None:
    data = _read(reader, MANIFEST_PATH)
    if data is None:
        return None
    return json.loads(data.decode("utf-8"))


def manifest_bytes(manifest: dict[str, Any]) -> bytes:
    return (
        json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def write_manifest(root: Path, manifest: dict[str, Any]) -> None:
    path = root / MANIFEST_PATH
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(manifest_bytes(manifest))


def build_record_errors(
    reader: Reader, artifact: dict[str, Any], record: Any
) -> list[str]:
    """Why ``record`` does not describe the committed PDF and its inputs."""
    artifact_id = artifact.get("id", "<unknown>")
    source = artifact.get("source_path")
    storage = storage_path(artifact)
    rebuild = rebuild_instruction(artifact)
    if not isinstance(record, dict):
        return [
            f"publication artifact {artifact_id!r} has no recorded build in "
            f"{MANIFEST_PATH} for {storage}; {rebuild}"
        ]
    if (
        not isinstance(source, str)
        or record.get("source_path") != source
        or record.get("storage_path") != storage
    ):
        return [
            f"{MANIFEST_PATH} records {artifact_id!r} as "
            f"{record.get('source_path')!r} -> {record.get('storage_path')!r}, "
            f"and the publication contract names {source!r} -> {storage!r}; {rebuild}"
        ]
    errors: list[str] = []
    rendered = _read(reader, storage)
    if rendered is None:
        errors.append(f"publication artifact {artifact_id!r} PDF is unreadable: {storage}")
    elif record.get("rendered_content_digest") != sha256(rendered):
        errors.append(
            f"publication artifact {artifact_id!r} committed PDF {storage} is "
            "not the PDF its recorded build produced (recorded "
            f"{record.get('rendered_content_digest')}, committed {sha256(rendered)}); "
            f"{rebuild}"
        )
    recorded_inputs = record.get("inputs")
    if not isinstance(recorded_inputs, dict) or not recorded_inputs:
        errors.append(
            f"{MANIFEST_PATH} records no TeX inputs for {artifact_id!r}; {rebuild}"
        )
        return errors
    current = input_digests(reader, source)
    changed = sorted(
        path
        for path in set(recorded_inputs) | set(current)
        if recorded_inputs.get(path) != current.get(path)
    )
    if changed:
        errors.append(
            f"publication artifact {artifact_id!r} PDF {storage} was built from "
            "TeX inputs that differ from the committed ones: "
            f"{', '.join(changed)}; {rebuild}"
        )
    return errors


def recorded_build_matches(
    reader: Reader, artifact: dict[str, Any], manifest: dict[str, Any] | None
) -> bool:
    """True when the committed PDF is the recorded build of the committed inputs."""
    if not isinstance(manifest, dict) or not isinstance(manifest.get("builds"), dict):
        return False
    record = manifest["builds"].get(artifact.get("id"))
    return isinstance(record, dict) and not build_record_errors(reader, artifact, record)


def manifest_errors(
    reader: Reader,
    *,
    contract: dict[str, Any] | None = None,
    manifest: dict[str, Any] | None = None,
) -> list[str]:
    """Every registered PDF must be the recorded build of its committed inputs."""
    if contract is None:
        data = _read(reader, CONTRACT_PATH)
        if data is None:
            return [f"{CONTRACT_PATH} is unreadable"]
        try:
            contract = json.loads(data.decode("utf-8"))
        except ValueError as error:
            return [f"{CONTRACT_PATH}: {error}"]
    if manifest is None:
        try:
            manifest = load_manifest(reader)
        except ValueError as error:
            return [f"{MANIFEST_PATH}: {error}"]
        if manifest is None:
            return [
                f"{MANIFEST_PATH} is missing, so no publication PDF has a recorded "
                "build; build the papers with `make -C paper`, which records them"
            ]
    errors: list[str] = []
    if manifest.get("schema") != MANIFEST_SCHEMA:
        errors.append(f"{MANIFEST_PATH} must use schema {MANIFEST_SCHEMA}")
    builds = manifest.get("builds")
    if not isinstance(builds, dict):
        return [*errors, f"{MANIFEST_PATH} must map artifact ids to recorded builds"]
    artifacts = [row for row in contract.get("artifacts", []) if isinstance(row, dict)]
    registered = {row.get("id") for row in artifacts}
    for unknown in sorted(str(key) for key in set(builds) - registered):
        errors.append(
            f"{MANIFEST_PATH} records a build of {unknown!r}, which the publication "
            "contract does not register"
        )
    for artifact in artifacts:
        errors.extend(
            build_record_errors(reader, artifact, builds.get(artifact.get("id")))
        )
    return errors


def newer_inputs(root: Path, artifact: dict[str, Any], output: Path) -> list[str]:
    """Inputs modified after ``output`` was written. A fresh build has none."""
    source = artifact.get("source_path")
    if not isinstance(source, str):
        return []
    output_time = output.stat().st_mtime_ns
    return sorted(
        path
        for path in input_closure(WorktreeReader(root), source)
        if (root / path).stat().st_mtime_ns > output_time
    )


def record_builds(
    root: Path, built: list[tuple[dict[str, Any], bytes]]
) -> dict[str, Any]:
    """The manifest with a fresh row for each ``(artifact, built PDF bytes)``."""
    reader = WorktreeReader(root)
    manifest = load_manifest(reader) or empty_manifest()
    builds = manifest.setdefault("builds", {})
    for artifact, rendered in built:
        builds[artifact["id"]] = build_record(reader, artifact, rendered)
    return manifest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check that each published paper PDF was built from its committed TeX."
    )
    parser.add_argument(
        "--git-ref",
        help="check a committed Git ref, or ':' for the staged index",
    )
    args = parser.parse_args(argv)
    from publication_contract import RepositoryReader

    errors = manifest_errors(RepositoryReader(ROOT, args.git_ref))
    if errors:
        print(f"paper_build_manifest: {len(errors)} failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1
    target = args.git_ref or "worktree"
    print(
        "paper_build_manifest: every publication PDF is the recorded build of its "
        f"committed TeX inputs at {target}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
