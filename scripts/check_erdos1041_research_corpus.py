#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Fast integrity gate for the exported Erdős #1041 research corpus.

This deliberately checks the public, content-addressed publication envelope;
it does not rerun the private producer or claim that numerical evidence proves
the parent theorem.  A corpus-only pull request should not need the unrelated
paper, citation, external-verification, or whole-repository release gates.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
from pathlib import Path, PurePosixPath
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "research_corpus" / "Erdos1041"
PUBLIC_PREFIX = "research_corpus/Erdos1041"
GENERATED_ENVELOPE = {
    f"{PUBLIC_PREFIX}/CORPUS_MANIFEST.json",
    f"{PUBLIC_PREFIX}/PUBLIC_CORPUS_CHECKPOINT.json",
    f"{PUBLIC_PREFIX}/README.md",
    f"{PUBLIC_PREFIX}/STRONGEST_RESULTS.json",
}
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
PRIVATE_PATH_MARKERS = (
    ("/Users/", b"/Users/"),
    ("/home/", b"/home/"),
    ("/root/", b"/root/"),
    ("/private/var/", b"/private/var/"),
    ("file://", b"file://"),
    ("~/.codex/", b"~/.codex/"),
    ("~/.agents/", b"~/.agents/"),
    ("%USERPROFILE%\\", b"%USERPROFILE%\\"),
    ("C:\\Users\\", b"C:\\Users\\"),
    ("\\\\Users\\", b"\\\\Users\\"),
)


class CorpusError(ValueError):
    pass


def safe_public_file(path: Path, label: str) -> Path:
    """Return a regular file wholly inside the public corpus checkout."""
    root = Path(os.path.abspath(ROOT))
    candidate = Path(os.path.abspath(path))
    current = candidate
    while True:
        require(not current.is_symlink(), f"symlinked corpus path: {label}")
        if current == root:
            break
        require(current.parent != current, f"corpus path escapes checkout: {label}")
        current = current.parent
    require(candidate.is_file(), f"missing or non-regular corpus file: {label}")
    return candidate


def load_json(path: Path) -> dict[str, Any]:
    path = safe_public_file(path, str(path.relative_to(ROOT)))
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CorpusError(f"cannot read {path.relative_to(ROOT)}: {exc}") from exc
    if not isinstance(value, dict):
        raise CorpusError(f"{path.relative_to(ROOT)} must contain a JSON object")
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(safe_public_file(path, str(path.relative_to(ROOT))).read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CorpusError(message)


def private_path_leaks(data: bytes) -> list[str]:
    """Return portable local-path markers found in one public artifact."""
    folded = data.lower()
    return [label for label, marker in PRIVATE_PATH_MARKERS if marker.lower() in folded]


def safe_public_path(raw: Any) -> tuple[str, Path]:
    require(isinstance(raw, str), "manifest public_path must be a string")
    pure = PurePosixPath(raw)
    require(not pure.is_absolute() and ".." not in pure.parts, f"unsafe public path: {raw}")
    require(raw.startswith(f"{PUBLIC_PREFIX}/"), f"path escapes corpus prefix: {raw}")
    path = ROOT.joinpath(*pure.parts)
    return raw, safe_public_file(path, raw)


def check() -> tuple[int, int, int]:
    manifest_path = CORPUS / "CORPUS_MANIFEST.json"
    strongest_path = CORPUS / "STRONGEST_RESULTS.json"
    checkpoint_path = CORPUS / "PUBLIC_CORPUS_CHECKPOINT.json"
    manifest = load_json(manifest_path)
    strongest = load_json(strongest_path)
    checkpoint = load_json(checkpoint_path)

    require(manifest.get("schema") == "erdos1041_public_research_corpus_manifest_v1", "unknown corpus manifest schema")
    require(strongest.get("schema") == "erdos1041_strongest_result_activation_map_v1", "unknown strongest-result schema")
    require(checkpoint.get("schema") == "plectis_public_problem_corpus_checkpoint_v1", "unknown public checkpoint schema")
    require(manifest.get("problem_id") == strongest.get("problem_id") == checkpoint.get("problem_id") == "erdos_1041", "problem identity mismatch")
    source_commit = manifest.get("source_checkpoint")
    require(isinstance(source_commit, str) and COMMIT_RE.fullmatch(source_commit) is not None, "source checkpoint is not a full commit")
    require(strongest.get("source_checkpoint") == source_commit, "strongest-result map source checkpoint differs from manifest")
    require(checkpoint.get("source_commit") == source_commit, "public checkpoint source commit differs from manifest")
    require(manifest.get("public_prefix") == PUBLIC_PREFIX, "manifest public prefix mismatch")

    files = manifest.get("files")
    require(isinstance(files, list) and files, "manifest files must be a nonempty list")
    require(manifest.get("file_count") == len(files), "manifest file_count mismatch")
    require(checkpoint.get("exported_source_file_count") == len(files), "checkpoint file count mismatch")

    seen: set[str] = set()
    total_bytes = 0
    replacement_count = 0
    for row in files:
        require(isinstance(row, dict), "manifest file row must be an object")
        public_path, path = safe_public_path(row.get("public_path"))
        require(public_path not in seen, f"duplicate manifest path: {public_path}")
        seen.add(public_path)
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        require(SHA256_RE.fullmatch(str(row.get("published_sha256", ""))) is not None, f"malformed digest: {public_path}")
        require(digest == row.get("published_sha256"), f"digest mismatch: {public_path}")
        require(len(data) == row.get("bytes"), f"byte-count mismatch: {public_path}")
        relation = row.get("relation")
        require(
            relation in {"exact_copy", "source_faithful_public_sanitized_copy"},
            f"unknown publication relation: {public_path}",
        )
        replacements = row.get("local_path_replacements")
        require(isinstance(replacements, int) and replacements >= 0, f"bad replacement count: {public_path}")
        if relation == "exact_copy":
            require(row.get("source_sha256") == row.get("published_sha256"), f"exact-copy digest mismatch: {public_path}")
            require(replacements == 0, f"exact-copy row records replacements: {public_path}")
        else:
            require(
                row.get("source_sha256") != row.get("published_sha256"),
                f"sanitized row retained the source digest: {public_path}",
            )
        leaked = private_path_leaks(data)
        require(not leaked, f"private local-path marker in {public_path}: {leaked}")
        total_bytes += len(data)
        replacement_count += replacements

    require(manifest.get("total_bytes") == total_bytes, "manifest total_bytes mismatch")
    require(manifest.get("local_path_replacement_count") == replacement_count, "manifest replacement total mismatch")
    actual: set[str] = set()
    for path in CORPUS.rglob("*"):
        if path.is_dir():
            require(not path.is_symlink(), f"symlinked corpus directory: {path.relative_to(ROOT)}")
            continue
        actual.add(safe_public_file(path, str(path.relative_to(ROOT))).relative_to(ROOT).as_posix())
    require(actual == seen | GENERATED_ENVELOPE, f"untracked corpus files: {sorted(actual - seen - GENERATED_ENVELOPE)}; missing: {sorted((seen | GENERATED_ENVELOPE) - actual)}")
    for public_path in sorted(GENERATED_ENVELOPE):
        _, path = safe_public_path(public_path)
        leaked = private_path_leaks(path.read_bytes())
        require(not leaked, f"private local-path marker in {public_path}: {leaked}")

    strongest_pointer = manifest.get("strongest_result_map")
    require(isinstance(strongest_pointer, dict), "manifest strongest-result pointer missing")
    require(strongest_pointer.get("path") == f"{PUBLIC_PREFIX}/STRONGEST_RESULTS.json", "strongest-result path mismatch")
    require(strongest_pointer.get("sha256") == sha256(strongest_path), "strongest-result digest mismatch")
    require(checkpoint.get("strongest_result_map_sha256") == sha256(strongest_path), "checkpoint strongest-result digest mismatch")
    require(checkpoint.get("corpus_manifest_sha256") == sha256(manifest_path), "checkpoint manifest digest mismatch")
    results = strongest.get("results")
    require(isinstance(results, list) and results, "strongest-result map is empty")
    require(strongest_pointer.get("result_count") == len(results), "strongest-result count mismatch")
    result_ids: set[str] = set()
    for result in results:
        require(isinstance(result, dict), "strongest-result row must be an object")
        result_id = result.get("result_id")
        require(isinstance(result_id, str) and result_id and result_id not in result_ids, "missing or duplicate strongest-result id")
        result_ids.add(result_id)
        public_paths = result.get("public_authority_paths")
        require(isinstance(public_paths, list) and public_paths, f"{result_id} lacks public authority paths")
        for raw in public_paths:
            public_path, _ = safe_public_path(raw)
            require(public_path in seen, f"{result_id} authority is absent from manifest: {public_path}")

    return len(files), len(results), total_bytes


def main() -> int:
    try:
        file_count, result_count, total_bytes = check()
    except CorpusError as exc:
        print(f"check_erdos1041_research_corpus: FAIL: {exc}", file=sys.stderr)
        return 1
    print(
        "check_erdos1041_research_corpus: "
        f"{file_count} content-addressed files, {result_count} activated results, "
        f"{total_bytes} bytes; checkpoint coherent"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
