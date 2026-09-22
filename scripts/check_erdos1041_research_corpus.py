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
import stat
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
SCHEMA_ENVELOPES = {
    (
        "erdos1041_public_research_corpus_manifest_v1",
        "erdos1041_strongest_result_activation_map_v1",
        "plectis_public_problem_corpus_checkpoint_v1",
    ): "legacy_v1",
    (
        "plectis_public_research_corpus_manifest_v2",
        "plectis_strongest_result_activation_map_v2",
        "plectis_public_problem_corpus_checkpoint_v2",
    ): "generic_v2",
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


def read_public_bytes(path: Path, label: str) -> bytes:
    """Read public bytes through a no-follow descriptor after path admission."""
    candidate = safe_public_file(path, label)
    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise CorpusError(f"cannot safely read corpus file: {label}: {exc}") from exc
    try:
        require(
            stat.S_ISREG(os.fstat(descriptor).st_mode),
            f"non-regular corpus file: {label}",
        )
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = -1
            return stream.read()
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def load_json(path: Path) -> dict[str, Any]:
    label = str(path.relative_to(ROOT))
    try:
        value = json.loads(read_public_bytes(path, label).decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CorpusError(f"cannot read {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise CorpusError(f"{label} must contain a JSON object")
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(
        read_public_bytes(path, str(path.relative_to(ROOT)))
    ).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CorpusError(message)


def private_path_leaks(data: bytes) -> list[str]:
    """Return portable local-path markers found in one public artifact."""
    folded = data.lower()
    leaks = []
    for label, marker in PRIVATE_PATH_MARKERS:
        marker = marker.lower()
        if marker not in folded:
            continue
        if marker in {b"/users/", b"/home/", b"/root/", b"/private/var/"} and not re.search(
            rb"(?<![a-z0-9_.-])" + re.escape(marker), folded
        ):
            continue
        leaks.append(label)
    return leaks


def safe_public_path(raw: Any) -> tuple[str, Path]:
    require(isinstance(raw, str), "manifest public_path must be a string")
    pure = PurePosixPath(raw)
    require(not pure.is_absolute() and ".." not in pure.parts, f"unsafe public path: {raw}")
    require(raw.startswith(f"{PUBLIC_PREFIX}/"), f"path escapes corpus prefix: {raw}")
    path = ROOT.joinpath(*pure.parts)
    return raw, safe_public_file(path, raw)


def envelope_version(
    manifest: dict[str, Any], strongest: dict[str, Any], checkpoint: dict[str, Any]
) -> str:
    """Accept one coherent legacy or generic envelope, never a mixed tuple."""
    schemas = (
        manifest.get("schema"), strongest.get("schema"), checkpoint.get("schema")
    )
    require(schemas in SCHEMA_ENVELOPES, f"unknown or mixed corpus schemas: {schemas}")
    return SCHEMA_ENVELOPES[schemas]


def strongest_result_id(result: dict[str, Any], version: str) -> str:
    """Return the row identity without conflating activation and packet rows."""
    result_id = result.get("result_id")
    source_result_id = result.get("source_result_id")
    if version == "legacy_v1":
        require(
            isinstance(result_id, str) and result_id and source_result_id is None,
            "legacy strongest-result row must have result_id only",
        )
        return result_id
    require(
        (isinstance(result_id, str) and result_id and source_result_id is None)
        or (
            isinstance(source_result_id, str)
            and source_result_id
            and result_id is None
        ),
        "generic strongest-result row must have exactly one of result_id or source_result_id",
    )
    return str(result_id or source_result_id)


def validate_result_authority(
    result: dict[str, Any], version: str, result_id: str
) -> list[Any]:
    """Require either manifest-bound public sources or an explicit no-authority row."""
    public_paths = result.get("public_authority_paths")
    require(isinstance(public_paths, list), f"{result_id} has malformed public authority paths")
    authority_binding = result.get("authority_binding")
    if version == "legacy_v1":
        require(public_paths, f"{result_id} lacks public authority paths")
    elif public_paths:
        require(
            isinstance(authority_binding, dict)
            and authority_binding.get("status") == "bound_public_source",
            f"{result_id} has paths without a bound public-source receipt",
        )
    else:
        require(
            result.get("source_result_id") == result_id,
            f"{result_id} activation row lacks public authority paths",
        )
        require(
            isinstance(authority_binding, dict)
            and authority_binding.get("status") == "unresolved_source_locator"
            and authority_binding.get("posture")
            == "source_status_only_not_public_authority"
            and authority_binding.get("reason")
            in {
                "unresolved_declaration_locator",
                "research_packet_row_has_no_resolved_source_locator",
            },
            f"{result_id} has empty authority without an explicit unresolved binding",
        )
    return public_paths


def check() -> tuple[int, int, int]:
    manifest_path = CORPUS / "CORPUS_MANIFEST.json"
    strongest_path = CORPUS / "STRONGEST_RESULTS.json"
    checkpoint_path = CORPUS / "PUBLIC_CORPUS_CHECKPOINT.json"
    manifest = load_json(manifest_path)
    strongest = load_json(strongest_path)
    checkpoint = load_json(checkpoint_path)

    version = envelope_version(manifest, strongest, checkpoint)
    require(manifest.get("problem_id") == strongest.get("problem_id") == checkpoint.get("problem_id") == "erdos_1041", "problem identity mismatch")
    source_commit = manifest.get("source_checkpoint")
    require(isinstance(source_commit, str) and COMMIT_RE.fullmatch(source_commit) is not None, "source checkpoint is not a full commit")
    require(strongest.get("source_checkpoint") == source_commit, "strongest-result map source checkpoint differs from manifest")
    require(checkpoint.get("source_commit") == source_commit, "public checkpoint source commit differs from manifest")
    require(manifest.get("public_prefix") == PUBLIC_PREFIX, "manifest public prefix mismatch")
    if version == "generic_v2":
        require(
            manifest.get("sanitization_profile") == "erdos1041_public_coordinates",
            "generic corpus sanitization profile mismatch",
        )

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
        data = read_public_bytes(path, public_path)
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
    generated_envelope = set(GENERATED_ENVELOPE)
    if version == "generic_v2":
        generated_envelope.add(f"{PUBLIC_PREFIX}/FRONTIER.md")
    require(actual == seen | generated_envelope, f"untracked corpus files: {sorted(actual - seen - generated_envelope)}; missing: {sorted((seen | generated_envelope) - actual)}")
    for public_path in sorted(generated_envelope):
        _, path = safe_public_path(public_path)
        leaked = private_path_leaks(read_public_bytes(path, public_path))
        require(not leaked, f"private local-path marker in {public_path}: {leaked}")

    strongest_pointer = manifest.get("strongest_result_map")
    require(isinstance(strongest_pointer, dict), "manifest strongest-result pointer missing")
    require(strongest_pointer.get("path") == f"{PUBLIC_PREFIX}/STRONGEST_RESULTS.json", "strongest-result path mismatch")
    require(strongest_pointer.get("sha256") == sha256(strongest_path), "strongest-result digest mismatch")
    require(checkpoint.get("strongest_result_map_sha256") == sha256(strongest_path), "checkpoint strongest-result digest mismatch")
    require(checkpoint.get("corpus_manifest_sha256") == sha256(manifest_path), "checkpoint manifest digest mismatch")
    require(checkpoint.get("corpus_manifest_path") == f"{PUBLIC_PREFIX}/CORPUS_MANIFEST.json", "checkpoint manifest path mismatch")
    require(checkpoint.get("strongest_result_map_path") == f"{PUBLIC_PREFIX}/STRONGEST_RESULTS.json", "checkpoint strongest-result path mismatch")
    if version == "generic_v2":
        frontier_pointer = manifest.get("browser_frontier")
        require(isinstance(frontier_pointer, dict), "generic corpus frontier pointer missing")
        require(frontier_pointer.get("path") == f"{PUBLIC_PREFIX}/FRONTIER.md", "frontier path mismatch")
        require(frontier_pointer.get("sha256") == sha256(CORPUS / "FRONTIER.md"), "frontier digest mismatch")
        require(frontier_pointer.get("source") == "exported research_packet.json", "frontier source mismatch")
    results = strongest.get("results")
    require(isinstance(results, list) and results, "strongest-result map is empty")
    require(strongest_pointer.get("result_count") == len(results), "strongest-result count mismatch")
    result_ids: set[str] = set()
    for result in results:
        require(isinstance(result, dict), "strongest-result row must be an object")
        result_id = strongest_result_id(result, version)
        require(result_id not in result_ids, "missing or duplicate strongest-result id")
        result_ids.add(result_id)
        public_paths = validate_result_authority(result, version, result_id)
        for raw in public_paths:
            public_path, _ = safe_public_path(raw)
            require(public_path in seen, f"{result_id} authority is absent from manifest: {public_path}")

    return len(files), len(results), total_bytes


# `research_corpus/Erdos1041` is source-only: it is absent from `lakefile.toml`
# and from both root import files, so no job in this repository elaborates it,
# and it sits outside `check_release.py`'s `LIBRARY_ROOTS` proof-trust scan.
# docs/SCOPE.md already says it extends neither the checkpoint nor `docs/claims.json`,
# but nothing enforced that boundary at the token level: a `sorry` or a fresh
# `native_decide` could land here and no gate in the repository would notice.
#
# `sorry`, `admit`, and project-defined axioms have no justification in a
# published corpus and are rejected outright. The committed source refresh
# replaces the former nine native decisions in CentroidHubCounterexample and
# QuarticCoreRadiusCase with `decide +kernel`. Pin the now-empty native surface:
# any reintroduction fails. This token check is not an elaboration receipt or
# evidence of Palomar acceptance.
NATIVE_DECIDE_PIN: dict[str, int] = {}
FORBIDDEN_TOKEN_RE = re.compile(r"\bsorry\b|\badmit\b|(?<![\w.])axiom\s+")
NATIVE_DECIDE_RE = re.compile(r"native_decide|\+native\b")


def check_proof_trust() -> tuple[int, int]:
    """Gate the source-only corpus that no Lean job in this repository builds."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from lean_source import lean_code_without_comments_and_strings

    observed: dict[str, int] = {}
    scanned = 0
    for path in sorted(CORPUS.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        scanned += 1
        code = lean_code_without_comments_and_strings(
            path.read_text(encoding="utf-8")
        )
        forbidden = FORBIDDEN_TOKEN_RE.search(code)
        if forbidden:
            raise CorpusError(
                f"{rel} contains {forbidden.group(0).strip()!r}; the research "
                "corpus is published source and must not carry proof holes"
            )
        count = len(NATIVE_DECIDE_RE.findall(code))
        if count:
            observed[rel] = count

    if observed != NATIVE_DECIDE_PIN:
        raise CorpusError(
            "native_decide surface moved; update NATIVE_DECIDE_PIN deliberately. "
            f"expected {NATIVE_DECIDE_PIN}, observed {observed}"
        )
    return scanned, sum(observed.values())


def main() -> int:
    try:
        scanned, native_decide_count = check_proof_trust()
        file_count, result_count, total_bytes = check()
    except CorpusError as exc:
        print(f"check_erdos1041_research_corpus: FAIL: {exc}", file=sys.stderr)
        return 1
    print(
        "check_erdos1041_research_corpus: "
        f"{file_count} content-addressed files, {result_count} activated results, "
        f"{total_bytes} bytes; checkpoint coherent; "
        f"{scanned} Lean sources scanned, no sorry/admit/axiom, "
        f"{native_decide_count} pinned native_decide uses (not Palomar-eligible)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
