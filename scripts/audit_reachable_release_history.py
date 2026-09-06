#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Audit the reachable Git history of the public Plectis release candidate.

This is deliberately a redacted, object-addressed audit.  It enumerates the
objects reachable from every local ref, but never prints blob contents or
secret-like matches.  The resulting report is evidence for the release gate;
it is not permission to rewrite history, delete refs, or force-push.

The report is generated at an anchor commit and may be followed by one commit
that adds the report itself.  The companion validator accepts only that narrow
control-plane delta, so a later source/ref change makes the release decision
stale instead of silently staying green.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
import tarfile
import zipfile
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterable, Iterator, NamedTuple

ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = ROOT / "docs/release/reachable-history-audit.json"
SCHEMA = "plectis.reachable_git_history_trust.v1"
MAX_SINGLE_BLOB_BYTES = 50 * 1024 * 1024
# Payloads above this size are excluded from the two scans that count or
# recognise ordinary document text (address candidates and the custom license
# marker).  Every other content scan in ``_scan_payload`` is deliberately
# unbounded, so this cap is not a licence to skip a large payload entirely.
TEXTUAL_SCAN_CAP_BYTES = 8 * 1024 * 1024

# Progress and reusable-verdict state never enters the release candidate.  The
# location is an environment override, then a sibling of the checkout, then the
# platform temporary directory.  None of those is spelled as a literal path.
STATE_DIR_ENV = "PLECTIS_RELEASE_AUDIT_STATE_DIR"
PROGRESS_PATH_ENV = "PLECTIS_RELEASE_AUDIT_PROGRESS"
PROGRESS_SECONDS_ENV = "PLECTIS_RELEASE_AUDIT_PROGRESS_SECONDS"
CONTENT_CACHE_ENV = "PLECTIS_RELEASE_AUDIT_CONTENT_CACHE"
DEFAULT_PROGRESS_SECONDS = 15.0
STATE_DIR_NAME = "release-audit-state"

# These files are the control plane for this audit.  They are checked by the
# release workflow, but are excluded from the source-history delta comparison
# so the report can be committed immediately after its scan anchor.
CONTROL_PATHS = frozenset(
    {
        "scripts/audit_reachable_release_history.py",
        "scripts/test_reachable_release_history.py",
        "scripts/test_reachable_release_history_environment.py",
        "docs/release/reachable-history-audit.json",
        "docs/release/RELEASE_HISTORY_TRUST.md",
        "docs/primary-sources/redistribution-dispositions.json",
        ".github/workflows/reachable-history-trust.yml",
    }
)

BINARY_SUFFIXES = (
    ".7z",
    ".avi",
    ".avif",
    ".bin",
    ".bmp",
    ".bz2",
    ".crt",
    ".db",
    ".djvu",
    ".gif",
    ".gz",
    ".ico",
    ".jpeg",
    ".jpg",
    ".key",
    ".p12",
    ".pfx",
    ".pdf",
    ".png",
    ".rar",
    ".sqlite",
    ".sqlite3",
    ".tar",
    ".tbz",
    ".tbz2",
    ".tgz",
    ".tif",
    ".tiff",
    ".wav",
    ".webp",
    ".xz",
    ".zip",
    ".zst",
)
ARCHIVE_SUFFIXES = (
    ".7z",
    ".bz2",
    ".gz",
    ".rar",
    ".tar",
    ".tbz",
    ".tbz2",
    ".tgz",
    ".xz",
    ".zip",
    ".zst",
)

PRIVATE_PATH_TERMS = (
    ".codex",
    ".env",
    "ai_workflow",
    "credentials",
    "private",
    "secret",
    "tmp/",
)

_PRIVATE_PATH_MARKERS = (b"/" + b"Users" + b"/", b"/" + b"home" + b"/")
PRIVATE_PATH_RE = re.compile(
    rb"/(?:Users|home)/[A-Za-z0-9._-]+(?:/[A-Za-z0-9._~+%-]+)+"
)
EMAIL_RE = re.compile(rb"\b[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}\b")
PRIVATE_KEY_RE = re.compile(rb"-----BEGIN [A-Z0-9 ]*PRIVATE KEY-----")
AWS_KEY_RE = re.compile(rb"\b(?:AKIA|ASIA)[0-9A-Z]{16}\b")
TOKEN_RE = re.compile(
    rb"\b(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|"
    rb"xox[baprs]-[A-Za-z0-9-]{20,}|glpat-[A-Za-z0-9_-]{20,}|"
    rb"npm_[A-Za-z0-9]{20,}|sk-[A-Za-z0-9]{20,})\b"
)
ASSIGNMENT_RE = re.compile(
    rb"\b(?:AWS_SECRET_ACCESS_KEY|PRIVATE_KEY|API[_-]?KEY|SECRET[_-]?KEY|"
    rb"ACCESS[_-]?TOKEN|AUTH[_-]?TOKEN|PASSWORD)\s*[:=]\s*[\"']?"
    rb"[A-Za-z0-9/+_.=-]{20,}"
)
LICENSE_MARKER_RE = re.compile(rb"LicenseRef-ThirdParty-Source-Artifact")
GIT_CONTEXT_KEYS = frozenset(
    {
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_CEILING_DIRECTORIES",
        "GIT_DISCOVERY_ACROSS_FILESYSTEM",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
    }
)
PYTHON_CONTEXT_KEYS = frozenset(
    {
        "PYTHONHOME",
        "PYTHONPATH",
        "PYTHONUSERBASE",
        "PYTHONSTARTUP",
        "PYTHONBREAKPOINT",
        "PYTHONWARNINGS",
        "PYTHONHASHSEED",
        "PYTHONOPTIMIZE",
        "PYTHONUTF8",
        "PYTHONNOUSERSITE",
        "PYTHONDONTWRITEBYTECODE",
    }
)
LOCALE_KEYS = frozenset({"LC_ALL", "LANG", "LANGUAGE"})


def git_environment() -> dict[str, str]:
    """Run history inspection without caller runtime, Git/config, or replacement state."""
    environment = os.environ.copy()
    for key in list(environment):
        if (
            key.startswith("GIT_CONFIG_")
            or key == "GIT_ASKPASS"
            or key in GIT_CONTEXT_KEYS
            or key in PYTHON_CONTEXT_KEYS
            or key in LOCALE_KEYS
        ):
            environment.pop(key, None)
    environment.update(
        {
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_PAGER": "cat",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_ASKPASS": "/bin/false",
            "LC_ALL": "C.UTF-8",
            "LANG": "C.UTF-8",
            "LANGUAGE": "C.UTF-8",
            "PYTHONHASHSEED": "0",
            "PYTHONNOUSERSITE": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONUTF8": "1",
        }
    )
    return environment


def _git(root: Path, *args: str, input_bytes: bytes | None = None) -> bytes:
    completed = subprocess.run(
        ["git", *args],
        cwd=root,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
        env=git_environment(),
    )
    return completed.stdout


def _git_lines(root: Path, *args: str) -> list[str]:
    return _git(root, *args).decode("utf-8", "surrogateescape").splitlines()


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _redacted_fingerprint(value: bytes) -> str:
    """Return a non-reversible location fingerprint, never the matched value."""
    return "sha256:" + _sha256_bytes(value)


def _scanner_source_fingerprint(root: Path) -> str:
    candidate = root / "scripts/audit_reachable_release_history.py"
    if not candidate.is_file():
        candidate = Path(__file__).resolve()
    try:
        return "sha256:" + _sha256_bytes(candidate.read_bytes())
    except OSError:
        return "unavailable"


def state_directory(root: Path) -> Path:
    """Return a writable, never-tracked directory for progress and cache state."""
    override = os.environ.get(STATE_DIR_ENV, "").strip()
    candidates = [Path(override).expanduser()] if override else []
    candidates.append(root.parent / STATE_DIR_NAME)
    candidates.append(Path(tempfile.gettempdir()) / "plectis-release-audit-state")
    for candidate in candidates:
        try:
            candidate.mkdir(parents=True, exist_ok=True)
            probe = candidate / ".writable"
            probe.write_text("", encoding="utf-8")
            probe.unlink()
            return candidate
        except OSError:
            continue
    return Path(tempfile.mkdtemp(prefix="plectis-release-audit-"))


def progress_path(root: Path, report_path: Path) -> Path:
    """Return the progress sidecar location.

    The default sits beside the report so an operator watching the audit does
    not have to know where the state directory landed.  ``.gitignore`` excludes
    ``docs/release/*.progress.json`` so the sidecar can never reach a commit.
    """
    override = os.environ.get(PROGRESS_PATH_ENV, "").strip()
    if override:
        return Path(override).expanduser()
    sidecar = report_path.with_name(report_path.stem + ".progress.json")
    try:
        sidecar.parent.mkdir(parents=True, exist_ok=True)
        return sidecar
    except OSError:
        return state_directory(root) / "reachable-history-audit.progress.json"


class ProgressReporter:
    """Emit bounded-cadence phase, object, and byte progress.

    A process id and a wall clock are not progress.  Every update names the
    phase, how many objects were requested and completed, how many payload
    bytes have been streamed, and the last object id consumed, so an operator
    can tell a slow run from a stalled one without attaching a debugger.
    """

    def __init__(
        self,
        path: Path | None,
        *,
        stream: object | None = None,
        interval_seconds: float | None = None,
        enabled: bool = True,
    ) -> None:
        self.path = path
        self.stream = stream
        self.enabled = enabled
        if interval_seconds is None:
            try:
                interval_seconds = float(
                    os.environ.get(PROGRESS_SECONDS_ENV, "") or DEFAULT_PROGRESS_SECONDS
                )
            except ValueError:
                interval_seconds = DEFAULT_PROGRESS_SECONDS
        self.interval_seconds = max(0.0, interval_seconds)
        self.started_at = time.monotonic()
        self._last_emit = 0.0
        self.state: dict[str, object] = {
            "phase": "starting",
            "objects_requested": 0,
            "objects_completed": 0,
            "objects_reused_from_cache": 0,
            "bytes_streamed": 0,
            "bytes_requested": 0,
            "last_object_id": "",
            "elapsed_seconds": 0.0,
        }

    def phase(self, name: str, **fields: object) -> None:
        self.state["phase"] = name
        self.state.update(fields)
        self.emit(force=True)

    def advance(self, **fields: object) -> None:
        for key, value in fields.items():
            if isinstance(value, (int, float)) and key.startswith(("objects_", "bytes_")):
                self.state[key] = (self.state.get(key) or 0) + value
            else:
                self.state[key] = value
        self.emit()

    def emit(self, *, force: bool = False) -> None:
        if not self.enabled:
            return
        now = time.monotonic()
        if not force and now - self._last_emit < self.interval_seconds:
            return
        self._last_emit = now
        self.state["elapsed_seconds"] = round(now - self.started_at, 3)
        self.state["updated_at"] = datetime.now(timezone.utc).isoformat()
        line = (
            "audit_reachable_release_history: phase={phase} "
            "objects={objects_completed}/{objects_requested} "
            "cached={objects_reused_from_cache} "
            "streamed_bytes={bytes_streamed} "
            "last_object={last_object_id} "
            "elapsed_s={elapsed_seconds}".format(**self.state)
        )
        target = self.stream if self.stream is not None else sys.stderr
        try:
            print(line, file=target, flush=True)
        except (OSError, ValueError):
            pass
        if self.path is None:
            return
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            temporary = self.path.with_name(self.path.name + ".tmp")
            temporary.write_text(
                json.dumps(self.state, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            os.replace(temporary, self.path)
        except OSError:
            pass

    def snapshot(self) -> dict[str, object]:
        self.state["elapsed_seconds"] = round(time.monotonic() - self.started_at, 3)
        return dict(self.state)


def policy_inputs_digest(root: Path) -> str:
    """Digest every input that can change what a payload scan concludes.

    The scanner source digest already covers the code.  This covers the tuned
    policy surface and the artifact disposition manifest the release decision
    consumes, so a manifest edit cannot be answered from a cached verdict.
    """
    manifest_path = root / "docs/primary-sources/redistribution-dispositions.json"
    try:
        manifest_digest = _sha256_bytes(manifest_path.read_bytes())
    except OSError:
        manifest_digest = "absent"
    payload = {
        "schema": SCHEMA,
        "binary_suffixes": list(BINARY_SUFFIXES),
        "archive_suffixes": list(ARCHIVE_SUFFIXES),
        "private_path_terms": list(PRIVATE_PATH_TERMS),
        "control_paths": sorted(CONTROL_PATHS),
        "max_single_blob_bytes": MAX_SINGLE_BLOB_BYTES,
        "textual_scan_cap_bytes": TEXTUAL_SCAN_CAP_BYTES,
        "patterns": [
            PRIVATE_PATH_RE.pattern.decode("latin-1"),
            EMAIL_RE.pattern.decode("latin-1"),
            PRIVATE_KEY_RE.pattern.decode("latin-1"),
            AWS_KEY_RE.pattern.decode("latin-1"),
            TOKEN_RE.pattern.decode("latin-1"),
            ASSIGNMENT_RE.pattern.decode("latin-1"),
            LICENSE_MARKER_RE.pattern.decode("latin-1"),
        ],
        "manifest_sha256": manifest_digest,
    }
    return "sha256:" + _sha256_bytes(
        json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8")
    )


class ContentScanCache:
    """Reuse payload-derived primitives across interrupted or superseded runs.

    Only payload-derived facts are stored.  Occurrence, path, and ref policy is
    re-derived on every run from the live object/path map, because Git's
    ``rev-list --objects`` names are hints: the same blob can appear at several
    paths and each path is judged separately.  The cache key carries the
    scanner source digest, the policy digest, and the scan mode the paths
    imply, so a policy or code change starts a fresh file instead of answering
    from a verdict reached under different rules.

    An entry is appended only after its payload was fully read and scanned
    without error.  A torn trailing line from a killed run is discarded on
    load, so a partial shard can never be read back as a clean verdict.
    """

    HEADER_KIND = "plectis.reachable_history_content_scan_cache.v1"

    def __init__(self, path: Path | None, key: str, *, writable: bool = True) -> None:
        self.path = path
        self.key = key
        self.writable = writable and path is not None
        self.entries: dict[str, dict[str, object]] = {}
        self.hits = 0
        self.misses = 0
        self.writes = 0
        self.truncated_entries = 0
        self._handle = None
        if path is not None:
            self._load()

    def _load(self) -> None:
        assert self.path is not None
        try:
            raw = self.path.read_text(encoding="utf-8")
        except OSError:
            return
        lines = raw.splitlines()
        trailing_partial = bool(raw) and not raw.endswith("\n")
        if trailing_partial and lines:
            # The run that wrote this file was killed mid-append.
            lines.pop()
            self.truncated_entries += 1
        for index, line in enumerate(lines):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                # Anything after an unreadable line is untrusted.
                self.truncated_entries += 1
                break
            if index == 0:
                if not (
                    isinstance(row, dict)
                    and row.get("kind") == self.HEADER_KIND
                    and row.get("key") == self.key
                ):
                    self.entries.clear()
                    return
                continue
            if not isinstance(row, dict):
                break
            entry_key = row.get("k")
            value = row.get("v")
            if isinstance(entry_key, str) and isinstance(value, dict):
                self.entries[entry_key] = value

    @staticmethod
    def entry_key(object_id: str, scan_mode: str) -> str:
        return f"{object_id}|{scan_mode}"

    def get(self, object_id: str, scan_mode: str) -> dict[str, object] | None:
        value = self.entries.get(self.entry_key(object_id, scan_mode))
        if value is None:
            self.misses += 1
            return None
        self.hits += 1
        return value

    def put(self, object_id: str, scan_mode: str, value: dict[str, object]) -> None:
        key = self.entry_key(object_id, scan_mode)
        self.entries[key] = value
        if not self.writable or self.path is None:
            return
        try:
            if self._handle is None:
                self.path.parent.mkdir(parents=True, exist_ok=True)
                fresh = not self.path.exists() or self.path.stat().st_size == 0
                self._handle = self.path.open("a", encoding="utf-8")
                if fresh:
                    self._handle.write(
                        json.dumps(
                            {"kind": self.HEADER_KIND, "key": self.key},
                            sort_keys=True,
                        )
                        + "\n"
                    )
            self._handle.write(
                json.dumps({"k": key, "v": value}, sort_keys=True, ensure_ascii=False) + "\n"
            )
            self._handle.flush()
            self.writes += 1
        except OSError:
            self.writable = False

    def close(self) -> None:
        if self._handle is not None:
            try:
                self._handle.flush()
                self._handle.close()
            except OSError:
                pass
            self._handle = None

    def statistics(self) -> dict[str, object]:
        return {
            "enabled": self.path is not None,
            "writable": bool(self.writable),
            "location_is_tracked": False,
            "entries_loaded": len(self.entries) - self.writes,
            "hits": self.hits,
            "misses": self.misses,
            "writes": self.writes,
            "discarded_partial_entries": self.truncated_entries,
        }


def open_content_cache(
    root: Path, *, mode: str = "auto", scanner_sha: str | None = None
) -> ContentScanCache:
    """Open the reusable payload-verdict store for this scanner and policy."""
    if mode == "off":
        return ContentScanCache(None, "disabled", writable=False)
    scanner_sha = scanner_sha or _scanner_source_fingerprint(root)
    key = _sha256_bytes(
        json.dumps(
            {"scanner": scanner_sha, "policy": policy_inputs_digest(root)}, sort_keys=True
        ).encode("utf-8")
    )
    directory = state_directory(root)
    path = directory / f"content-scan-cache-{key[:16]}.jsonl"
    return ContentScanCache(path, key, writable=mode != "read-only")


def _ref_class(refname: str) -> str:
    if refname.startswith("refs/heads/"):
        return "branch"
    if refname.startswith("refs/tags/"):
        return "tag"
    if refname.startswith("refs/remotes/"):
        return "remote_tracking"
    if refname.startswith("refs/aiw/rescue/"):
        return "rescue"
    return "other"


def snapshot_refs(root: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for line in _git_lines(root, "for-each-ref", "--format=%(refname)%00%(objectname)"):
        if "\x00" not in line:
            continue
        refname, object_id = line.split("\x00", 1)
        object_type = _git(root, "cat-file", "-t", object_id).decode().strip()
        peeled = _git(root, "rev-parse", f"{refname}^{{commit}}").decode().strip()
        rows.append(
            {
                "ref": refname,
                "object_id": object_id,
                "object_type": object_type,
                "peeled_commit": peeled if re.fullmatch(r"[0-9a-f]{40}", peeled) else "",
                "ref_class": _ref_class(refname),
            }
        )
    return sorted(rows, key=lambda row: row["ref"])


def active_head_ref(root: Path) -> str:
    return _git(root, "symbolic-ref", "--quiet", "--short", "HEAD").decode().strip()


def head_commit(root: Path) -> str:
    return _git(root, "rev-parse", "HEAD").decode().strip()


def _snapshot_tips(ref_rows: list[dict[str, str]]) -> list[str]:
    return sorted(
        {
            row.get("peeled_commit") or row.get("object_id")
            for row in ref_rows
            if row.get("peeled_commit")
            or row.get("object_type") == "commit"
            and row.get("object_id")
        }
    )


def _reachable_ref_objects(
    root: Path, ref_rows: list[dict[str, str]]
) -> tuple[set[str], dict[str, set[str]]]:
    """Walk ref/tag edges that ``rev-list`` normally peels away.

    ``rev-list --objects`` is excellent for commit trees, but it does not
    retain an annotated tag object or a ref that points directly at a blob.
    Those objects are still retrievable from a public clone, so keep their
    object ids and the ref names that make them reachable without retaining
    any object contents.
    """
    object_ids: set[str] = set()
    ref_names_by_object: dict[str, set[str]] = defaultdict(set)
    pending = [
        (row.get("object_id", ""), row.get("ref", ""))
        for row in ref_rows
        if row.get("object_id") and row.get("ref")
    ]
    while pending:
        object_id, ref = pending.pop()
        if not re.fullmatch(r"[0-9a-f]{40}", object_id):
            continue
        ref_names_by_object[object_id].add(ref)
        if object_id in object_ids:
            continue
        object_ids.add(object_id)
        object_type = _git(root, "cat-file", "-t", object_id).decode("ascii", "replace").strip()
        if object_type != "tag":
            continue
        payload = _git(root, "cat-file", "-p", object_id).decode("utf-8", "surrogateescape")
        target = next(
            (
                line.split(maxsplit=1)[1]
                for line in payload.splitlines()
                if line.startswith("object ") and len(line.split(maxsplit=1)) == 2
            ),
            "",
        )
        if re.fullmatch(r"[0-9a-f]{40}", target):
            pending.append((target, ref))
    return object_ids, ref_names_by_object


def reachable_object_paths(
    root: Path, ref_rows: list[dict[str, str]]
) -> tuple[dict[str, set[str]], set[str], dict[str, set[str]]]:
    object_paths: dict[str, set[str]] = defaultdict(set)
    object_ids: set[str] = set()
    ref_object_ids, ref_names_by_object = _reachable_ref_objects(root, ref_rows)
    commit_tips = sorted(
        {
            row["peeled_commit"]
            for row in ref_rows
            if row.get("peeled_commit")
        }
    )
    direct_tips = sorted(
        {
            row["object_id"]
            for row in ref_rows
            if row.get("object_id") and not row.get("peeled_commit")
        }
    )
    def add_rev_list_objects(tips: list[str], propagate_direct_refs: bool) -> None:
        if not tips:
            return
        raw = _git(
            root,
            "rev-list",
            "--objects",
            "--stdin",
            input_bytes=("\n".join(tips) + "\n").encode(),
        )
        inherited_refs: set[str] = set()
        if propagate_direct_refs:
            for tip in tips:
                inherited_refs.update(ref_names_by_object.get(tip, set()))
        for line in raw.decode("utf-8", "surrogateescape").splitlines():
            pieces = line.split(" ", 1)
            object_id = pieces[0]
            if not re.fullmatch(r"[0-9a-f]{40}", object_id):
                continue
            object_ids.add(object_id)
            if propagate_direct_refs:
                ref_names_by_object[object_id].update(inherited_refs)
            if len(pieces) == 2 and pieces[1]:
                object_paths[object_id].add(pieces[1])

    # Keep commit-tree path discovery separate from direct-ref object
    # discovery.  A pathless blob tip must not win an ordering race and hide
    # the same blob's ordinary pathname in a commit tree.  Walk each direct
    # tip independently so a tree ref's aliases cannot leak to another tip's
    # descendants.
    add_rev_list_objects(commit_tips, propagate_direct_refs=False)
    for tip in direct_tips:
        add_rev_list_objects([tip], propagate_direct_refs=True)
    object_ids.update(ref_object_ids)
    return object_paths, object_ids, ref_names_by_object


def object_metadata(root: Path, object_ids: Iterable[str]) -> dict[str, dict[str, int | str]]:
    ordered = sorted(set(object_ids))
    if not ordered:
        return {}
    raw = _git(root, "cat-file", "--batch-check", input_bytes=("\n".join(ordered) + "\n").encode())
    metadata: dict[str, dict[str, int | str]] = {}
    for line in raw.decode("ascii", "replace").splitlines():
        pieces = line.split()
        if len(pieces) != 3 or pieces[1] == "missing":
            continue
        try:
            metadata[pieces[0]] = {"type": pieces[1], "size_bytes": int(pieces[2])}
        except ValueError:
            continue
    return metadata


def _read_exactly(stream, size: int, object_id: str) -> bytes:
    """Read a whole payload or fail loudly.

    ``BufferedReader.read(n)`` may return fewer bytes than asked for.  A short
    read used to be scanned as if it were the whole object, which turns a
    truncated stream into a clean verdict.  Refuse instead.
    """
    chunks: list[bytes] = []
    remaining = size
    while remaining > 0:
        chunk = stream.read(remaining)
        if not chunk:
            raise RuntimeError(
                "reachable-history audit read a truncated payload for object "
                f"{object_id}: {size - remaining} of {size} bytes"
            )
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks) if len(chunks) != 1 else chunks[0]


def object_contents(
    root: Path,
    object_ids: Iterable[str],
    *,
    progress: ProgressReporter | None = None,
) -> Iterator[tuple[str, str, bytes]]:
    ordered = sorted(set(object_ids))
    if not ordered:
        return
    # Stream one ``cat-file --batch`` process. Requesting every object in a
    # single call avoids per-object pipe round trips, but the reply must not be
    # collected into memory: the reachable blob store of this repository
    # decompresses to over 200 GiB because generated navigation projections
    # of 70-100 MB were rewritten hundreds of times, and on 2026-09-04 the
    # audit was SIGKILLed while trying to hold that reply in one bytes
    # object. Feed requests from a helper thread, and consume the reply
    # object by object so peak memory is bounded by the largest single blob.
    process = subprocess.Popen(
        ["git", "cat-file", "--batch"],
        cwd=root,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        env=git_environment(),
    )
    assert process.stdin is not None and process.stdout is not None
    request = ("\n".join(ordered) + "\n").encode("ascii")

    def feed() -> None:
        try:
            process.stdin.write(request)
        except BrokenPipeError:
            pass
        finally:
            try:
                process.stdin.close()
            except BrokenPipeError:
                pass

    feeder = threading.Thread(target=feed, name="cat-file-batch-feeder", daemon=True)
    feeder.start()
    try:
        for object_id in ordered:
            header = process.stdout.readline()
            if not header:
                break
            pieces = header.split()
            if len(pieces) < 3 or pieces[1] not in {b"blob", b"commit", b"tag"}:
                # ``<id> missing`` and non-content types carry no payload.
                continue
            object_type = pieces[1].decode("ascii", "replace")
            try:
                size = int(pieces[2])
            except ValueError:
                continue
            payload = _read_exactly(process.stdout, size, object_id)
            process.stdout.read(1)  # trailing newline after each object
            if progress is not None:
                progress.advance(
                    objects_completed=1,
                    bytes_streamed=len(payload),
                    last_object_id=object_id,
                )
            yield object_id, object_type, payload
    finally:
        try:
            process.stdout.close()
        except OSError:
            pass
        process.wait()
        feeder.join()


def blob_contents(root: Path, object_ids: Iterable[str]) -> Iterator[tuple[str, bytes]]:
    """Yield the legacy blob-only view used by narrow callers."""
    for object_id, object_type, payload in object_contents(root, object_ids):
        if object_type == "blob":
            yield object_id, payload


def _is_control_path(path: str) -> bool:
    return path in CONTROL_PATHS


def _is_binary_path(path: str) -> bool:
    lowered = path.lower()
    return lowered.endswith(BINARY_SUFFIXES)


def _is_archive_path(path: str) -> bool:
    return path.lower().endswith(ARCHIVE_SUFFIXES)


def _looks_like_archive_payload(payload: bytes) -> bool:
    """Recognize archive payloads whose reachable ref has no tree filename."""
    return (
        payload.startswith((b"PK\x03\x04", b"Rar!", b"7z\xbc\xaf\x27\x1c"))
        or payload.startswith(b"\x1f\x8b")
        or payload.startswith((b"BZh", b"\xfd7zXZ\x00", b"\x28\xb5\x2f\xfd"))
        or len(payload) >= 265
        and payload[257:262] == b"ustar"
    )


def _is_primary_artifact_path(path: str) -> bool:
    return path.startswith("docs/primary-sources/") and _is_binary_path(path)


def _load_manifest_paths(root: Path) -> dict[str, dict[str, object]]:
    manifest_path = root / "docs/primary-sources/redistribution-dispositions.json"
    try:
        payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    rows = payload.get("artifacts") if isinstance(payload, dict) else None
    if not isinstance(rows, list):
        return {}
    return {
        str(row["path"]): row
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("path"), str)
    }


def _path_history(root: Path, path: str, ref_rows: list[dict[str, str]]) -> dict[str, object]:
    tips = _snapshot_tips(ref_rows)
    introduced = list(
        dict.fromkeys(
            _git_lines(
                root,
                "log",
                "--full-history",
                "--diff-filter=A",
                "--format=%H",
                *tips,
                "--",
                path,
            )
        )
    )
    removed = list(
        dict.fromkeys(
            _git_lines(
                root,
                "log",
                "--full-history",
                "--diff-filter=D",
                "--format=%H",
                *tips,
                "--",
                path,
            )
        )
    )
    introduced_objects: dict[str, list[str]] = defaultdict(list)
    for commit in introduced:
        resolved = _git(root, "rev-parse", f"{commit}:{path}").decode().strip()
        if re.fullmatch(r"[0-9a-f]{40}", resolved):
            introduced_objects[resolved].append(commit)
    removed_objects: dict[str, list[str]] = defaultdict(list)
    for commit in removed:
        parents = _git_lines(root, "rev-list", "--parents", "-n", "1", commit)
        if not parents:
            continue
        parent_commits = parents[0].split()[1:]
        for parent in parent_commits:
            resolved = _git(root, "rev-parse", f"{parent}:{path}").decode().strip()
            if re.fullmatch(r"[0-9a-f]{40}", resolved):
                removed_objects[resolved].append(commit)
    return {
        "introducing_commits": introduced,
        "removing_commits": removed,
        "object_commits": {
            key: sorted(set(value))
            for key, value in sorted(introduced_objects.items())
        },
        "introduced_object_commits": {
            key: sorted(set(value)) for key, value in sorted(introduced_objects.items())
        },
        "removed_object_commits": {
            key: sorted(set(value)) for key, value in sorted(removed_objects.items())
        },
    }


_REF_MEMBERSHIP_CACHE: dict[tuple[str, str], tuple[list[str], dict[str, int]]] = {}


def _ref_membership(root: Path, ref_rows: list[dict[str, str]]) -> tuple[list[str], dict[str, int]]:
    """Build, once per ref set, a bitmask of which refs contain each commit.

    ``for-each-ref --contains <commit>`` answers one commit per full
    repository walk.  With tens of thousands of findings that walk repeated
    per commit was the audit's wall-clock wall (hours, after the payload
    stream itself had finished).  One ``rev-list`` per ref, streamed line by
    line, gives the same reachability relation as a ``commit -> bitmask``
    table: the refs whose tip reaches the commit are exactly the refs
    ``for-each-ref --contains`` would list, tags peeled to their commits.
    Refs that do not peel to a commit contribute nothing, as before.
    """
    names = sorted(
        {
            row["ref"]
            for row in ref_rows
            if row.get("ref", "").startswith("refs/") and row.get("peeled_commit")
        }
    )
    key = (str(root), hashlib.sha256("\n".join(names).encode()).hexdigest())
    cached = _REF_MEMBERSHIP_CACHE.get(key)
    if cached is not None:
        return cached
    membership: dict[str, int] = {}
    for index, ref in enumerate(names):
        bit = 1 << index
        process = subprocess.Popen(
            ["git", "rev-list", ref, "--"],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            env=git_environment(),
        )
        assert process.stdout is not None
        for line in process.stdout:
            commit = line.strip().decode("ascii", "replace")
            if commit:
                membership[commit] = membership.get(commit, 0) | bit
        process.wait()
    _REF_MEMBERSHIP_CACHE[key] = (names, membership)
    return names, membership


def _refs_containing_commits(root: Path, commits: Iterable[str], ref_rows: list[dict[str, str]]) -> list[str]:
    """Return the refs containing the requested commits.

    Same relation as ``for-each-ref --contains`` per commit, served from the
    once-built membership table in ``_ref_membership`` so the cost is one
    walk per ref rather than one walk per finding.
    """
    names, membership = _ref_membership(root, ref_rows)
    mask = 0
    for commit in sorted(set(commits)):
        if not re.fullmatch(r"[0-9a-f]{40}", commit):
            continue
        mask |= membership.get(commit, 0)
    return sorted(name for index, name in enumerate(names) if mask & (1 << index))


def _ref_rows_by_name(ref_rows: list[dict[str, str]]) -> dict[str, dict[str, str]]:
    return {row["ref"]: row for row in ref_rows}


def _object_record(
    root: Path,
    object_id: str,
    paths: list[str],
    metadata: dict[str, dict[str, int | str]],
    history_by_path: dict[str, dict[str, object]],
    ref_rows: list[dict[str, str]],
    ref_names_by_object: dict[str, set[str]],
) -> dict[str, object]:
    path_histories: list[dict[str, object]] = []
    for path in paths:
        if path.startswith("<reachable-ref:"):
            continue
        history = history_by_path.get(path)
        if history is None:
            history = _path_history(root, path, ref_rows)
            history_by_path[path] = history
        path_histories.append(history)
    object_commits: set[str] = set()
    introducing: set[str] = set()
    removing: set[str] = set()
    for history in path_histories:
        object_commits.update(history.get("object_commits", {}).get(object_id, []))
        introducing.update(history.get("introduced_object_commits", {}).get(object_id, []))
        removing.update(history.get("removed_object_commits", {}).get(object_id, []))
    if not object_commits:
        for history in path_histories:
            object_commits.update(history.get("introducing_commits", []))
    reachable_ref_names = set(ref_names_by_object.get(object_id, set()))
    reachable_ref_names.update(_refs_containing_commits(root, object_commits, ref_rows))
    if metadata.get(object_id, {}).get("type") == "commit":
        reachable_ref_names.update(_refs_containing_commits(root, [object_id], ref_rows))
    ref_index = _ref_rows_by_name(ref_rows)
    return {
        "object_id": object_id,
        "paths": paths,
        "object_type": metadata.get(object_id, {}).get("type", "unknown"),
        "size_bytes": metadata.get(object_id, {}).get("size_bytes", -1),
        "introducing_commits": sorted(introducing),
        "removing_commits": sorted(removing),
        "object_history_commits": sorted(object_commits),
        "reachable_refs": [
            {"ref": ref, "ref_class": ref_index.get(ref, {}).get("ref_class", _ref_class(ref))}
            for ref in sorted(reachable_ref_names)
        ],
        "retrievable_from_reachable_ref": bool(reachable_ref_names),
    }


def _bind_finding_context(
    findings: list[dict[str, object]], context: dict[str, object]
) -> None:
    """Attach object history and ref reachability to every redacted finding."""
    for finding in findings:
        for key in (
            "object_type",
            "size_bytes",
            "introducing_commits",
            "removing_commits",
            "object_history_commits",
            "reachable_refs",
            "retrievable_from_reachable_ref",
        ):
            finding[key] = context.get(key)


def _annotate_current_head_exposure(
    findings: list[dict[str, object]], current_tracked_paths: set[str]
) -> None:
    """Mark whether each object-backed finding names a path in the scan tip."""
    for finding in findings:
        if "current_head_exposure" in finding:
            continue
        paths = finding.get("paths", [])
        if not isinstance(paths, list):
            paths = []
        finding["current_head_exposure"] = any(
            isinstance(path, str)
            and not path.startswith("<reachable-ref:")
            and path in current_tracked_paths
            for path in paths
        )


class ScanMode(NamedTuple):
    """Every payload-scan parameter that the object's paths decide."""

    scan_textual_payload: bool
    archive_branches: tuple[str, ...]

    def digest(self) -> str:
        return f"t{int(self.scan_textual_payload)}|a:{','.join(self.archive_branches)}"


def _archive_branch_labels(paths: list[str]) -> tuple[str, ...]:
    """Name the archive parser branches ``_archive_findings`` would take.

    ``zip`` and ``tar`` are decided by the path suffix.  ``magic`` marks a
    pathless direct-ref object whose branch is decided by the payload's leading
    bytes, so the branch it resolved to is recorded alongside its rows.
    """
    labels: set[str] = set()
    archive_paths = [path for path in paths if _is_archive_path(path)]
    pathless = [path for path in paths if path.startswith("<reachable-ref:")]
    for path in archive_paths:
        labels.add("zip" if path.lower().endswith(".zip") else "tar")
    if not archive_paths and pathless:
        labels.add("magic")
    return tuple(sorted(labels))


def scan_mode_for(
    paths: list[str], object_type: str, size_bytes: int
) -> ScanMode:
    """Derive the scan parameters from metadata and paths, before any payload.

    This mirrors, exactly, the decisions ``build_audit`` used to make only once
    a payload was already in memory.  Deriving them from ``--batch-check`` type
    and size plus the path map is what lets the audit decline to request a
    payload it would never consult.
    """
    if object_type == "blob":
        binary_like = any(_is_binary_path(path) for path in paths)
        textual = not binary_like and size_bytes <= TEXTUAL_SCAN_CAP_BYTES
        branches = _archive_branch_labels(paths)
    else:
        textual = size_bytes <= TEXTUAL_SCAN_CAP_BYTES
        branches = ()
    return ScanMode(textual, branches)


def _archive_member_rows(payload: bytes, branch: str) -> list[list[object]]:
    """Parse one archive branch into redacted member rows.

    ``archive_parse_failure`` carries the offending path in the original, so its
    fingerprint is path-derived; it is stored with a null name and the live path
    is substituted when the finding is assembled.
    """

    def unsafe_name(name: str) -> bool:
        normalized = name.replace("\\", "/")
        return (
            normalized.startswith("/")
            or "../" in normalized
            or normalized == ".."
            or "/.." in normalized
        )

    rows: list[list[object]] = []
    try:
        if branch == "zip":
            with zipfile.ZipFile(io.BytesIO(payload)) as archive:
                for member in archive.infolist():
                    if unsafe_name(member.filename):
                        rows.append(["unsafe_member_name", member.filename])
                    if (member.external_attr >> 16) & 0o170000 == 0o120000:
                        rows.append(["symlink_member", member.filename])
        else:
            with tarfile.open(fileobj=io.BytesIO(payload), mode="r:*") as archive:
                for member in archive.getmembers():
                    if unsafe_name(member.name):
                        rows.append(["unsafe_member_name", member.name])
                    if member.issym() or member.islnk():
                        rows.append(["link_member", member.name])
    except (OSError, EOFError, tarfile.TarError, zipfile.BadZipFile):
        # A malformed archive is a review finding, not a parser crash.  The
        # outer object/path identity still binds the remediation decision.
        return [["archive_parse_failure", None]]
    return rows


def _match_primitive(matches: list[bytes]) -> dict[str, object]:
    return {
        "count": len(matches),
        "fingerprints": sorted({_redacted_fingerprint(match) for match in matches})[:16],
    }


def _scan_payload(payload: bytes, mode: ScanMode) -> dict[str, object]:
    """Reduce a payload to the redacted primitives every finding is built from.

    Nothing here depends on the object's paths or refs, so the result is a
    property of the immutable Git object under a fixed scanner and policy and
    can be reused by a later run.  Path, occurrence, and ref judgements stay in
    ``_findings_from_primitives`` and are redone on every run.
    """
    private_keys = PRIVATE_KEY_RE.findall(payload) if b"PRIVATE KEY" in payload else []
    aws_keys = AWS_KEY_RE.findall(payload) if b"AKIA" in payload or b"ASIA" in payload else []
    tokens = TOKEN_RE.findall(payload) if any(
        marker in payload
        for marker in (
            b"ghp_",
            b"gho_",
            b"ghs_",
            b"ghr_",
            b"ghu_",
            b"github_pat_",
            b"xox",
            b"glpat-",
            b"npm_",
            b"sk-",
        )
    ) else []
    assignment_markers = (
        b"AWS_SECRET_ACCESS_KEY",
        b"PRIVATE_KEY",
        b"API_KEY",
        b"API-KEY",
        b"SECRET_KEY",
        b"SECRET-KEY",
        b"ACCESS_TOKEN",
        b"ACCESS-TOKEN",
        b"AUTH_TOKEN",
        b"AUTH-TOKEN",
        b"PASSWORD",
    )
    # A path suffix is untrusted: a binary-looking blob can still contain a
    # credential assignment, while a normal-looking path can contain one
    # without using a secret-related name.  Scan the bounded marker set in
    # every payload and retain only redacted fingerprints in the report.
    assignments = (
        [match.group(0) for match in ASSIGNMENT_RE.finditer(payload)]
        if any(marker in payload for marker in assignment_markers)
        else []
    )
    path_matches = (
        PRIVATE_PATH_RE.findall(payload)
        if any(marker in payload for marker in _PRIVATE_PATH_MARKERS)
        else []
    )
    primitives: dict[str, object] = {
        "size_bytes": len(payload),
        "private_key_material_marker": _match_primitive(private_keys),
        "aws_access_key_marker": _match_primitive(aws_keys),
        "credential_token_marker": _match_primitive(tokens),
        "credential_assignment_marker": _match_primitive(assignments),
        "absolute_private_filesystem_path": _match_primitive(path_matches),
        # An address is a privacy review candidate, not an automatic release
        # blocker.  Count likely address separators without retaining or
        # printing the address text; the blob/path identity remains the
        # evidence binding.
        "email_candidate_count": (
            payload.count(b"@") if mode.scan_textual_payload else 0
        ),
        "license_marker": bool(
            mode.scan_textual_payload and LICENSE_MARKER_RE.pattern in payload
        ),
        "looks_like_archive_payload": _looks_like_archive_payload(payload),
        "starts_with_pk": payload.startswith(b"PK\x03\x04"),
    }
    archive_rows: dict[str, object] = {}
    magic_branch: str | None = None
    for branch in mode.archive_branches:
        if branch == "magic":
            if not primitives["looks_like_archive_payload"]:
                continue
            magic_branch = "zip" if primitives["starts_with_pk"] else "tar"
            archive_rows[magic_branch] = _archive_member_rows(payload, magic_branch)
        else:
            archive_rows.setdefault(branch, _archive_member_rows(payload, branch))
    primitives["archive_rows"] = archive_rows
    primitives["magic_branch"] = magic_branch
    return primitives


def _findings_from_primitives(
    object_id: str,
    paths: list[str],
    primitives: dict[str, object],
    mode: ScanMode,
) -> tuple[
    list[dict[str, object]],
    list[dict[str, object]],
    list[dict[str, object]],
    list[dict[str, object]],
]:
    """Judge one object's live paths against reusable payload primitives."""
    security: list[dict[str, object]] = []
    privacy: list[dict[str, object]] = []
    license_rows: list[dict[str, object]] = []
    archives: list[dict[str, object]] = []

    def add(target: list[dict[str, object]], kind: str, count: int, fingerprints: list[str]) -> None:
        if not count:
            return
        target.append(
            {
                "kind": kind,
                "object_id": object_id,
                "paths": paths,
                "match_count": count,
                "redacted_fingerprints": list(fingerprints),
            }
        )

    for kind in (
        "private_key_material_marker",
        "aws_access_key_marker",
        "credential_token_marker",
        "credential_assignment_marker",
    ):
        row = primitives.get(kind) or {}
        add(security, kind, int(row.get("count", 0)), list(row.get("fingerprints", [])))
    row = primitives.get("absolute_private_filesystem_path") or {}
    add(
        privacy,
        "absolute_private_filesystem_path",
        int(row.get("count", 0)),
        list(row.get("fingerprints", [])),
    )
    email_count = int(primitives.get("email_candidate_count") or 0)
    if email_count:
        add(
            privacy,
            "email_address_candidate",
            email_count,
            [_redacted_fingerprint(b"email-candidate")],
        )
    if primitives.get("license_marker"):
        license_rows.append(
            {
                "kind": "custom_third_party_license_marker",
                "object_id": object_id,
                "paths": paths,
                "interpretation": "label_is_not_redistribution_permission",
            }
        )

    archive_rows = primitives.get("archive_rows") or {}
    magic_branch = primitives.get("magic_branch")
    archive_paths = [path for path in paths if _is_archive_path(path)]
    if not archive_paths and any(path.startswith("<reachable-ref:") for path in paths):
        if primitives.get("looks_like_archive_payload"):
            archive_paths = paths
    for path in archive_paths:
        if _is_archive_path(path):
            branch = "zip" if path.lower().endswith(".zip") else "tar"
        else:
            branch = magic_branch or ("zip" if primitives.get("starts_with_pk") else "tar")
        member_rows = archive_rows.get(branch)
        if member_rows is None:
            continue
        resolved = [
            (str(kind), path if name is None else str(name)) for kind, name in member_rows
        ]
        if not resolved:
            continue
        archives.append(
            {
                "kind": "unsafe_archive",
                "object_id": object_id,
                "paths": paths,
                "member_finding_count": len(resolved),
                "member_finding_kinds": sorted({kind for kind, _ in resolved}),
                "redacted_member_fingerprints": sorted(
                    {
                        _redacted_fingerprint(name.encode("utf-8", "surrogateescape"))
                        for _, name in resolved
                    }
                )[:32],
            }
        )
    return security, privacy, license_rows, archives


def _content_findings(
    object_id: str,
    paths: list[str],
    payload: bytes,
    *,
    scan_textual_payload: bool | None = None,
) -> tuple[list[dict[str, object]], list[dict[str, object]], list[dict[str, object]]]:
    """Legacy content-finding view, retained for narrow callers and fixtures."""
    # A pathless direct-ref object is not evidence of binary content.  Treating
    # its synthetic ``<reachable-ref:...>`` label as binary would skip bounded
    # textual scans and could hide a license marker in a direct-ref blob.
    if scan_textual_payload is None:
        binary_like = any(_is_binary_path(path) for path in paths)
        scan_textual_payload = (
            not binary_like and len(payload) <= TEXTUAL_SCAN_CAP_BYTES
        )
    mode = ScanMode(bool(scan_textual_payload), ())
    security, privacy, license_rows, _ = _findings_from_primitives(
        object_id, paths, _scan_payload(payload, mode), mode
    )
    return security, privacy, license_rows


def _archive_findings(object_id: str, paths: list[str], payload: bytes) -> list[dict[str, object]]:
    """Legacy archive-finding view, retained for narrow callers and fixtures."""
    mode = ScanMode(True, _archive_branch_labels(paths))
    _, _, _, archives = _findings_from_primitives(
        object_id, paths, _scan_payload(payload, mode), mode
    )
    return archives


def _private_path_findings(object_id: str, paths: list[str]) -> list[dict[str, object]]:
    findings: list[dict[str, object]] = []
    for path in paths:
        lowered = path.lower()
        matched_terms = sorted(term for term in PRIVATE_PATH_TERMS if term in lowered)
        if matched_terms:
            findings.append(
                {
                    "kind": "private_or_working_path",
                    "object_id": object_id,
                    "path": path,
                    "paths": [path],
                    "matched_terms": matched_terms,
                    "interpretation": "historical_path_is_retrievable_and_requires_operator_privacy_review",
                }
            )
    return findings


def _private_ref_findings(ref_rows: list[dict[str, str]]) -> list[dict[str, object]]:
    """Treat privacy-bearing ref names as reachable release evidence."""
    findings: list[dict[str, object]] = []
    for row in ref_rows:
        ref = row.get("ref", "")
        lowered = ref.lower()
        matched_terms = sorted(term for term in PRIVATE_PATH_TERMS if term in lowered)
        if not matched_terms:
            continue
        findings.append(
            {
                "kind": "private_or_working_ref",
                "object_id": row.get("object_id", ""),
                "path": ref,
                "reachable_refs": [
                    {
                        "ref": ref,
                        "ref_class": row.get("ref_class", _ref_class(ref)),
                    }
                ],
                "matched_terms": matched_terms,
                "interpretation": "historical ref name is retrievable and requires operator privacy review",
            }
        )
    return findings


def _missing_ref_findings(
    ref_rows: list[dict[str, str]],
    metadata: dict[str, dict[str, int | str]],
    head_ref: str,
) -> list[dict[str, object]]:
    """Make refs whose object is absent an explicit release-blocking finding."""
    findings: list[dict[str, object]] = []
    for row in ref_rows:
        ref = row.get("ref", "")
        object_id = row.get("object_id", "")
        if (
            not ref
            or not re.fullmatch(r"[0-9a-f]{40}", object_id)
            or object_id in metadata
        ):
            continue
        findings.append(
            {
                "kind": "missing_reachable_ref_object",
                "object_id": object_id,
                "path": ref,
                "paths": [f"<reachable-ref:{ref}>"],
                "object_type": "missing",
                "size_bytes": None,
                "introducing_commits": [],
                "removing_commits": [],
                "object_history_commits": [],
                "reachable_refs": [
                    {
                        "ref": ref,
                        "ref_class": row.get("ref_class", _ref_class(ref)),
                    }
                ],
                "retrievable_from_reachable_ref": False,
                "current_head_exposure": ref == head_ref,
                "interpretation": (
                    "reachable ref names an object absent from the local object database; "
                    "public ref integrity cannot be established"
                ),
            }
        )
    return findings


def _current_tracked_paths(root: Path) -> set[str]:
    return set(_git_lines(root, "ls-tree", "-r", "--name-only", "HEAD"))


def _tracked_paths_at(root: Path, commit: str) -> set[str]:
    return set(_git_lines(root, "ls-tree", "-r", "--name-only", commit))


def _ref_changes(start: list[dict[str, str]], end: list[dict[str, str]]) -> list[dict[str, object]]:
    start_by_ref = {row["ref"]: row for row in start}
    end_by_ref = {row["ref"]: row for row in end}
    changes: list[dict[str, object]] = []
    for ref in sorted(set(start_by_ref) | set(end_by_ref)):
        before = start_by_ref.get(ref)
        after = end_by_ref.get(ref)
        if before == after:
            continue
        changes.append(
            {
                "ref": ref,
                "start": before,
                "end": after,
            }
        )
    return changes


def _build_remediation(
    ref_rows: list[dict[str, str]],
    artifact_records: list[dict[str, object]],
    release_blockers: list[dict[str, object]],
    ref_changes: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    refs = sorted({row["ref"] for row in ref_rows})
    selected_objects: list[dict[str, object]] = []
    for record in artifact_records:
        selected_objects.append(
            {
                "object_id": record.get("object_id"),
                "paths": record.get("paths", []),
                "object_type": record.get("object_type"),
                "size_bytes": record.get("size_bytes"),
                "introducing_commits": record.get("introducing_commits", []),
                "removing_commits": record.get("removing_commits", []),
                "object_history_commits": record.get("object_history_commits", []),
                "reachable_refs": record.get("reachable_refs", []),
                "retrievable_from_reachable_ref": record.get(
                    "retrievable_from_reachable_ref"
                ),
                "current_head_exposure": record.get("current_head_exposure"),
                "manifest_disposition": record.get("manifest_disposition"),
                "manifest_sha256": record.get("manifest_sha256"),
                "selection_reason": "historical_third_party_artifact",
                "governing_disposition": record.get("manifest_disposition"),
            }
        )
    for blocker in release_blockers:
        if blocker.get("kind") in {
            "historical_secret",
            "absolute_private_filesystem_path",
            "private_or_working_path",
            "private_or_working_ref",
            "missing_reachable_ref_object",
            "unsafe_archive",
            "oversized_blob",
            "unattributed_reachable_blob",
            "historical_license_marker",
            "unmanifested_primary_source_binary",
        }:
            selected_objects.append(
                {
                    "object_id": blocker.get("object_id"),
                    "paths": blocker.get("paths", [blocker.get("path")] if blocker.get("path") else []),
                    "ref": (
                        blocker.get("path")
                        if blocker.get("kind") == "private_or_working_ref"
                        else None
                    ),
                    "object_type": blocker.get("object_type"),
                    "size_bytes": blocker.get("size_bytes"),
                    "introducing_commits": blocker.get("introducing_commits", []),
                    "removing_commits": blocker.get("removing_commits", []),
                    "object_history_commits": blocker.get("object_history_commits", []),
                    "reachable_refs": blocker.get("reachable_refs", []),
                    "retrievable_from_reachable_ref": blocker.get(
                        "retrievable_from_reachable_ref"
                    ),
                    "current_head_exposure": blocker.get("current_head_exposure"),
                    "selection_reason": blocker.get("kind"),
                    "manifest_disposition": blocker.get("manifest_disposition"),
                    "governing_disposition": blocker.get(
                        "disposition", blocker.get("manifest_disposition")
                    ),
                }
            )
    return {
        "decision_id": "RHT-2026-08-27-001",
        "status": "operator_approval_required_before_any_outbound_mutation",
        "protected_identities": [
            "standalone repository identity: w cook04/plectis-lean-erdos249-257",
            "all current branch, tag, remote-tracking, and rescue ref names in this report",
        ],
        "protected_refs": refs or [row["ref"] for row in ref_rows],
        "ref_changes_during_scan": ref_changes or [],
        "object_path_selection": selected_objects,
        "expected_commit_tag_receipt_consequences": [
            "A history rewrite or ref-prune would change commit IDs for affected descendants and may invalidate existing tags.",
            "The current audit report and release receipt must be regenerated at the post-remediation exact commit.",
            "The public candidate must remain blocked until a fresh all-ref scan proves no prohibited reachable object remains.",
        ],
        "collaborator_and_fork_coordination": [
            "Notify every collaborator or fork owner before rewriting shared history.",
            "Freeze inbound pushes while protected refs are rewritten and require fresh clones or explicit ref migration instructions.",
            "Do not delete recovery refs until the operator confirms the verified post-remediation audit and rollback window has expired.",
        ],
        "verification_commands": [
            "git fsck --full --no-reflogs --connectivity-only",
            "git rev-list --objects --all",
            "python3 scripts/audit_reachable_release_history.py --write-report",
            "python3 scripts/test_reachable_release_history.py --check",
            "python3 scripts/test_reachable_release_history.py --release-gate",
        ],
        "rollback_material": [
            "Preserve the pre-remediation ref/object mapping and all recovery refs named in this report.",
            "Create an operator-controlled bundle before any rewrite: git bundle create <operator-private-recovery>.bundle --all.",
            "Rollback is a ref restoration from the protected recovery mapping; do not erase the bundle or recovery refs as part of this agent turn.",
        ],
        "outbound_mutation_requiring_explicit_operator_approval": [
            "git filter-repo/filter-branch or equivalent history rewrite",
            "deleting or moving refs/tags",
            "force-pushing rewritten branches/tags to origin",
            "publishing or announcing a replacement release",
        ],
        "agent_action_taken": "No history rewrite, ref deletion, force-push, publication, or recovery-evidence removal was performed.",
    }


def _manifest_artifact_object_ids(
    path: str,
    object_paths: dict[str, set[str]],
    metadata: dict[str, dict[str, int | str]],
    history: dict[str, object],
) -> list[str]:
    """Retain manifest-path blobs even when Git reports a later renamed path."""
    object_ids = {
        object_id
        for object_id, paths in object_paths.items()
        if path in paths and metadata.get(object_id, {}).get("type") == "blob"
    }
    object_commits = history.get("object_commits", {})
    if isinstance(object_commits, dict):
        object_ids.update(
            object_id
            for object_id in object_commits
            if isinstance(object_id, str)
            and re.fullmatch(r"[0-9a-f]{40}", object_id)
            and metadata.get(object_id, {}).get("type") == "blob"
        )
    return sorted(object_ids)


class ContentScanTarget(NamedTuple):
    """One object's scan decision, derived before any payload is requested."""

    object_id: str
    object_type: str
    size_bytes: int
    paths: tuple[str, ...]
    mode: ScanMode
    required: bool
    reason: str
    lazy_commit_ref_binding: bool


def content_scan_targets(
    metadata: dict[str, dict[str, int | str]],
    object_paths: dict[str, set[str]],
    ref_names_by_object: dict[str, set[str]],
) -> dict[str, ContentScanTarget]:
    """Decide, from ``--batch-check`` metadata and the path map alone, which
    payloads can influence a finding.

    The scan loop used to make these decisions with the payload already in
    memory, so every reachable blob, commit, and tag was decompressed and
    shipped through the ``cat-file --batch`` pipe even when the object was
    dropped on the next line.  Type and size are known from ``--batch-check``
    before any payload is requested, and the path map is known from
    ``rev-list --objects``, so the same decisions can be taken first.

    An object is not required only when the scan loop would have discarded it
    without consulting its payload: every path it carries is a control path, or
    it has no path and no ref that would give it a synthetic one.  Size alone
    never excludes an object, because the credential, private-key, token,
    assignment, and absolute-path scans in ``_scan_payload`` are deliberately
    unbounded; only address counting and the license marker respect
    ``TEXTUAL_SCAN_CAP_BYTES``.
    """
    targets: dict[str, ContentScanTarget] = {}
    for object_id in sorted(metadata):
        details = metadata[object_id]
        object_type = str(details.get("type", ""))
        if object_type not in {"blob", "commit", "tag"}:
            continue
        try:
            size_bytes = int(details.get("size_bytes", -1))
        except (TypeError, ValueError):
            size_bytes = -1
        raw_paths = object_paths.get(object_id)
        paths = sorted(path for path in (raw_paths or ()) if not _is_control_path(path))
        lazy_commit_ref_binding = False
        reason = ""
        if not paths:
            if raw_paths:
                reason = "control_path_only"
            else:
                paths = [
                    f"<reachable-ref:{ref}>"
                    for ref in sorted(ref_names_by_object.get(object_id, set()))
                ]
                if not paths and object_type == "commit":
                    paths = ["<reachable-ref:commit-object>"]
                    lazy_commit_ref_binding = True
                if not paths:
                    reason = "unbound_object"
        mode = scan_mode_for(paths, object_type, size_bytes)
        if reason:
            targets[object_id] = ContentScanTarget(
                object_id, object_type, size_bytes, (), mode, False, reason, False
            )
            continue
        if any(path.startswith("<reachable-ref:") for path in paths):
            reason = "pathless_direct_ref_object"
        elif mode.archive_branches:
            reason = "archive_suffixed_path"
        elif mode.scan_textual_payload:
            reason = "textual_scannable_payload"
        else:
            reason = "unbounded_marker_scan"
        targets[object_id] = ContentScanTarget(
            object_id,
            object_type,
            size_bytes,
            tuple(paths),
            mode,
            True,
            reason,
            lazy_commit_ref_binding,
        )
    return targets


def build_audit(
    root: Path = ROOT,
    *,
    progress: ProgressReporter | None = None,
    cache: ContentScanCache | None = None,
    payload_selection: str = "selective",
) -> dict[str, object]:
    if progress is not None:
        progress.phase("refs")
    refs = snapshot_refs(root)
    scan_commit = head_commit(root)
    head_ref = active_head_ref(root)
    if progress is not None:
        progress.phase("object_discovery")
    object_paths, object_ids, ref_names_by_object = reachable_object_paths(root, refs)
    if progress is not None:
        progress.phase("object_metadata", reachable_object_count=len(object_ids))
    metadata = object_metadata(root, object_ids)
    manifest = _load_manifest_paths(root)
    all_paths = sorted({path for paths in object_paths.values() for path in paths})
    binary_paths = sorted(path for path in all_paths if _is_binary_path(path) and not _is_control_path(path))
    primary_paths = sorted(path for path in binary_paths if _is_primary_artifact_path(path))
    if progress is not None:
        progress.phase(
            "artifact_path_history",
            paths_to_walk=len(set(primary_paths) | set(manifest)),
        )
    history_by_path = {
        path: _path_history(root, path, refs)
        for path in sorted(set(primary_paths) | set(manifest))
    }
    current_tracked_paths = _tracked_paths_at(root, scan_commit)
    missing_ref_findings = _missing_ref_findings(refs, metadata, head_ref)

    artifact_records: list[dict[str, object]] = []
    for path, manifest_row in sorted(manifest.items()):
        object_ids_for_path = _manifest_artifact_object_ids(
            path,
            object_paths,
            metadata,
            history_by_path.get(path, {}),
        )
        for object_id in object_ids_for_path:
            record = _object_record(
                root, object_id, [path], metadata, history_by_path, refs, ref_names_by_object
            )
            record["manifest_disposition"] = manifest_row.get("disposition")
            record["manifest_sha256"] = manifest_row.get("sha256")
            record["current_head_exposure"] = path in current_tracked_paths
            record["governing_interpretation"] = "link_and_digest_only does not remove a reachable historical blob"
            artifact_records.append(record)

    security_findings: list[dict[str, object]] = []
    privacy_findings: list[dict[str, object]] = []
    license_findings: list[dict[str, object]] = []
    archive_findings: list[dict[str, object]] = []
    scanned_blob_ids = sorted(
        object_id for object_id, details in metadata.items() if details.get("type") == "blob"
    )
    scanned_content_ids = sorted(
        object_id
        for object_id, details in metadata.items()
        if details.get("type") in {"blob", "commit", "tag"}
    )
    targets = content_scan_targets(metadata, object_paths, ref_names_by_object)
    required_ids = [object_id for object_id, target in targets.items() if target.required]
    primitives_by_id: dict[str, dict[str, object]] = {}
    if cache is not None and payload_selection != "full":
        for object_id in required_ids:
            hit = cache.get(object_id, targets[object_id].mode.digest())
            if hit is not None:
                primitives_by_id[object_id] = hit
    if payload_selection == "full":
        # The legacy request set: every reachable blob, commit, and tag.  Kept
        # so a fixture can prove the selective path reaches the same decision.
        requested_ids = list(scanned_content_ids)
    else:
        requested_ids = [
            object_id for object_id in required_ids if object_id not in primitives_by_id
        ]
    requested_bytes = sum(int(metadata[object_id]["size_bytes"]) for object_id in requested_ids)
    if progress is not None:
        progress.phase(
            "content_scan",
            objects_requested=len(requested_ids),
            bytes_requested=requested_bytes,
            objects_reused_from_cache=len(primitives_by_id),
        )
    for object_id, _object_type, payload in object_contents(
        root, requested_ids, progress=progress
    ):
        target = targets.get(object_id)
        if target is None or not target.required:
            continue
        primitives = _scan_payload(payload, target.mode)
        primitives_by_id[object_id] = primitives
        if cache is not None:
            # Reached only after the whole payload was read and scanned without
            # error, so an interrupted object never lands as a clean verdict.
            cache.put(object_id, target.mode.digest(), primitives)
    if progress is not None:
        # Binding an object's history and ref reachability costs one repository
        # walk per commit, so this phase can outlast the payload stream.  It
        # gets its own counter for exactly that reason.
        progress.phase(
            "content_judgement",
            objects_to_judge=len(primitives_by_id),
            objects_judged=0,
        )
    for object_id in sorted(primitives_by_id):
        if progress is not None:
            progress.advance(objects_judged=1, last_object_id=object_id)
        target = targets[object_id]
        object_type = target.object_type
        paths = list(target.paths)
        lazy_commit_ref_binding = target.lazy_commit_ref_binding
        security, privacy, licenses, archives = _findings_from_primitives(
            object_id, paths, primitives_by_id[object_id], target.mode
        )
        if object_type != "blob":
            archives = []
        finding_rows = (security, privacy, licenses, archives)
        if any(finding_rows):
            if lazy_commit_ref_binding:
                reachable_refs = _refs_containing_commits(root, [object_id], refs)
                paths = [
                    f"<reachable-ref:{ref}>"
                    for ref in sorted(reachable_refs)
                ] or ["<reachable-ref:unresolved-commit>"]
                for rows in finding_rows:
                    for finding in rows:
                        finding["paths"] = paths
            context = _object_record(
                root, object_id, paths, metadata, history_by_path, refs, ref_names_by_object
            )
            for rows in finding_rows:
                _bind_finding_context(rows, context)
        security_findings.extend(security)
        privacy_findings.extend(privacy)
        license_findings.extend(licenses)
        archive_findings.extend(archives)

    if progress is not None:
        progress.phase("path_privacy")
    path_privacy_findings: list[dict[str, object]] = []
    for object_id, paths in sorted(object_paths.items()):
        if object_id not in metadata or metadata[object_id].get("type") != "blob":
            continue
        normalized_paths = sorted(paths)
        findings = _private_path_findings(object_id, normalized_paths)
        if findings:
            context = _object_record(
                root,
                object_id,
                normalized_paths,
                metadata,
                history_by_path,
                refs,
                ref_names_by_object,
            )
            _bind_finding_context(findings, context)
        path_privacy_findings.extend(findings)
    privacy_findings.extend(path_privacy_findings)
    private_ref_findings = _private_ref_findings(refs)
    for finding in private_ref_findings:
        ref_name = str(finding.get("path", ""))
        object_id = str(finding.get("object_id", ""))
        context = _object_record(
            root,
            object_id,
            [f"<reachable-ref:{ref_name}>"],
            metadata,
            history_by_path,
            refs,
            ref_names_by_object,
        )
        finding["paths"] = [f"<reachable-ref:{ref_name}>"]
        finding["current_head_exposure"] = True
        _bind_finding_context([finding], context)
    privacy_findings.extend(private_ref_findings)

    if progress is not None:
        progress.phase("oversized_blob_review")
    oversized_findings: list[dict[str, object]] = []
    for object_id, details in sorted(metadata.items()):
        if details.get("type") != "blob" or int(details.get("size_bytes", -1)) <= MAX_SINGLE_BLOB_BYTES:
            continue
        paths = sorted(object_paths.get(object_id, set()))
        if not paths:
            paths = [
                f"<reachable-ref:{ref}>"
                for ref in sorted(ref_names_by_object.get(object_id, set()))
            ]
        finding = {
            "kind": "oversized_blob",
            "object_id": object_id,
            "paths": paths,
            "size_bytes": details.get("size_bytes"),
            "threshold_bytes": MAX_SINGLE_BLOB_BYTES,
            "interpretation": "historical object exceeds the release single-blob review threshold",
        }
        context = _object_record(
            root, object_id, paths, metadata, history_by_path, refs, ref_names_by_object
        )
        _bind_finding_context([finding], context)
        oversized_findings.append(finding)

    if progress is not None:
        progress.phase("unattributed_blob_review")
    unattributed_reachable_blob_findings: list[dict[str, object]] = []
    for object_id, details in sorted(metadata.items()):
        if (
            details.get("type") != "blob"
            or object_paths.get(object_id)
            or not ref_names_by_object.get(object_id)
        ):
            continue
        paths = [
            f"<reachable-ref:{ref}>"
            for ref in sorted(ref_names_by_object.get(object_id, set()))
        ]
        finding = {
            "kind": "unattributed_reachable_blob",
            "object_id": object_id,
            "paths": paths,
            "size_bytes": details.get("size_bytes"),
            "disposition": "release_blocked_direct_ref_blob_requires_operator_content_review",
        }
        context = _object_record(
            root, object_id, paths, metadata, history_by_path, refs, ref_names_by_object
        )
        _bind_finding_context([finding], context)
        unattributed_reachable_blob_findings.append(finding)

    if progress is not None:
        progress.phase("unmanifested_binary_review")
    other_primary_binary_paths = sorted(set(primary_paths) - set(manifest))
    other_binary_findings: list[dict[str, object]] = []
    for path in other_primary_binary_paths:
        for object_id, paths in sorted(object_paths.items()):
            if path not in paths or metadata.get(object_id, {}).get("type") != "blob":
                continue
            record = _object_record(
                root, object_id, [path], metadata, history_by_path, refs, ref_names_by_object
            )
            record.update(
                {
                    "kind": "unmanifested_primary_source_binary",
                    "disposition": "release_blocking_unclassified_third_party_artifact",
                }
            )
            other_binary_findings.append(record)

    for findings in (
        security_findings,
        privacy_findings,
        license_findings,
        archive_findings,
        oversized_findings,
        unattributed_reachable_blob_findings,
    ):
        _annotate_current_head_exposure(findings, current_tracked_paths)
    _annotate_current_head_exposure(other_binary_findings, current_tracked_paths)

    historical_artifact_blockers: list[dict[str, object]] = []
    for record in artifact_records:
        if record.get("retrievable_from_reachable_ref"):
            historical_artifact_blockers.append(
                {
                    "kind": "historical_third_party_artifact",
                    "object_id": record.get("object_id"),
                    "paths": record.get("paths", []),
                    "object_type": record.get("object_type"),
                    "size_bytes": record.get("size_bytes"),
                    "reachable_refs": record.get("reachable_refs", []),
                    "introducing_commits": record.get("introducing_commits", []),
                    "removing_commits": record.get("removing_commits", []),
                    "object_history_commits": record.get("object_history_commits", []),
                    "retrievable_from_reachable_ref": record.get(
                        "retrievable_from_reachable_ref"
                    ),
                    "manifest_disposition": record.get("manifest_disposition"),
                    "manifest_sha256": record.get("manifest_sha256"),
                    "current_head_exposure": record.get("current_head_exposure"),
                    "disposition": "release_blocked_until_operator_approved_history_or_ref_remediation",
                }
            )

    security_blockers = [
        {
            **finding,
            "kind": "historical_secret",
            "disposition": "release_blocked_redacted_secret_review_required",
        }
        for finding in security_findings
    ]
    privacy_blockers = [
        finding
        for finding in privacy_findings
        if finding.get("kind")
        in {
            "absolute_private_filesystem_path",
            "private_or_working_path",
            "private_or_working_ref",
        }
    ]
    privacy_blockers = [
        {**finding, "disposition": "release_blocked_operator_privacy_review_required"}
        for finding in privacy_blockers
    ]
    archive_blockers = [
        {**finding, "disposition": "release_blocked_unsafe_archive_review_required"}
        for finding in archive_findings
    ]
    license_blockers = [
        {
            **finding,
            "kind": "historical_license_marker",
            "disposition": "release_blocked_custom_license_review_required",
        }
        for finding in license_findings
    ]
    oversized_blockers = [
        {**finding, "disposition": "release_blocked_oversized_blob_review_required"}
        for finding in oversized_findings
    ]
    release_blockers = (
        historical_artifact_blockers
        + other_binary_findings
        + unattributed_reachable_blob_findings
        + missing_ref_findings
        + security_blockers
        + privacy_blockers
        + archive_blockers
        + license_blockers
        + oversized_blockers
    )
    if progress is not None:
        progress.phase("scan_boundary")
    scan_end_commit = head_commit(root)
    end_refs = snapshot_refs(root)
    scan_ref_changes = _ref_changes(refs, end_refs)
    scan_consistent = scan_commit == scan_end_commit and not scan_ref_changes
    if not scan_consistent:
        release_blockers = release_blockers + [
            {
                "kind": "non_atomic_scan",
                "scan_start_commit": scan_commit,
                "scan_end_commit": scan_end_commit,
                "ref_change_count": len(scan_ref_changes),
                "changed_refs": [row["ref"] for row in scan_ref_changes],
                "disposition": "release_blocked_history_changed_during_scan",
            }
        ]
    safe = not release_blockers
    content_object_bytes = sum(
        int(metadata[object_id]["size_bytes"]) for object_id in scanned_content_ids
    )
    required_bytes = sum(int(metadata[object_id]["size_bytes"]) for object_id in required_ids)
    skip_reasons: dict[str, int] = defaultdict(int)
    for target in targets.values():
        if not target.required:
            skip_reasons[target.reason] += 1
    payload_selection_evidence = {
        "mode": payload_selection,
        "content_object_count": len(scanned_content_ids),
        "content_object_bytes": content_object_bytes,
        "payload_required_object_count": len(required_ids),
        "payload_required_bytes": required_bytes,
        "payload_requested_object_count": len(requested_ids),
        "payload_requested_bytes": requested_bytes,
        "payload_not_required_by_reason": dict(sorted(skip_reasons.items())),
        "textual_scan_cap_bytes": TEXTUAL_SCAN_CAP_BYTES,
        "size_alone_never_excludes_a_payload": True,
    }
    if progress is not None:
        progress.phase("assembly")
    remediation = _build_remediation(
        refs,
        artifact_records,
        release_blockers,
        scan_ref_changes,
    )

    return {
        "schema": SCHEMA,
        "scanner_source_sha256": _scanner_source_fingerprint(root),
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "scan": {
            "anchor_commit": scan_commit,
            "scan_end_commit": scan_end_commit,
            "scan_consistent": scan_consistent,
            "end_refs": end_refs,
            "ref_changes": scan_ref_changes,
            "active_head_ref": head_ref,
            "ref_count": len(refs),
            "reachable_object_count": len(object_ids),
            "reachable_blob_count": len(scanned_blob_ids),
            "single_blob_review_threshold_bytes": MAX_SINGLE_BLOB_BYTES,
            "control_paths_excluded_from_post_report_delta": sorted(CONTROL_PATHS),
            "audited_ref_names": [row["ref"] for row in refs],
            "audited_ref_digest": "sha256:"
            + _sha256_bytes(json.dumps(refs, sort_keys=True).encode("utf-8")),
            "payload_selection": payload_selection_evidence,
            "content_scan_cache": (
                cache.statistics() if cache is not None else {"enabled": False}
            ),
            "progress": progress.snapshot() if progress is not None else None,
        },
        "refs": refs,
        "inventory": {
            "reachable_object_count": len(object_ids),
            "reachable_blob_count": len(scanned_blob_ids),
            "binary_path_count": len(binary_paths),
            "primary_source_binary_path_count": len(primary_paths),
            "manifest_artifact_count": len(manifest),
            "manifest_artifact_paths_without_reachable_blob": sorted(set(manifest) - set(primary_paths)),
            "unmanifested_primary_source_binary_paths": other_primary_binary_paths,
            "direct_ref_object_count": len(ref_names_by_object),
            "reachable_blob_count_without_tree_path": len(unattributed_reachable_blob_findings),
            "missing_reachable_ref_count": len(missing_ref_findings),
        },
        "artifact_history": sorted(artifact_records, key=lambda row: (str(row.get("paths")), str(row.get("object_id")))),
        "security_findings": sorted(security_findings, key=lambda row: (str(row.get("object_id")), str(row.get("kind")))),
        "privacy_findings": sorted(privacy_findings, key=lambda row: (str(row.get("object_id")), str(row.get("kind")), str(row.get("path", "")))),
        "license_findings": sorted(license_findings, key=lambda row: (str(row.get("object_id")), str(row.get("kind")))),
        "archive_findings": sorted(archive_findings, key=lambda row: (str(row.get("object_id")), str(row.get("kind")))),
        "oversized_findings": oversized_findings,
        "other_binary_findings": other_binary_findings,
        "ref_integrity_findings": missing_ref_findings,
        "release_blockers": sorted(
            release_blockers,
            key=lambda row: (str(row.get("kind")), str(row.get("object_id")), str(row.get("path", row.get("paths", "")))),
        ),
        "release_decision": {
            "status": "release_safe" if safe else "release_blocked_operator_decision_required",
            "safe_for_public_clone": safe,
            "reason": "No prohibited reachable-history finding" if safe else "Reachable history contains prohibited or unresolved ref content that current-tree quarantine cannot remove",
            "scanner_is_not_permission": True,
            "decision_consumes_artifact_manifest": True,
            "operator_remediation": remediation,
        },
    }


def _json_without_volatile(payload: dict[str, object]) -> dict[str, object]:
    copy = json.loads(json.dumps(payload))
    copy.pop("generated_at", None)
    copy.pop("scan", None)
    inventory = copy.get("inventory")
    if isinstance(inventory, dict):
        inventory.pop("reachable_object_count", None)
        inventory.pop("reachable_blob_count", None)
    refs = copy.get("refs")
    if isinstance(refs, list):
        copy["refs"] = _public_ref_view(refs)
    return copy


def _public_ref_view(refs: list[dict[str, object]]) -> list[dict[str, object]]:
    """Collapse ref rows to the view every public clone shape shares.

    The evidence comparison used to keep every ref row verbatim, so a report
    could validate only in a clone whose refs were row-for-row identical to
    the one that generated it. No two checkouts are: a local clone carries
    ``refs/heads/<branch>`` and ``refs/remotes/origin/HEAD``, a push-event
    runner carries ``refs/heads/<branch>`` without the symbolic HEAD, and a
    pull-request runner carries ``refs/remotes/pull/<n>/merge`` and no local
    branch at all. The job had never been green. Compare instead by what a
    public clone can actually reach: each branch name once, whether it is
    seen as a local head or as origin's remote-tracking ref, plus every tag,
    keyed by the commit it peels to. Pull-request merge refs and the
    symbolic origin HEAD name nothing a reader can clone, so they are
    dropped from the comparison; they are still scanned.
    """
    view: dict[tuple[str, str], str] = {}
    for row in refs:
        ref = str(row.get("ref", ""))
        peeled = str(row.get("peeled_commit") or row.get("object_id") or "")
        if ref.startswith("refs/heads/"):
            key = ("branch", ref[len("refs/heads/"):])
        elif ref.startswith("refs/remotes/origin/"):
            name = ref[len("refs/remotes/origin/"):]
            if name == "HEAD":
                continue
            key = ("branch", name)
        elif ref.startswith("refs/remotes/pull/"):
            continue
        elif ref.startswith("refs/tags/"):
            key = ("tag", ref[len("refs/tags/"):])
        else:
            key = ("other", ref)
        if key == ("branch", "main"):
            continue
        view.setdefault(key, peeled)
    return [
        {"ref_class": ref_class, "name": name, "peeled_commit": peeled}
        for (ref_class, name), peeled in sorted(view.items())
    ]


MAX_REPORTED_SUCCESSOR_COMMITS = 32


def successor_commits(root: Path, anchor: str, head: str) -> list[str]:
    """List the commits, oldest first, that carried the subject past the anchor."""
    if not re.fullmatch(r"[0-9a-f]{40}", anchor) or not re.fullmatch(r"[0-9a-f]{40}", head):
        return []
    return [
        line
        for line in _git_lines(root, "rev-list", "--reverse", f"{anchor}..{head}")
        if re.fullmatch(r"[0-9a-f]{40}", line)
    ]


def _stale_subject_error(
    root: Path, anchor: str, head: str, changed: set[str], boundary: str
) -> str:
    """Name the exact successor commits instead of an opaque staleness verdict."""
    commits = successor_commits(root, anchor, head)
    shown = commits[:MAX_REPORTED_SUCCESSOR_COMMITS]
    suffix = "" if len(commits) == len(shown) else f" (+{len(commits) - len(shown)} more)"
    ancestry = (
        "" if commits else " (current head is not a descendant of the audited subject)"
    )
    changed_paths = sorted(changed - CONTROL_PATHS)
    return (
        f"stale-subject: history audit {boundary} {anchor} is not the current head "
        f"{head}{ancestry}; successor commits ({len(commits)}): "
        f"{', '.join(shown) if shown else 'none'}{suffix}; "
        f"changed non-control paths ({len(changed_paths)}): "
        f"{', '.join(changed_paths[:16]) if changed_paths else 'none'}"
    )


def comparison_errors(report: dict[str, object], current: dict[str, object], root: Path = ROOT) -> list[str]:
    errors: list[str] = []
    if report.get("schema") != SCHEMA:
        errors.append("history audit report schema is not the governed version")
    anchor = report.get("scan", {}).get("anchor_commit") if isinstance(report.get("scan"), dict) else None
    current_head = head_commit(root)
    if not isinstance(anchor, str) or not re.fullmatch(r"[0-9a-f]{40}", anchor):
        errors.append("history audit report lacks a valid scan anchor commit")
    if report.get("scanner_source_sha256") != current.get("scanner_source_sha256"):
        errors.append("history audit was generated by a different scanner source revision")
    scan = report.get("scan")
    atomic = isinstance(scan, dict) and scan.get("scan_consistent") is True
    if atomic:
        if anchor != current_head:
            changed = set(_git_lines(root, "diff", "--name-only", f"{anchor}..HEAD"))
            if not changed.issubset(CONTROL_PATHS):
                errors.append(
                    _stale_subject_error(root, anchor, current_head, changed, "scan anchor")
                )
        if _json_without_volatile(report) != _json_without_volatile(current):
            errors.append("committed history audit does not match the current reachable object/ref evidence")
    else:
        # A moving shared checkout can make a scan non-atomic.  That report is
        # still useful only as an explicit red release decision if it proves
        # the frozen start/end boundary and remains current at the ref level.
        decision = report.get("release_decision")
        if not isinstance(decision, dict) or decision.get("safe_for_public_clone") is not False:
            errors.append("non-atomic history audit must remain an explicit release block")
        end_refs = scan.get("end_refs") if isinstance(scan, dict) else None
        start_refs = report.get("refs")
        if not isinstance(start_refs, list) or not isinstance(end_refs, list):
            errors.append("non-atomic history audit lacks frozen start/end ref evidence")
        else:
            active_ref = scan.get("active_head_ref")
            active_ref = (
                active_ref
                if isinstance(active_ref, str) and active_ref.startswith("refs/")
                else f"refs/heads/{active_ref}"
                if isinstance(active_ref, str) and active_ref
                else "refs/heads/main"
            )
            current_refs = current.get("refs")
            if not isinstance(current_refs, list):
                errors.append("current reachable history has no ref evidence")
            else:
                without_active = lambda rows: [row for row in rows if row.get("ref") != active_ref]
                if without_active(current_refs) != without_active(end_refs):
                    errors.append("non-atomic history audit is stale: non-active refs changed after the scan")
            if not isinstance(scan.get("scan_end_commit"), str) or not re.fullmatch(
                r"[0-9a-f]{40}", scan["scan_end_commit"]
            ):
                errors.append("non-atomic history audit lacks a valid scan end commit")
            elif current_head != scan["scan_end_commit"]:
                changed = set(_git_lines(root, "diff", "--name-only", f"{scan['scan_end_commit']}..HEAD"))
                if not changed.issubset(CONTROL_PATHS):
                    errors.append(
                        _stale_subject_error(
                            root,
                            scan["scan_end_commit"],
                            current_head,
                            changed,
                            "non-atomic scan end",
                        )
                    )
            recorded_changes = scan.get("ref_changes")
            if not isinstance(recorded_changes, list) or recorded_changes != _ref_changes(start_refs, end_refs):
                errors.append("non-atomic history audit ref-change evidence is inconsistent")
        blockers = report.get("release_blockers")
        if not isinstance(blockers, list) or not any(
            isinstance(row, dict) and row.get("kind") == "non_atomic_scan" for row in blockers
        ):
            errors.append("non-atomic history audit lacks its release-blocking boundary finding")
    if not isinstance(report.get("release_decision"), dict):
        errors.append("history audit has no release decision consumed by the gate")
    else:
        decision = report["release_decision"]
        if decision.get("decision_consumes_artifact_manifest") is not True:
            errors.append("history release decision does not consume the artifact disposition manifest")
        if decision.get("scanner_is_not_permission") is not True:
            errors.append("history audit incorrectly treats scanning as redistribution permission")
    return errors


def _write_report(report: dict[str, object], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-report", action="store_true", help="write the redacted report")
    parser.add_argument("--check", action="store_true", help="validate the committed report against current history")
    parser.add_argument("--release-gate", action="store_true", help="return non-zero when the public clone is unsafe")
    parser.add_argument("--report", type=Path, default=REPORT_PATH)
    parser.add_argument(
        "--content-cache",
        choices=("auto", "off", "read-only"),
        default=os.environ.get(CONTENT_CACHE_ENV, "auto"),
        help="reuse payload verdicts across interrupted or superseded runs",
    )
    parser.add_argument(
        "--payload-selection",
        choices=("selective", "full"),
        default="selective",
        help="request only payloads that can influence a finding, or every content object",
    )
    parser.add_argument(
        "--progress-seconds",
        type=float,
        default=None,
        help="minimum seconds between progress lines and sidecar writes",
    )
    parser.add_argument(
        "--no-progress", action="store_true", help="suppress progress telemetry"
    )
    args = parser.parse_args(argv)

    progress = ProgressReporter(
        None if args.no_progress else progress_path(ROOT, args.report),
        interval_seconds=args.progress_seconds,
        enabled=not args.no_progress,
    )
    cache = open_content_cache(ROOT, mode=args.content_cache)

    if args.write_report:
        try:
            report = build_audit(
                ROOT,
                progress=progress,
                cache=cache,
                payload_selection=args.payload_selection,
            )
        finally:
            cache.close()
        progress.phase("writing_report")
        _write_report(report, args.report)
        progress.phase("done")
        blockers = report["release_decision"]["safe_for_public_clone"] is False
        print(
            "audit_reachable_release_history: "
            f"{len(report['release_blockers'])} release blockers, "
            f"{report['inventory']['reachable_blob_count']} reachable blobs; "
            f"decision={report['release_decision']['status']}"
        )
        return 3 if args.release_gate and blockers else 0

    if not args.check and not args.release_gate:
        parser.error("choose --write-report, --check, or --release-gate")
    try:
        report = json.loads(args.report.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"audit_reachable_release_history: cannot read report ({type(exc).__name__})", file=sys.stderr)
        return 2
    try:
        current = build_audit(
            ROOT,
            progress=progress,
            cache=cache,
            payload_selection=args.payload_selection,
        )
    finally:
        cache.close()
    progress.phase("done")
    errors = comparison_errors(report, current, ROOT)
    if errors:
        for error in errors:
            print(f"audit_reachable_release_history: ERROR: {error}", file=sys.stderr)
        return 2
    decision = report.get("release_decision", {})
    print(
        "audit_reachable_release_history: evidence matches the reachable history; "
        f"decision={decision.get('status', 'unknown')}"
    )
    if args.release_gate and decision.get("safe_for_public_clone") is not True:
        print("audit_reachable_release_history: RELEASE BLOCKED: operator remediation is required", file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
