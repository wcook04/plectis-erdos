#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Deterministic, bounded storage for the unchanged semantic-corpus JSON."""

from __future__ import annotations

import gzip
import io
import json
import os
from pathlib import Path
import stat
import zlib

ROOT = Path(__file__).resolve().parents[1]
CORPUS_RELATIVE_PATH = "docs/semantic_corpus.json.gz"
CORPUS = ROOT / CORPUS_RELATIVE_PATH
MAX_COMPRESSED_BYTES = 16 * 1024 * 1024
MAX_DECOMPRESSED_BYTES = 192 * 1024 * 1024


class CorpusStorageError(ValueError):
    """Compressed corpus is unsafe, corrupt, or outside its size contract."""


def _open_regular(path: Path, root: Path, *, write: bool = False) -> int:
    """Walk directory descriptors without following replaceable symlinks."""
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(path))
    try:
        relative = candidate.relative_to(root)
    except ValueError as error:
        raise CorpusStorageError(f"corpus path escaped checkout: {candidate}") from error
    candidate = root.resolve() / relative
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    directory = os.open(os.sep, flags)
    descriptor = -1
    try:
        for component in candidate.parts[1:-1]:
            child = os.open(component, flags, dir_fd=directory)
            os.close(directory)
            directory = child
        file_flags = (os.O_WRONLY | os.O_CREAT) if write else os.O_RDONLY
        file_flags |= getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
        descriptor = os.open(candidate.name, file_flags, 0o644, dir_fd=directory)
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode):
            raise CorpusStorageError(f"corpus is not a regular file: {candidate}")
        if not write and info.st_size > MAX_COMPRESSED_BYTES:
            raise CorpusStorageError("compressed corpus exceeds 16 MiB storage budget")
        result, descriptor = descriptor, -1
        return result
    except OSError as error:
        raise CorpusStorageError(f"corpus could not be opened safely: {candidate}") from error
    finally:
        os.close(directory)
        if descriptor >= 0:
            os.close(descriptor)


def decode_corpus(compressed: bytes) -> bytes:
    """Read through the gzip footer, rejecting truncation and oversized output."""
    if len(compressed) > MAX_COMPRESSED_BYTES:
        raise CorpusStorageError("compressed corpus exceeds 16 MiB storage budget")
    try:
        with gzip.GzipFile(fileobj=io.BytesIO(compressed), mode="rb") as stream:
            raw = stream.read(MAX_DECOMPRESSED_BYTES + 1)
    except (OSError, EOFError, zlib.error) as error:
        raise CorpusStorageError("semantic corpus gzip is corrupt or truncated") from error
    if len(raw) > MAX_DECOMPRESSED_BYTES:
        raise CorpusStorageError("decompressed corpus exceeds 192 MiB budget")
    return raw


def encode_corpus(text: str) -> bytes:
    raw = text.encode("utf-8")
    if len(raw) > MAX_DECOMPRESSED_BYTES:
        raise CorpusStorageError("decompressed corpus exceeds 192 MiB budget")
    # GzipFile fixes the OS header byte across Python/zlib platform versions.
    output = io.BytesIO()
    with gzip.GzipFile(fileobj=output, mode="wb", compresslevel=6, mtime=0) as stream:
        stream.write(raw)
    compressed = output.getvalue()
    if len(compressed) > MAX_COMPRESSED_BYTES:
        raise CorpusStorageError("compressed corpus exceeds 16 MiB storage budget")
    return compressed


def read_corpus_bytes(path: Path = CORPUS, *, root: Path = ROOT) -> bytes:
    with os.fdopen(_open_regular(path, root), "rb") as stream:
        compressed = stream.read(MAX_COMPRESSED_BYTES + 1)
    return decode_corpus(compressed)


def load_corpus(path: Path = CORPUS, *, root: Path = ROOT) -> dict:
    try:
        payload = json.loads(read_corpus_bytes(path, root=root))
    except (UnicodeError, json.JSONDecodeError) as error:
        raise CorpusStorageError("semantic corpus does not contain valid JSON") from error
    if not isinstance(payload, dict):
        raise CorpusStorageError("semantic corpus must contain a JSON object")
    return payload


def write_corpus(path: Path, compressed: bytes, *, root: Path = ROOT) -> None:
    if len(compressed) > MAX_COMPRESSED_BYTES:
        raise CorpusStorageError("compressed corpus exceeds 16 MiB storage budget")
    with os.fdopen(_open_regular(path, root, write=True), "wb") as stream:
        stream.truncate(0)
        stream.write(compressed)
