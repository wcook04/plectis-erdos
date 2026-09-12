#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise compressed corpus integrity and checkout boundaries."""

import gzip
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import semantic_corpus_storage as storage


class CorpusStorageTests(unittest.TestCase):
    def test_roundtrip_preserves_unicode_and_deterministic_bytes(self) -> None:
        text = '{"nodes":["𝓝","λ","\\\\",null],"count":42}\n'
        compressed = storage.encode_corpus(text)
        self.assertEqual(compressed, storage.encode_corpus(text))
        self.assertEqual(compressed[4:8], b"\0" * 4)
        self.assertEqual(compressed[9], 255)
        self.assertEqual(storage.decode_corpus(compressed), text.encode())
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "corpus.json.gz"
            storage.write_corpus(path, compressed, root=root)
            self.assertEqual(storage.load_corpus(path, root=root), json.loads(text))
            smaller = storage.encode_corpus('{"small":true}')
            storage.write_corpus(path, smaller, root=root)
            self.assertEqual(path.read_bytes(), smaller)

    def test_corruption_truncation_and_trailing_garbage_are_rejected(self) -> None:
        compressed = storage.encode_corpus('{"node":"exact"}')
        for corrupted in (
            b"not gzip", compressed[:8], compressed[:-1], compressed[:-8],
            compressed[:-8] + bytes([compressed[-8] ^ 1]) + compressed[-7:],
            compressed + b"trailing garbage",
        ):
            with self.subTest(corrupted=corrupted), self.assertRaises(storage.CorpusStorageError):
                storage.decode_corpus(corrupted)

    def test_compressed_and_expanded_budgets_are_enforced(self) -> None:
        compressed = storage.encode_corpus('{"payload":"' + 'x' * 1000 + '"}')
        with patch.object(storage, "MAX_COMPRESSED_BYTES", len(compressed) - 1):
            with self.assertRaises(storage.CorpusStorageError):
                storage.decode_corpus(compressed)
        with patch.object(storage, "MAX_DECOMPRESSED_BYTES", 40):
            with self.assertRaises(storage.CorpusStorageError):
                storage.decode_corpus(compressed)
            with self.assertRaises(storage.CorpusStorageError):
                storage.encode_corpus('x' * 41)

    def test_invalid_json_and_non_object_roots_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "corpus.json.gz"
            for raw in (b"", b"not JSON", b"[]", b"\xff"):
                path.write_bytes(gzip.compress(raw, mtime=0))
                with self.subTest(raw=raw), self.assertRaises(storage.CorpusStorageError):
                    storage.load_corpus(path, root=root)

    def test_symlink_files_parents_and_escapes_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actual = root / "actual"
            actual.mkdir()
            path = actual / "corpus.json.gz"
            content = storage.encode_corpus('{"untouched":true}')
            path.write_bytes(content)
            (root / "file-link").symlink_to(path)
            (root / "parent-link").symlink_to(actual, target_is_directory=True)
            for unsafe in (root / "file-link", root / "parent-link" / path.name, root / ".." / "outside.json.gz"):
                with self.subTest(path=unsafe):
                    with self.assertRaises(storage.CorpusStorageError):
                        storage.load_corpus(unsafe, root=root)
                    with self.assertRaises(storage.CorpusStorageError):
                        storage.write_corpus(unsafe, content, root=root)
            self.assertEqual(path.read_bytes(), content)

    def test_nonregular_and_oversized_files_are_rejected_before_reading(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pipe = root / "pipe"
            os.mkfifo(pipe)
            with self.assertRaises(storage.CorpusStorageError):
                storage.load_corpus(pipe, root=root)
            path = root / "large.json.gz"
            with path.open("wb") as stream:
                stream.truncate(storage.MAX_COMPRESSED_BYTES + 1)
            with self.assertRaises(storage.CorpusStorageError):
                storage.load_corpus(path, root=root)

    def test_checkout_root_alias_is_portable_but_artifact_links_are_not(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root = base / "actual-checkout"
            root.mkdir()
            alias = base / "checkout-alias"
            alias.symlink_to(root, target_is_directory=True)
            path = alias / "corpus.json.gz"
            storage.write_corpus(path, storage.encode_corpus('{"ok":true}'), root=alias)
            self.assertEqual(storage.load_corpus(path, root=alias), {"ok": True})


if __name__ == "__main__":
    unittest.main()
