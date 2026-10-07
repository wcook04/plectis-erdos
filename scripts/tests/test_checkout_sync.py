#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise safe checkout convergence with disposable local Git repositories."""

import _test_bootstrap  # noqa: F401

import subprocess
import sys
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import check_checkout_sync
from check_checkout_sync import git, mergeability, snapshot, synchronize_main


class CheckoutSyncTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        git(self.root, "init", "-b", "main")
        git(self.root, "config", "user.name", "Test")
        git(self.root, "config", "user.email", "test@example.invalid")
        self.commit("initial")
        git(self.root, "update-ref", "refs/remotes/origin/main", "HEAD")

    def commit(self, text):
        (self.root / "tracked.txt").write_text(text)
        git(self.root, "add", "--", "tracked.txt")
        git(self.root, "-c", "core.hooksPath=/dev/null", "commit", "-m", text)

    def advance_remote(self):
        git(self.root, "switch", "-c", "remote-candidate")
        self.commit("remote")
        git(self.root, "update-ref", "refs/remotes/origin/main", "HEAD")
        git(self.root, "switch", "main")

    def test_fast_forward_preserves_untracked_work(self):
        self.advance_remote()
        (self.root / "unfinished.lean").write_text("private candidate bytes")
        self.assertEqual(snapshot(self.root)["main_only_commits"], 1)
        self.assertTrue(synchronize_main(self.root)["synchronized"])
        self.assertEqual((self.root / "unfinished.lean").read_text(), "private candidate bytes")

    def test_unfinished_branch_is_never_switched(self):
        git(self.root, "switch", "-c", "unfinished")
        self.commit("local")
        before = git(self.root, "rev-parse", "HEAD")
        with self.assertRaisesRegex(ValueError, "switch branches"):
            synchronize_main(self.root)
        self.assertEqual(git(self.root, "rev-parse", "HEAD"), before)

    def test_divergent_main_is_never_reset(self):
        self.advance_remote()
        self.commit("local")
        before = git(self.root, "rev-parse", "HEAD")
        with self.assertRaisesRegex(ValueError, "local commits"):
            synchronize_main(self.root)
        self.assertEqual(git(self.root, "rev-parse", "HEAD"), before)

    def test_tracked_changes_are_preserved(self):
        self.advance_remote()
        (self.root / "tracked.txt").write_text("unfinished edit")
        with self.assertRaisesRegex(ValueError, "tracked changes"):
            synchronize_main(self.root)
        self.assertEqual((self.root / "tracked.txt").read_text(), "unfinished edit")

    def test_untracked_collision_is_preserved(self):
        git(self.root, "switch", "-c", "remote-candidate")
        (self.root / "new.txt").write_text("public")
        git(self.root, "add", "new.txt")
        git(self.root, "-c", "core.hooksPath=/dev/null", "commit", "-m", "new file")
        git(self.root, "update-ref", "refs/remotes/origin/main", "HEAD")
        git(self.root, "switch", "main")
        (self.root / "new.txt").write_text("unpublished")
        with self.assertRaises(subprocess.CalledProcessError):
            synchronize_main(self.root)
        self.assertEqual((self.root / "new.txt").read_text(), "unpublished")

    def run_merge_check(self):
        return subprocess.run(
            [sys.executable, check_checkout_sync.__file__, "--root", str(self.root),
             "--check-merge"], capture_output=True, text=True,
        )

    def test_clean_feature_divergence_is_mergeable_without_syncing(self):
        self.advance_remote()
        git(self.root, "switch", "-c", "feature")
        (self.root / "feature.txt").write_text("independent work")
        git(self.root, "add", "feature.txt")
        git(self.root, "-c", "core.hooksPath=/dev/null", "commit", "-m", "feature")
        before = snapshot(self.root)
        index = git(self.root, "write-tree")
        result = self.run_merge_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["status"], "mergeable")
        self.assertEqual(snapshot(self.root), before)
        self.assertEqual(git(self.root, "write-tree"), index)
        self.assertEqual((self.root / "tracked.txt").read_text(), "initial")

    def test_real_conflict_is_named_without_touching_candidate(self):
        self.advance_remote()
        self.commit("incompatible local edit")
        before = snapshot(self.root)
        index = git(self.root, "write-tree")
        result = self.run_merge_check()
        self.assertEqual(result.returncode, 1, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report["status"], "conflicting")
        self.assertEqual(report["conflicting_paths"], ["tracked.txt"])
        self.assertEqual(snapshot(self.root), before)
        self.assertEqual(git(self.root, "write-tree"), index)
        self.assertEqual((self.root / "tracked.txt").read_text(), "incompatible local edit")

    def test_uncommitted_inputs_are_not_certified_by_head(self):
        for untracked in (False, True):
            with self.subTest(untracked=untracked):
                path = self.root / ("new.txt" if untracked else "tracked.txt")
                original = path.read_text() if path.exists() else None
                path.write_text("unfinished")
                self.assertEqual(self.run_merge_check().returncode, 2)
                self.assertEqual(path.read_text(), "unfinished")
                if original is None:
                    path.unlink()
                else:
                    path.write_text(original)

    def test_unavailable_base_fails_closed(self):
        with self.assertRaises(subprocess.CalledProcessError):
            mergeability(self.root, "missing-base")

    def test_explicit_base_does_not_require_origin_main(self):
        git(self.root, "update-ref", "refs/remotes/origin/release", "HEAD")
        git(self.root, "update-ref", "-d", "refs/remotes/origin/main")
        result = mergeability(self.root, "origin/release")
        self.assertEqual(result["status"], "mergeable")
        self.assertEqual(result["base"], "origin/release")

    def test_ambient_git_context_cannot_redirect_merge_check(self):
        with patch.dict(os.environ, {
            "GIT_DIR": str(self.root / "not-a-repository"),
            "GIT_WORK_TREE": str(self.root / "wrong-tree"),
            "GIT_INDEX_FILE": str(self.root / "wrong-index"),
        }):
            result = mergeability(self.root)
        self.assertEqual(result["status"], "mergeable")
        self.assertFalse((self.root / "wrong-index").exists())


if __name__ == "__main__":
    unittest.main()
