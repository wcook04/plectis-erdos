#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise safe checkout convergence with disposable local Git repositories."""

import subprocess
import tempfile
import unittest
from pathlib import Path

from check_checkout_sync import git, snapshot, synchronize_main


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


if __name__ == "__main__":
    unittest.main()
