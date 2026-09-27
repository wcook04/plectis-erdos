#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise an actual Git push: dirty repairs cannot validate stale commits."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import check_push


class PushTests(unittest.TestCase):
    def test_delete_duplicate_and_malformed_updates(self):
        oid = "a" * 40
        zero = "0" * 40
        self.assertEqual(check_push.outgoing_commits([
            f"refs/heads/a {oid} refs/heads/a {zero}",
            f"refs/heads/b {oid} refs/heads/b {zero}",
            f"(delete) {zero} refs/heads/c {oid}",
        ]), [oid])
        for row in ("", "a b c d", f"a {oid} c"):
            with self.assertRaises(ValueError):
                check_push.outgoing_commits([row])

    def test_git_push_checks_outgoing_commit_and_preserves_dirty_tree(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "source"
            root.mkdir()
            remote = Path(temp) / "remote.git"
            env = check_push.snapshot.clean_environment()
            env["PATH"] = str(Path(sys.executable).parent) + os.pathsep + os.defpath

            def git(*args, check=True):
                return subprocess.run(["git", *args], cwd=root, env=env,
                                      text=True, capture_output=True, check=check)

            git("init", "-q")
            git("config", "user.name", "Push fixture")
            git("config", "user.email", "push@example.invalid")
            git("init", "--bare", "-q", str(remote))
            git("remote", "add", "origin", str(remote))
            for command in check_push.snapshot.RELEASE_COMMANDS:
                path = root / command[1]
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("print('fixture')\n")
            for name in ("check_push.py", "check_release_ref.py"):
                shutil.copyfile(Path(check_push.__file__).parent / name, root / "scripts" / name)
            (root / "scripts/refresh_projections.py").write_text(
                "from pathlib import Path\n"
                "raise SystemExit(0 if Path('source.txt').read_bytes() == "
                "Path('projection.txt').read_bytes() else 1)\n"
            )
            (root / ".githooks").mkdir()
            hook = root / ".githooks/pre-push"
            shutil.copyfile(Path(check_push.__file__).parents[1] / ".githooks/pre-push", hook)
            hook.chmod(0o755)
            for name in ("source.txt", "projection.txt"):
                (root / name).write_text("before\n")
            git("add", ".")
            git("commit", "-qm", "current fixture")
            subprocess.run([sys.executable, "scripts/check_push.py", "--install"],
                           cwd=root, env=env, check=True, capture_output=True)
            good = git("rev-parse", "HEAD").stdout.strip()
            self.assertEqual(git("push", "origin", "HEAD:refs/heads/review", check=False).returncode, 0)

            (root / "source.txt").write_text("after\n")
            git("add", "source.txt")
            git("commit", "-qm", "stale projection")
            stale = git("rev-parse", "HEAD").stdout.strip()
            # A dirty repair would pass a working-tree-only preflight.
            (root / "projection.txt").write_text("after\n")
            rejected = git("push", "origin", "HEAD:refs/heads/review", check=False)
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
            self.assertIn("Push stopped", rejected.stderr)
            self.assertEqual(git("ls-remote", "origin", "refs/heads/review").stdout.split()[0], good)
            self.assertEqual((root / "projection.txt").read_text(), "after\n")

            git("add", "projection.txt")
            git("commit", "-qm", "commit repair")
            self.assertEqual(git("push", "origin", "HEAD:refs/heads/review", check=False).returncode, 0)
            # Validate the ref being pushed even when HEAD is good.
            self.assertNotEqual(git("push", "origin", f"{stale}:refs/heads/old", check=False).returncode, 0)
            self.assertEqual(git("push", "origin", ":refs/heads/review", check=False).returncode, 0)


if __name__ == "__main__":
    unittest.main()
