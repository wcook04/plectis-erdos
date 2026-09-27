#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exercise an actual Git push: dirty repairs cannot validate stale commits."""

from __future__ import annotations

import os
import json
from unittest import mock
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
            (root / "scripts/check_release.py").write_text(
                "import runpy\nrunpy.run_path('scripts/refresh_projections.py', run_name='__main__')\n")
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
            def prepare(commit="HEAD", check=True):
                return subprocess.run([sys.executable, "scripts/check_push.py", "--prepare", commit],
                                      cwd=root, env=env, text=True, capture_output=True, check=check)
            good = git("rev-parse", "HEAD").stdout.strip()
            self.assertNotEqual(git("push", "origin", "HEAD:refs/heads/review", check=False).returncode, 0)
            prepare()
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
            self.assertNotEqual(prepare(stale, check=False).returncode, 0)
            git("commit", "-qm", "commit repair")
            prepare()
            self.assertEqual(git("push", "origin", "HEAD:refs/heads/review", check=False).returncode, 0)
            # Validate the ref being pushed even when HEAD is good.
            self.assertNotEqual(git("push", "origin", f"{stale}:refs/heads/old", check=False).returncode, 0)
            self.assertEqual(git("push", "origin", ":refs/heads/review", check=False).returncode, 0)

            # A green old head is insufficient after another PR advances main.
            self.assertEqual(git("push", "origin", "HEAD:refs/heads/main", check=False).returncode, 0)
            old_base = git("rev-parse", "origin/main").stdout.strip()
            peer = Path(temp) / "peer"
            git("clone", "-q", "--branch", "main", str(remote), str(peer))
            def peer_git(*args):
                return subprocess.run(["git", *args], cwd=peer, env=env, text=True,
                                      capture_output=True, check=True)
            peer_git("config", "user.name", "Base fixture")
            peer_git("config", "user.email", "base@example.invalid")
            (peer / "base.txt").write_text("new main\n")
            peer_git("add", "base.txt")
            peer_git("commit", "-qm", "advance destination main")
            peer_git("push", "origin", "main")
            new_base = peer_git("rev-parse", "HEAD").stdout.strip()
            peer_git("push", "origin", f"{old_base}:refs/heads/parent")
            git("config", "branch.stacked.plectisAdmissionBase", "refs/heads/parent")
            self.assertEqual(git("push", "origin", "HEAD:refs/heads/stacked", check=False).returncode, 0)
            (root / "scratch.txt").write_text("preserve local work\n")
            fetch_head = root / ".git/FETCH_HEAD"
            fetch_head.write_text("preserve fetch receipt\n")
            before = git("status", "--porcelain").stdout
            rejected = git("push", "origin", "HEAD:refs/heads/review", check=False)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn("destination main advanced", rejected.stderr)
            self.assertEqual(git("status", "--porcelain").stdout, before)
            self.assertEqual(fetch_head.read_text(), "preserve fetch receipt\n")
            self.assertEqual(git("rev-parse", "origin/main").stdout.strip(), old_base)
            # The observed object was fetched without moving any local ref.
            git("cat-file", "-e", new_base)
            git("merge", "--no-edit", new_base)
            prepare()
            self.assertEqual(git("push", "origin", "HEAD:refs/heads/review", check=False).returncode, 0)


            # One shared versioned guard covers another worktree, using that
            # worktree's Git root rather than the copied driver's directory.
            git("config", "--worktree", "--unset", "core.hooksPath")
            subprocess.run([sys.executable, "scripts/check_push.py", "--install-shared"],
                           cwd=root, env=env, check=True, capture_output=True)
            sibling = Path(temp) / "sibling"
            git("worktree", "add", "-b", "sibling", str(sibling))
            pushed = subprocess.run(["git", "push", "origin", "HEAD:refs/heads/sibling"],
                                    cwd=sibling, env=env, text=True, capture_output=True)
            self.assertEqual(pushed.returncode, 0, pushed.stderr)
            # A changed validation driver invalidates its old admission.
            installed = Path(git("config", "--get", "core.hooksPath").stdout.strip())
            bundled = next(installed.glob("*/check_push.py"))
            bundled.write_text(bundled.read_text() + "\n# revised validator\n")
            rejected = subprocess.run(["git", "push", "origin", "HEAD:refs/heads/uncertified"],
                                      cwd=sibling, env=env, text=True, capture_output=True)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn("no current admission", rejected.stderr)
            git("config", "--local", "core.hooksPath", "/custom/preserve")
            refused = subprocess.run([sys.executable, "scripts/check_push.py", "--install-shared"],
                                     cwd=root, env=env, text=True, capture_output=True)
            self.assertNotEqual(refused.returncode, 0)
            self.assertEqual(git("config", "--get", "core.hooksPath").stdout.strip(), "/custom/preserve")

    def test_failed_incomplete_or_other_commit_receipts_never_admit(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "release.json"
            passed = {"schema": check_push.snapshot.SCHEMA, "resolved_commit": "a" * 40,
                      "status": "passed", "gate_exit_code": 0, "failed_gate_count": 0,
                      "snapshot_posture": "clean_committed_clone_excludes_caller_worktree_changes",
                      "release_commands": [list(c) for c in check_push.snapshot.RELEASE_COMMANDS],
                      "gate_coverage": {"all_configured_gates_completed": True,
                                        "completed_gate_count": len(check_push.snapshot.RELEASE_COMMANDS)}}
            with mock.patch.object(check_push.snapshot, "resolve_commit", return_value="a" * 40), \
                 mock.patch.object(check_push, "save_admission") as save:
                for change in ({"status": "failed"}, {"resolved_commit": "b" * 40},
                               {"gate_coverage": {}}, {"gate_exit_code": 1},
                               {"failed_gate_count": 1}, {"release_commands": []}):
                    path.write_text(json.dumps({**passed, **change}))
                    with self.assertRaises(ValueError):
                        check_push.prepare_commit("HEAD", path)
                save.assert_not_called()
                path.write_text(json.dumps(passed))
                self.assertEqual(check_push.prepare_commit("HEAD", path), 0)
                save.assert_called_once()


if __name__ == "__main__":
    unittest.main()
