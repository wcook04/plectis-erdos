#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Offline wrapper tests using disposable Git fixtures, not mathematical evidence."""
from __future__ import annotations
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SKILL = ROOT / ".agents/skills/plectis-frontier"
spec = importlib.util.spec_from_file_location("frontier_bootstrap", SKILL / "scripts/bootstrap.py")
assert spec and spec.loader
bootstrap = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bootstrap)


class FrontierSkillTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="plectis-frontier-test-")
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)

    def fixture(self):
        root = self.base / "research checkout ; literal"
        root.mkdir()
        bootstrap.git(root, "init", "--template=")
        bootstrap.git(root, "config", "user.name", "Offline test fixture")
        bootstrap.git(root, "config", "user.email", "fixture@example.invalid")
        bootstrap.git(root, "remote", "add", "origin", bootstrap.PUBLIC_URL)
        for name in bootstrap.REQUIRED:
            file = root / name
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text("Offline test fixture only.\n", encoding="utf-8")
        (root / "scripts/agent_entry.py").write_text(
            'import json\nprint(json.dumps({"schema":"plectis-agent-entry/1",'
            '"primary_lane":{"id":"fixture"}}))\n', encoding="utf-8")
        (root / "scripts/query_corpus.py").write_text(
            'print("OFFLINE FIXTURE: not real corpus or mathematical evidence")\n', encoding="utf-8")
        bootstrap.git(root, "add", "--all")
        bootstrap.git(root, "-c", "commit.gpgsign=false", "commit", "-m", "Disposable fixture")
        return root, {"repository": bootstrap.PUBLIC_URL, "commit": bootstrap.git(root, "rev-parse", "HEAD")}

    def manifest(self, **changes):
        data = bootstrap.load_source()
        data.update(changes)
        path = self.base / "source.json"
        path.write_text(json.dumps(data), encoding="utf-8")
        return path

    def test_source_is_exact_and_public(self):
        source = bootstrap.load_source()
        self.assertEqual(source["repository"], bootstrap.PUBLIC_URL)
        self.assertRegex(source["commit"], r"^[0-9a-f]{40}$")

    def test_moving_ref_rejected(self):
        with self.assertRaises(bootstrap.BootstrapError):
            bootstrap.load_source(self.manifest(commit="main"))

    def test_nonstring_commit_rejected(self):
        with self.assertRaises(bootstrap.BootstrapError):
            bootstrap.load_source(self.manifest(commit=int("1" * 40)))

    def test_other_repository_rejected(self):
        with self.assertRaises(bootstrap.BootstrapError):
            bootstrap.load_source(self.manifest(repository="https://example.invalid/repo.git"))

    def test_nonobject_manifest_rejected(self):
        path = self.base / "bad.json"
        path.write_text("[]", encoding="utf-8")
        with self.assertRaises(bootstrap.BootstrapError):
            bootstrap.load_source(path)

    def test_default_is_inspection_without_subprocess(self):
        with mock.patch.object(bootstrap, "run", side_effect=AssertionError("must not execute")):
            with contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(bootstrap.main([]), 0)
        self.assertEqual(json.loads(output.getvalue())["status"], "inspection-only")

    def test_fetch_requires_permission(self):
        target = self.base / "new"
        with self.assertRaisesRegex(bootstrap.BootstrapError, "allow-network"):
            bootstrap.prepare(target, bootstrap.load_source(), False)
        self.assertFalse(target.exists())

    def test_existing_directory_is_not_overwritten(self):
        target = self.base / "existing"
        target.mkdir()
        sentinel = target / "keep.txt"
        sentinel.write_text("keep", encoding="utf-8")
        with self.assertRaisesRegex(bootstrap.BootstrapError, "already exists"):
            bootstrap.prepare(target, bootstrap.load_source(), True)
        self.assertEqual(sentinel.read_text(), "keep")

    def test_dangling_symlink_is_not_overwritten(self):
        target = self.base / "link"
        target.symlink_to(self.base / "not-created", target_is_directory=True)
        with self.assertRaises(bootstrap.BootstrapError):
            bootstrap.prepare(target, bootstrap.load_source(), True)
        self.assertTrue(target.is_symlink())

    def test_fetch_uses_only_exact_pin_mocked_network(self):
        source = bootstrap.load_source()
        target = self.base / "new"
        with mock.patch.object(bootstrap, "git", return_value="") as calls:
            with mock.patch.object(bootstrap, "verify", return_value={"commit": source["commit"]}):
                bootstrap.prepare(target, source, True)
        # prepare() resolves the parent (macOS maps /var to /private/var), so compare against the resolved root.
        root = target.parent.resolve() / target.name
        calls.assert_any_call(root, "fetch", "--depth", "1", "--no-tags", "origin", source["commit"], timeout=300)
        self.assertEqual(len(calls.call_args_list), 4)

    def test_clean_fixture_verifies(self):
        root, source = self.fixture()
        self.assertEqual(bootstrap.verify(root, source)["commit"], source["commit"])

    def test_wrong_pin_rejected(self):
        root, source = self.fixture()
        source["commit"] = "0" * 40
        with self.assertRaisesRegex(bootstrap.BootstrapError, "Wrong commit"):
            bootstrap.verify(root, source)

    def test_wrong_origin_rejected(self):
        root, source = self.fixture()
        bootstrap.git(root, "remote", "set-url", "origin", "https://example.invalid/other.git")
        with self.assertRaisesRegex(bootstrap.BootstrapError, "Origin differs"):
            bootstrap.verify(root, source)

    def test_dirty_tree_rejected_and_preserved(self):
        root, source = self.fixture()
        file = root / "AGENTS.md"
        file.write_text("user work", encoding="utf-8")
        with self.assertRaisesRegex(bootstrap.BootstrapError, "clean checkout"):
            bootstrap.verify(root, source)
        self.assertEqual(file.read_text(), "user work")

    def test_untracked_work_rejected_and_preserved(self):
        root, source = self.fixture()
        file = root / "my-result.txt"
        file.write_text("result", encoding="utf-8")
        with self.assertRaises(bootstrap.BootstrapError):
            bootstrap.verify(root, source)
        self.assertTrue(file.exists())

    def test_nested_directory_rejected(self):
        root, source = self.fixture()
        with self.assertRaises(bootstrap.BootstrapError):
            bootstrap.verify(root / "scripts", source)

    def test_execution_requires_permission(self):
        with self.assertRaisesRegex(bootstrap.BootstrapError, "allow-execution"):
            bootstrap.smoke(self.base, bootstrap.load_source(), False)

    def test_fixture_smoke_preserves_explicit_evidence_limit(self):
        root, source = self.fixture()
        receipt = bootstrap.smoke(root, source, True)
        self.assertEqual(receipt["status"], "entry-smoke-passed-not-lean-verified")
        self.assertIn("No Lean build", receipt["limits"])
        self.assertEqual(len(receipt["checks"]), 2)
        self.assertIn("OFFLINE FIXTURE", receipt["checks"][1]["output"])

    def test_child_environment_does_not_forward_credentials(self):
        with mock.patch.dict(os.environ, {"GITHUB_TOKEN": "fixture-secret", "OPENAI_API_KEY": "fixture-secret",
                                          "GIT_SSH_COMMAND": "do-not-run", "PYTHONPATH": "/unrelated"}):
            env = bootstrap.child_environment()
        for key in ("GITHUB_TOKEN", "OPENAI_API_KEY", "GIT_SSH_COMMAND"):
            self.assertNotIn(key, env)
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(env["PYTHONPATH"], "")

    def test_nonzero_exit_is_not_reported_as_pass(self):
        with self.assertRaises(bootstrap.BootstrapError):
            bootstrap.run([sys.executable, "-c", "raise SystemExit(7)"], self.base)

    def test_timeout_is_visible(self):
        with self.assertRaises(subprocess.TimeoutExpired):
            bootstrap.run([sys.executable, "-c", "import time; time.sleep(2)"], self.base, timeout=0.05)

    def test_oversized_output_rejected(self):
        with self.assertRaisesRegex(bootstrap.BootstrapError, "128 KiB"):
            bootstrap.run([sys.executable, "-c", "print('x' * 140000)"], self.base)

    def test_mit_zero_exception_is_narrow(self):
        config = tomllib.loads((ROOT / "REUSE.toml").read_text(encoding="utf-8"))
        exceptions = [row for row in config["annotations"]
                      if row.get("SPDX-License-Identifier") == "MIT-0"]
        self.assertEqual(len(exceptions), 1)
        self.assertEqual(exceptions[0]["path"], [".agents/skills/plectis-frontier/**"])
        self.assertEqual(exceptions[0]["precedence"], "override")
        self.assertEqual((SKILL / "LICENSE.txt").read_bytes(),
                         (ROOT / "LICENSES/MIT-0.txt").read_bytes())

    def test_portable_frontmatter_has_string_metadata(self):
        front = (SKILL / "SKILL.md").read_text(encoding="utf-8").split("---", 2)[1]
        fields = dict(line.split(": ", 1) for line in front.splitlines()
                      if ": " in line and not line.startswith(" "))
        self.assertLessEqual(len(fields["name"]), 64)
        self.assertLessEqual(len(fields["description"]), 1024)
        self.assertLessEqual(len(fields["compatibility"]), 500)
        self.assertIn('  author: Will Cook', front)
        self.assertIn('  version: "0.1.0"', front)
        self.assertNotIn("    ", front)

    def test_bundle_is_small_standalone_and_licensed(self):
        names = {p.relative_to(SKILL).as_posix() for p in SKILL.rglob("*") if p.is_file()}
        self.assertEqual(names, {"SKILL.md", "LICENSE.txt", "source.json", "scripts/bootstrap.py"})
        body = (SKILL / "SKILL.md").read_text(encoding="utf-8")
        self.assertTrue(body.startswith("---\nname: plectis-frontier\n"))
        self.assertIn("license: MIT-0", body)
        self.assertLess(len(body.splitlines()), 500)
        self.assertIn("separate owner approval", body)
        self.assertLess(sum(p.stat().st_size for p in SKILL.rglob("*") if p.is_file()), 32768)


if __name__ == "__main__":
    unittest.main(verbosity=2)
