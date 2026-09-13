#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Offline negative and package-boundary fixtures for downstream reuse."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_downstream_reuse as reuse


class DownstreamReuseTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="reuse fixture ")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'source "quoted"'
        for path in (".lake/build/lib/lean", ".lake/packages/mathlib", "research/examples"):
            (self.root / path).mkdir(parents=True)
        for module in ("Erdos249257", "ErdosProblems"):
            (self.root / f".lake/build/lib/lean/{module}.olean").write_bytes(b"fixture")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n")
        (self.root / ".lake/packages/mathlib/lakefile.lean").write_text("-- fixture\n")
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": "mathlib", "scope": "leanprover-community", "configFile": "lakefile.lean"}
        ]}))
        (self.root / "research/examples/Examples.lean").write_text("import Erdos249257\nexample : 1 = 1 := rfl\n")

    def test_independent_manifest_preserves_paths_and_exact_example(self):
        destination = Path(self.temp.name) / "consumer"
        reuse.prepare_consumer(self.root, destination)
        import tomllib
        config = tomllib.loads((destination / "lakefile.toml").read_text())
        self.assertEqual(config["require"][0]["path"], str(self.root.resolve()))
        entries = json.loads((destination / "lake-manifest.json").read_text())["packages"]
        self.assertEqual({entry["name"] for entry in entries}, {"mathlib", "erdos249257"})
        self.assertTrue(all(entry["type"] == "path" for entry in entries))
        self.assertEqual((destination / "Consumer.lean").read_bytes(),
                         (self.root / "research/examples/Examples.lean").read_bytes())

    def test_missing_build_is_not_success(self):
        (self.root / ".lake/build/lib/lean/ErdosProblems.olean").unlink()
        with self.assertRaisesRegex(ValueError, "build ErdosProblems first"):
            reuse.prepare_consumer(self.root, Path(self.temp.name) / "consumer")

    def test_missing_dependency_does_not_trigger_download(self):
        (self.root / ".lake/packages/mathlib/lakefile.lean").unlink()
        with self.assertRaisesRegex(ValueError, "prepared dependency mathlib is missing"):
            reuse.prepare_consumer(self.root, Path(self.temp.name) / "consumer")

    def test_checker_uses_lake_resolution_and_preserves_failed_lean_exit(self):
        commands = []
        def runner(command, **kwargs):
            commands.append(command)
            self.assertNotEqual(kwargs["cwd"], self.root)
            self.assertTrue((kwargs["cwd"] / "Consumer.lean").is_file())
            self.assertEqual(kwargs["timeout"], 300)
            self.assertNotIn("LEAN_PATH", kwargs["env"])
            return subprocess.CompletedProcess(command, 17)
        with patch.object(reuse.singleflight, "ensure_state_root", return_value={}), \
             patch.object(reuse.singleflight, "resource_lock_path", return_value=Path(self.temp.name) / "lock"):
            self.assertEqual(reuse.check(self.root, runner=runner), 17)
        self.assertEqual(commands, [["elan", "run", "leanprover/lean4:v4.29.1", "lake", "env", "lean", "Consumer.lean"]])

    def test_busy_host_does_not_launch_a_competing_process(self):
        with patch.object(reuse.singleflight, "ensure_state_root", return_value={}), \
             patch.object(reuse.singleflight, "resource_lock_path", return_value=Path(self.temp.name) / "lock"), \
             patch.object(reuse.singleflight, "open_lock", return_value=None):
            self.assertEqual(reuse.check(self.root, runner=lambda *_a, **_k: self.fail("competing launch")), 75)


if __name__ == "__main__":
    unittest.main()
