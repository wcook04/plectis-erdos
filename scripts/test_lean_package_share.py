#!/usr/bin/env python3
"""Regression tests for public cross-clone Lean package sharing."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import lean_package_share as package_share  # noqa: E402
import lean_fast_build as fast_build  # noqa: E402


class LeanPackageShareTests(unittest.TestCase):
    def make_root(self, parent: Path) -> Path:
        root = parent / "clone"
        root.mkdir()
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
        (root / "lake-manifest.json").write_text(
            json.dumps(
                {
                    "packages": [
                        {
                            "name": "mathlib",
                            "type": "git",
                            "url": "https://example.invalid/mathlib",
                            "rev": "abc123",
                        }
                    ]
                }
            )
        )
        return root

    def test_semantic_fingerprint_is_path_independent(self) -> None:
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            left = self.make_root(Path(first))
            right = self.make_root(Path(second))
            self.assertEqual(
                package_share.semantic_fingerprint(left),
                package_share.semantic_fingerprint(right),
            )

    def test_empty_cold_clone_requests_one_hydration(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            package_share, "load_seed", return_value=None
        ):
            base = Path(directory)
            root = self.make_root(base)
            receipt = package_share.prepare_workspace(root, base / "state")
        self.assertEqual(receipt["status"], "hydrate_then_publish")
        self.assertEqual(receipt["proof_scope"], "cache_acceleration_not_proof_evidence")

    def test_same_lock_seed_attaches_without_full_copy_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root = self.make_root(base)
            source = base / "seed-packages"
            heads = {"mathlib": "abc123"}
            with mock.patch.object(
                package_share, "load_seed", return_value=(source, heads)
            ), mock.patch.object(
                package_share, "lean_process_is_live", return_value=False
            ), mock.patch.object(
                package_share,
                "attach_seed",
                return_value={"schema": package_share.SCHEMA, "status": "attached_host_seed"},
            ) as attach:
                receipt = package_share.prepare_workspace(root, base / "state")
        self.assertEqual(receipt["status"], "attached_host_seed")
        attach.assert_called_once()

    def test_attach_rechecks_process_after_clone_staging(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            package_share, "clone_tree"
        ), mock.patch.object(
            package_share, "package_heads", return_value={"mathlib": "abc123"}
        ), mock.patch.object(
            package_share, "lean_process_is_live", return_value=True
        ):
            base = Path(directory)
            root = self.make_root(base)
            source = base / "seed"
            source.mkdir()
            with self.assertRaisesRegex(
                package_share.PackageShareError, "appeared during package staging"
            ):
                package_share.attach_seed(
                    root, source, "a" * 64, {"mathlib": "abc123"}
                )

    def test_clone_command_refuses_ordinary_copy_fallback(self) -> None:
        with mock.patch.object(package_share.sys, "platform", "win32"):
            self.assertIsNone(
                package_share.copy_on_write_command(Path("source"), Path("target"))
            )

    def test_setup_compression_is_explicitly_optional_off_macos(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            package_share.sys, "platform", "linux"
        ):
            receipt = package_share.compact_setup_json(Path(directory))
        self.assertEqual(receipt["status"], "setup_compression_unsupported")
        self.assertEqual(receipt["proof_scope"], "storage_compaction_not_proof_evidence")

    def test_worker_hydrates_once_then_publishes_seed(self) -> None:
        completed = subprocess.CompletedProcess([], 0)
        with mock.patch.object(
            fast_build.lean_package_share,
            "prepare_workspace",
            side_effect=[
                {"status": "hydrate_then_publish"},
                {"status": "published_host_seed"},
            ],
        ) as prepare, mock.patch.object(
            fast_build, "_run", return_value=completed
        ) as hydrate:
            code = fast_build.prepare_dependency_packages(ROOT)
        self.assertEqual(code, 0)
        self.assertEqual(prepare.call_count, 2)
        self.assertEqual(hydrate.call_args.args[0][-3:], ["exe", "cache", "get"])

    def test_mutable_cache_symlink_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root = self.make_root(base)
            outside = base / "outside"
            outside.mkdir()
            os.symlink(outside, root / ".lake")
            with self.assertRaises(package_share.PackageShareError):
                package_share.prepare_workspace(root, base / "state")

    def test_plan_and_apply_share_the_mutable_symlink_gate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root = self.make_root(base)
            outside = base / "outside"
            outside.mkdir()
            os.symlink(outside, root / ".lake")
            receipt = package_share.plan_workspace(root, base / "state")
        self.assertEqual(receipt["status"], "rejected_mutable_cache_symlink")
        self.assertEqual(receipt["action"], "preserve")


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(LeanPackageShareTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    print(
        json.dumps(
            {
                "schema": "public-lean-package-share-tests/1",
                "tests_run": result.testsRun,
                "successful": result.wasSuccessful(),
            },
            sort_keys=True,
        )
    )
    raise SystemExit(0 if result.wasSuccessful() else 1)
