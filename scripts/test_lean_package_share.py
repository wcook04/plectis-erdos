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

    def test_durable_workspace_publishes_pointer_without_duplicate_package_tree(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            package_share, "durable_workspace_reference", return_value=True
        ), mock.patch.object(package_share, "clone_tree") as clone:
            base = Path(directory)
            repo_parent = base / "repo"
            repo_parent.mkdir()
            root = self.make_root(repo_parent)
            (root / ".lake/packages").mkdir(parents=True)
            state_root = base / "state"
            receipt = package_share.publish_seed(
                root,
                state_root,
                "a" * 64,
                {"mathlib": "abc123"},
            )
            seed = json.loads(
                (state_root / "package-seeds" / ("a" * 64) / "seed.json").read_text()
            )

        self.assertEqual(receipt["status"], "published_durable_workspace_reference")
        self.assertEqual(seed["source_role"], "durable_host_workspace_reference")
        self.assertEqual(seed["source_path"], str(root.resolve()))
        self.assertFalse((state_root / "package-seeds" / ("a" * 64) / "packages").exists())
        clone.assert_not_called()

    def test_load_seed_resolves_validated_durable_workspace_pointer(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            package_share, "durable_workspace_reference", return_value=True
        ), mock.patch.object(
            package_share, "package_heads", return_value={"mathlib": "abc123"}
        ):
            base = Path(directory)
            source_root = base / "repo"
            source = source_root / ".lake/packages"
            source.mkdir(parents=True)
            state_root = base / "state"
            _, receipt_path = package_share.seed_paths(state_root, "b" * 64)
            package_share.atomic_json(
                receipt_path,
                {
                    "schema": package_share.SCHEMA,
                    "semantic_fingerprint": "b" * 64,
                    "package_heads": {"mathlib": "abc123"},
                    "source_role": "durable_host_workspace_reference",
                    "source_path": str(source_root),
                },
            )

            loaded = package_share.load_seed(state_root, "b" * 64)

        self.assertEqual(loaded, (source.resolve(), {"mathlib": "abc123"}))

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

    def test_attach_preserves_warm_workspace_outputs_the_seed_lacks(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            package_share, "clone_tree"
        ) as clone:
            base = Path(directory)
            root = self.make_root(base)
            built = root / ".lake/packages/mathlib/.lake/build/lib/Mathlib/Foo.olean"
            built.parent.mkdir(parents=True)
            built.write_bytes(b"warm")
            source = base / "seed"
            (source / "mathlib").mkdir(parents=True)
            receipt = package_share.attach_seed(
                root, source, "a" * 64, {"mathlib": "abc123"}
            )
            self.assertEqual(receipt["status"], "preserved_warm_workspace_artifacts")
            self.assertIn("Foo.olean", receipt["detail"])
            self.assertEqual(built.read_bytes(), b"warm")
            clone.assert_not_called()

    def test_warm_artifact_check_compares_outputs_and_ignores_sources(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            source = base / "seed"
            target = base / "workspace"
            output = "mathlib/.lake/build/lib/Mathlib/Foo.olean"
            for tree in (source, target):
                (tree / output).parent.mkdir(parents=True)
                (tree / output).write_bytes(b"same")
            # Sources, notes and Git internals are not compiled outputs.
            (target / "mathlib/Mathlib").mkdir(parents=True)
            (target / "mathlib/Mathlib/Foo.lean").write_text("theorem foo : True := trivial\n")
            (target / "mathlib/.git/objects").mkdir(parents=True)
            (target / "mathlib/.git/objects/pack").write_bytes(b"git")
            self.assertIsNone(package_share.warm_artifact_mismatch(source, target))
            (source / output).write_bytes(b"diff")
            self.assertEqual(package_share.warm_artifact_mismatch(source, target), output)

    def test_clone_command_refuses_ordinary_copy_fallback(self) -> None:
        with mock.patch.object(package_share.sys, "platform", "win32"):
            self.assertIsNone(
                package_share.copy_on_write_command(Path("source"), Path("target"))
            )

    @unittest.skipUnless(sys.platform == "darwin", "strict APFS clone is macOS-only")
    def test_strict_tree_clone_preserves_file_mode_and_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source"
            target = Path(directory) / "target"
            (source / "nested").mkdir(parents=True)
            artifact = source / "nested/artifact.olean"
            artifact.write_bytes(b"validated")
            artifact.chmod(0o640)
            (source / "link").symlink_to("nested/artifact.olean")
            package_share.clone_tree(source, target)
            self.assertEqual((target / "nested/artifact.olean").read_bytes(), b"validated")
            self.assertEqual((target / "nested/artifact.olean").stat().st_mode & 0o777, 0o640)
            self.assertTrue((target / "link").is_symlink())
            self.assertEqual(os.readlink(target / "link"), "nested/artifact.olean")

    @unittest.skipUnless(sys.platform == "darwin", "strict APFS clone is macOS-only")
    def test_strict_tree_clone_failure_removes_only_new_stage(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source"
            target = root / "target"
            source.mkdir()
            (source / "artifact.olean").write_bytes(b"must remain")
            with mock.patch.object(
                package_share, "clone_file_strict", side_effect=OSError("clone unsupported")
            ):
                with self.assertRaisesRegex(OSError, "clone unsupported"):
                    package_share.clone_tree(source, target)
            self.assertFalse(target.exists())
            self.assertEqual((source / "artifact.olean").read_bytes(), b"must remain")

    @unittest.skipUnless(sys.platform == "darwin", "strict APFS clone is macOS-only")
    def test_clone_failure_survives_stage_cleanup_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source"
            target = Path(directory) / "target"
            source.mkdir()
            (source / "artifact.olean").write_bytes(b"source")
            with mock.patch.object(
                package_share, "clone_file_strict", side_effect=OSError("clone unsupported")
            ), mock.patch.object(
                package_share.shutil, "rmtree", side_effect=OSError("cleanup denied")
            ):
                with self.assertRaisesRegex(OSError, "clone unsupported"):
                    package_share.clone_tree(source, target)
            self.assertEqual((source / "artifact.olean").read_bytes(), b"source")

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
    # An empty selection or an all-skipped run is not a pass: unittest reports
    # wasSuccessful() for both, so the verdict names what actually executed.
    skipped = len(result.skipped)
    if not result.wasSuccessful():
        status = "failed"
    elif result.testsRun == 0:
        status = "no_tests_ran"
    elif skipped >= result.testsRun:
        status = "all_skipped"
    else:
        status = "passed"
    print(
        json.dumps(
            {
                "schema": "public-lean-package-share-tests/2",
                "status": status,
                "tests_run": result.testsRun,
                "skipped": skipped,
                "successful": status == "passed",
            },
            sort_keys=True,
        )
    )
    raise SystemExit({"passed": 0, "failed": 1}.get(status, 5))
