#!/usr/bin/env python3
"""Regression tests for the public, checkout-independent validation scheduler."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import validation_singleflight as singleflight  # noqa: E402
import lean_fast_build as fast_build  # noqa: E402
import lean_build_share as build_share  # noqa: E402


class ValidationSingleflightTests(unittest.TestCase):
    def setUp(self) -> None:
        self._host_lock_directory = tempfile.TemporaryDirectory()
        self._host_lock_environment = mock.patch.dict(
            os.environ,
            {
                singleflight.HOST_LOCK_ROOT_ENV: str(
                    Path(self._host_lock_directory.name) / "not-created-yet"
                ),
            },
            clear=False,
        )
        self._host_lock_environment.start()

    def tearDown(self) -> None:
        self._host_lock_environment.stop()
        self._host_lock_directory.cleanup()

    def test_cli_honors_selected_test_and_rejects_unknown_selector(self) -> None:
        for selector, successful in (
            ("ValidationSingleflightTests.test_receipt_only_collect_waits_without_build_materialization", True),
            ("ValidationSingleflightTests.test_missing_cli_selector", False),
        ):
            with self.subTest(selector=selector):
                completed = subprocess.run(
                    [sys.executable, str(Path(__file__).resolve()), selector],
                    cwd=ROOT,
                    env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
                    capture_output=True,
                    text=True,
                    timeout=15,
                    check=False,
                )
                summary = json.loads(completed.stdout.strip().splitlines()[-1])
                self.assertEqual(completed.returncode, 0 if successful else 1, completed.stderr)
                self.assertEqual(summary, {
                    "schema": "public-validation-singleflight-tests/1",
                    "tests_run": 1,
                    "successful": successful,
                })
                self.assertIn("Ran 1 test", completed.stderr)

    @staticmethod
    def _safe_spec(command: list[str]) -> dict[str, object]:
        inputs = {
            "repository": {"fixture": True},
            "validation_class": "lean",
            "normalized_command": command,
            "toolchain": {"fixture": True},
            "relevant_sources": [],
        }
        key = singleflight.hashlib.sha256(
            singleflight.canonical_json(inputs)
        ).hexdigest()
        return {
            "schema": singleflight.SCHEMA,
            "key": key,
            "inputs": inputs,
            "command": command,
        }

    def test_default_state_root_is_host_shared_and_repository_scoped(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.dict(
            os.environ,
            {"XDG_CACHE_HOME": directory},
            clear=False,
        ):
            os.environ.pop(singleflight.SINGLEFLIGHT_STATE_ROOT_ENV, None)
            root = singleflight.default_state_root()
        self.assertEqual(
            root,
            Path(directory)
            / "plectis-lean"
            / "plectis-erdos"
            / "validation-singleflight-v1",
        )
        self.assertNotEqual(root.parent, ROOT)

    def test_explicit_state_root_override_remains_available(self) -> None:
        with mock.patch.dict(
            os.environ,
            {singleflight.SINGLEFLIGHT_STATE_ROOT_ENV: "/tmp/public-lean-shared"},
        ):
            self.assertEqual(
                singleflight.default_state_root(), Path("/tmp/public-lean-shared")
            )

    def test_status_card_omits_the_large_source_manifest(self) -> None:
        receipt = {
            "key": "a" * 64,
            "state": "queued",
            "live": True,
            "resource_group": "lean-host",
            "owner": {"pid": 123, "pgid": 123, "start_token": "fixture"},
            "inputs": {
                "validation_class": "lean",
                "targets": ["Pkg.Root"],
                "relevant_sources": [
                    {"path": f"Pkg/Module{index}.lean", "sha256": "sha256:" + "f" * 64}
                    for index in range(2_000)
                ],
            },
        }
        card = singleflight.status_card(receipt)
        encoded = json.dumps(card)
        self.assertEqual(card["state"], "queued")
        self.assertEqual(card["owner"]["pid"], 123)
        self.assertEqual(card["relevant_source_count"], 2_000)
        self.assertNotIn("relevant_sources", encoded)
        self.assertLess(len(encoded), 2_000)

    def test_status_cli_is_compact_by_default_with_explicit_full_mode(self) -> None:
        parser = singleflight.build_parser()
        compact = parser.parse_args(["status", "--key", "a" * 64])
        full = parser.parse_args(["status", "--key", "a" * 64, "--full"])
        self.assertFalse(compact.full)
        self.assertTrue(full.full)

    def test_heavy_lean_lock_is_host_wide_not_checkout_scoped(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.dict(
            os.environ,
            {
                "XDG_CACHE_HOME": directory,
                singleflight.HOST_LOCK_ROOT_ENV: str(Path(directory) / "host-locks"),
            },
            clear=False,
        ):
            first = singleflight.ensure_state_root(Path(directory) / "clone-a")
            second = singleflight.ensure_state_root(Path(directory) / "clone-b")
            first_lock = singleflight.resource_lock_path(first, "lean-host")
            second_lock = singleflight.resource_lock_path(second, "lean-host")
        self.assertEqual(first_lock, second_lock)
        self.assertEqual(first_lock.name, "resource-lean-host.lock")

    def test_semantic_repository_fingerprint_has_no_checkout_or_commit_identity(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fingerprint = singleflight.worktree_fingerprint(Path(directory))
        self.assertNotIn("repository_root", fingerprint)
        self.assertNotIn("commit", fingerprint)
        self.assertEqual(
            fingerprint["identity_policy"],
            "tree_and_dirty_content_checkout_independent",
        )
        self.assertIn("tree", fingerprint)
        self.assertIn("dirty_fingerprint", fingerprint)

    def test_lean_key_ignores_whole_tree_fingerprint_and_covers_target_closure(
        self,
    ) -> None:
        with mock.patch.object(
            singleflight,
            "worktree_fingerprint",
            side_effect=AssertionError("Lean key consulted unrelated tree state"),
        ):
            specification = singleflight.validator_spec(
                "lean",
                ["ErdosProblems.Erdos249.PeriodMultipleEscape"],
                None,
                Path("/tmp/public-lean-source-key"),
            )
        repository = specification["inputs"]["repository"]
        self.assertEqual(
            repository["identity_policy"],
            "target_transitive_lean_content_and_build_authorities_checkout_independent",
        )
        paths = {
            row["path"] for row in specification["inputs"]["relevant_sources"]
        }
        self.assertIn("lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean", paths)
        self.assertIn("lean/Erdos249257/LcmDiagonalReduction.lean", paths)
        self.assertIn("scripts/validation_singleflight.py", paths)
        self.assertIn("scripts/lean_package_share.py", paths)
        self.assertNotIn("README.md", paths)
        self.assertNotIn(
            "lean/ErdosProblems/Erdos269/PaperR7SeriesIdentification.lean",
            paths,
        )

    def test_lean_key_tracks_target_imports_and_toolchain_but_not_unrelated_lean(
        self,
    ) -> None:
        target = ROOT / "lean/Erdos249257.lean"
        imported = ROOT / "lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean"
        unrelated = ROOT / "lean/ErdosProblems/Erdos269/PaperR7SeriesIdentification.lean"
        content: dict[Path, str] = {}

        def digest(path: Path) -> str:
            return "sha256:" + content.get(path, path.as_posix())

        with (
            mock.patch.object(singleflight, "resolve_lean_target", return_value=target),
            mock.patch.object(
                singleflight,
                "lean_dependency_source_paths",
                return_value=[target, imported],
            ),
            mock.patch.object(singleflight, "digest_file", side_effect=digest),
        ):
            def key() -> str:
                return singleflight.validator_spec(
                    "lean", ["Fixture.Target"], None, Path("/tmp/key-fixture")
                )["key"]

            original = key()
            content[unrelated] = "unrelated-change"
            self.assertEqual(key(), original)
            content[imported] = "import-change"
            after_import = key()
            self.assertNotEqual(after_import, original)
            content[target] = "target-change"
            after_target = key()
            self.assertNotEqual(after_target, after_import)
            content[ROOT / "lean-toolchain"] = "toolchain-change"
            self.assertNotEqual(key(), after_target)

    def test_lean_dependency_key_material_uses_complete_filesystem_import_closure(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {
                "Pkg.Main": "import Pkg.Left Pkg.Right\n",
                "Pkg.Left": "public import Pkg.Base\n",
                "Pkg.Right": "-- right\n",
                "Pkg.Base": "-- base v1\n",
                "Other.Unrelated": "-- unrelated v1\n",
            }
            for name, text in sources.items():
                path = root / Path(*name.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")

            with (
                mock.patch.object(singleflight, "ROOT", root),
                mock.patch.object(fast_build, "ROOT", root),
            ):
                closure = singleflight.lean_dependency_source_paths(["Pkg.Main"])
                first = singleflight.regular_digest_rows(closure)
                unrelated = root / "Other/Unrelated.lean"
                unrelated.write_text("-- unrelated v2\n", encoding="utf-8")
                self.assertEqual(
                    singleflight.regular_digest_rows(
                        singleflight.lean_dependency_source_paths(["Pkg.Main"])
                    ),
                    first,
                )
                base = root / "Pkg/Base.lean"
                base.write_text("-- base v2\n", encoding="utf-8")
                second = singleflight.regular_digest_rows(
                    singleflight.lean_dependency_source_paths(["Pkg.Main"])
                )

            self.assertEqual(
                {row["path"] for row in first},
                {"Pkg/Main.lean", "Pkg/Left.lean", "Pkg/Right.lean", "Pkg/Base.lean"},
            )
            self.assertNotEqual(second, first)

    def test_declared_lake_source_roots_resolve_for_singleflight(self) -> None:
        expected = {
            "Examples": "research/examples/Examples.lean",
            "FormalConjecturesAdapter": "research/adapters/FormalConjecturesAdapter.lean",
            "FormalConjecturesVariants": "research/adapters/FormalConjecturesVariants.lean",
            "ResidualBench": "research/residualbench/ResidualBench.lean",
            "ExternalVerificationPortfolio.Problem249": (
                "research/examples/ExternalVerificationPortfolio/Problem249.lean"
            ),
        }
        self.assertEqual(
            {
                target: singleflight.resolve_lean_target(target)
                .relative_to(singleflight.ROOT)
                .as_posix()
                for target in expected
            },
            expected,
        )

    def test_job_locks_use_a_bounded_bucket_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            state = singleflight.ensure_state_root(Path(directory))
            paths = {
                singleflight.job_lock_path(state, f"{prefix:02x}" + "0" * 62).name
                for prefix in range(256)
            }
        self.assertEqual(len(paths), 256)
        self.assertTrue(all(name.startswith("job-") for name in paths))

    def test_output_log_is_compacted_to_a_bounded_tail(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "stdout.log"
            path.write_bytes(b"x" * 10_000)
            receipt = singleflight.compact_output_log(path, max_bytes=1_024)
            payload = path.read_bytes()
        self.assertTrue(receipt["truncated"])
        self.assertEqual(receipt["observed_bytes"], 10_000)
        self.assertTrue(payload.startswith(singleflight.TRUNCATED_LOG_PREFIX))
        self.assertLessEqual(len(payload), len(singleflight.TRUNCATED_LOG_PREFIX) + 1_024)

    def test_only_external_signal_exits_are_automatic_retry_candidates(self) -> None:
        for code in (-15, -9, 143, 137):
            with self.subTest(code=code):
                self.assertTrue(singleflight.is_external_termination_exit(code))
        for code in (0, 1, 2, 75, singleflight.WORKER_TIMEOUT_EXIT_CODE):
            with self.subTest(code=code):
                self.assertFalse(singleflight.is_external_termination_exit(code))
        self.assertEqual(singleflight.MAX_EXTERNAL_TERMINATION_ATTEMPTS, 3)

    def test_scheduler_cleanup_budget_excludes_cow_package_seeds(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            state = singleflight.ensure_state_root(Path(directory))
            seed = state["root"] / "package-seeds" / ("a" * 64) / "packages"
            seed.mkdir(parents=True)
            (seed / "logical-cache").write_bytes(b"x" * 10_000)
            (state["artifacts"] / "scheduler.log").write_bytes(b"y" * 17)
            bytes_used, _inodes = singleflight.validation_state_usage(state)
        self.assertEqual(bytes_used, 17)

    def test_successful_build_seed_hydrates_an_equivalent_clone(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            producer = base / "producer"
            consumer = base / "consumer"
            state_root = base / "state"
            configuration = '[[lean_lib]]\nname = "Pkg"\nsrcDir = "proof_sources"\n'
            sources = {
                "proof_sources/Pkg/Proof.lean": "import Pkg.Dependency\ntheorem proof : True := by trivial\n",
                "proof_sources/Pkg/Dependency.lean": "theorem dependency : True := by trivial\n",
                "proof_sources/Pkg/ProofExtra.lean": "theorem unrelated : True := by trivial\n",
                "proof_sources/Certificates/LadderT67.lean": "theorem certificate : True := by trivial\n",
            }
            for root in (producer, consumer):
                root.mkdir()
                (root / "lakefile.toml").write_text(configuration, encoding="utf-8")
                for relative, content in sources.items():
                    path = root / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(content, encoding="utf-8")
            inputs = {
                "validation_class": "lean",
                "normalized_command": [
                    sys.executable, "scripts/lean_fast_build.py", "--singleflight-worker",
                    "--singleflight-state-root", str(state_root), "--jobs", "2",
                    "--lake-staleness", "Pkg.Proof",
                ],
                # Real scheduler keys fingerprint unrelated Lean sources too.
                # Only the command's import closure was actually validated.
                "relevant_sources": [
                    {"path": "lakefile.toml", "sha256": singleflight.digest_file(producer / "lakefile.toml")},
                    *[{"path": path, "sha256": singleflight.digest_file(producer / path)} for path in sources],
                ],
            }
            key = singleflight.hashlib.sha256(singleflight.canonical_json(inputs)).hexdigest()
            (state_root / "jobs").mkdir(parents=True)
            (state_root / "jobs" / f"{key}.json").write_text(
                json.dumps({"key": key, "inputs": inputs}), encoding="utf-8"
            )
            source = producer / ".lake/build"
            target = consumer / ".lake/build"
            scoped = [
                "lib/lean/Pkg/Proof.olean", "lib/lean/Pkg/Proof.olean.private",
                "lib/lean/Pkg/Proof.trace", "lib/lean/Pkg/Dependency.olean",
                "ir/Pkg/Proof.c", "ir/Pkg/Proof.setup.json",
            ]
            unrelated = ["lib/lean/Pkg/ProofExtra.olean", "lib/lean/Certificates/LadderT67.olean"]
            for relative in scoped + unrelated:
                for root, content in ((source, "foreign"), (target, "local")):
                    path = root / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(content, encoding="utf-8")

            def copy_fixture(command: list[str], **_kwargs: object) -> subprocess.CompletedProcess[str]:
                destination = Path(command[-1])
                for argument in command[1:-1]:
                    if not argument.startswith("-"):
                        path = Path(argument)
                        shutil.copy2(path, destination / path.name)
                return subprocess.CompletedProcess(command, 0, "", "")

            with mock.patch.object(build_share.subprocess, "run", side_effect=copy_fixture):
                published = build_share.publish(producer, state_root, key)
                self.assertEqual(published["status"], "ready", published)
                seed, _receipt = build_share.seed_paths(state_root, key)
                for relative in scoped:
                    self.assertTrue((seed / relative).is_file(), relative)
                for relative in unrelated:
                    self.assertFalse((seed / relative).exists(), relative)
                hydrated = build_share.hydrate(consumer, state_root, key)
                self.assertEqual(hydrated["status"], "hydrated", hydrated)
                self.assertTrue(build_share.is_materialized(consumer, key))
                for relative in scoped:
                    self.assertEqual((target / relative).read_text(), "foreign", relative)
                for relative in unrelated:
                    self.assertEqual((target / relative).read_text(), "local", relative)

                # Legacy seeds contain an entire foreign build, including outputs
                # outside the selected closure, despite their sources being in
                # the broad key. Hydration must filter those too.
                legacy_extra = "lib/lean/Certificates/AbsentLocally.olean"
                for relative in unrelated + [legacy_extra]:
                    path = seed / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("stale foreign certificate", encoding="utf-8")
                _receipt.write_text(json.dumps({
                    "schema": build_share.SCHEMA, "status": "ready", "key": key,
                }), encoding="utf-8")
                hydrated = build_share.hydrate(consumer, state_root, key)
                self.assertEqual(hydrated["status"], "hydrated", hydrated)
                for relative in unrelated:
                    self.assertEqual((target / relative).read_text(), "local", relative)
                self.assertFalse((target / legacy_extra).exists())

                # The source identity must hold for imports as well as targets.
                dependency = consumer / "proof_sources/Pkg/Dependency.lean"
                dependency.write_text("-- changed after validation\n" + dependency.read_text())
                with mock.patch.object(build_share, "_copy_contents") as copy:
                    rejected = build_share.hydrate(consumer, state_root, key)
                self.assertEqual(rejected["status"], "unavailable")
                self.assertIn("differs from keyed bytes", rejected["reason"])
                copy.assert_not_called()
                dependency.write_text(sources["proof_sources/Pkg/Dependency.lean"])

                # A different source layout cannot reinterpret an old key's scope.
                (consumer / "lakefile.toml").write_text(configuration.replace("proof_sources", "other"))
                with mock.patch.object(build_share, "_copy_contents") as copy:
                    rejected = build_share.hydrate(consumer, state_root, key)
                self.assertEqual(rejected["status"], "unavailable")
                copy.assert_not_called()

    def test_build_sharing_rejects_missing_or_unkeyed_artifact_scope(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            state = Path(directory) / "state"
            build = root / ".lake/build"
            build.mkdir(parents=True)
            marker = build / build_share.MATERIALIZATION_MARKER
            marker.write_text("previous validation\n", encoding="utf-8")
            key = "a" * 64
            seed, receipt = build_share.seed_paths(state, key)
            seed.mkdir(parents=True)
            receipt.write_text(json.dumps({"schema": build_share.SCHEMA, "status": "ready", "key": key}))
            with mock.patch.object(build_share, "_copy_contents") as copy:
                self.assertEqual(build_share.publish(root, state, key)["status"], "unavailable")
                self.assertEqual(build_share.hydrate(root, state, key)["status"], "unavailable")
                (state / "jobs").mkdir()
                (state / "jobs" / f"{key}.json").write_text(json.dumps({
                    "key": key, "inputs": {"validation_class": "lean", "relevant_sources": []},
                }))
                self.assertEqual(build_share.hydrate(root, state, key)["status"], "unavailable")
            copy.assert_not_called()
            self.assertEqual(marker.read_text(), "previous validation\n")

    def test_build_share_scope_resolves_command_targets_and_rejects_missing_import_identity(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "checkout"
            state = Path(directory) / "state"
            sources = {
                "lakefile.toml": 'defaultTargets = ["Pkg.Proof"]\n[[lean_lib]]\nname = "Pkg"\nsrcDir = "src"\n',
                "src/Pkg/Proof.lean": (
                    "/- outer /- nested -/ import Pkg.Other -/\n"
                    "-- import Pkg.Other\nimport Pkg.Dependency\n"
                    "theorem proof : True := by trivial\n"
                ),
                "src/Pkg/Dependency.lean": "import Mathlib\ntheorem dependency : True := by trivial\n",
                "src/Pkg/Other.lean": "theorem other : True := by trivial\n",
                "scratch/probe.lean": "import Pkg.Proof\nexample : True := by trivial\n",
            }
            for relative, content in sources.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")
            (state / "jobs").mkdir(parents=True)

            def receipt(targets: list[str], omitted: str | None = None) -> str:
                inputs = {
                    "validation_class": "lean",
                    "normalized_command": [
                        sys.executable, "scripts/lean_fast_build.py", "--singleflight-worker",
                        "--jobs", "2", *targets,
                    ],
                    "relevant_sources": [
                        {"path": path, "sha256": singleflight.digest_file(root / path)}
                        for path in sources if path != omitted
                    ],
                }
                key = singleflight.hashlib.sha256(singleflight.canonical_json(inputs)).hexdigest()
                (state / "jobs" / f"{key}.json").write_text(json.dumps({"key": key, "inputs": inputs}))
                return key

            for targets in (["Pkg.Proof"], ["src/Pkg/Proof.lean"], []):
                with self.subTest(targets=targets):
                    self.assertEqual(
                        build_share._validated_modules(root, state, receipt(targets)),
                        {Path("Pkg/Proof"), Path("Pkg/Dependency")},
                    )
            self.assertEqual(
                build_share._validated_modules(root, state, receipt(["Pkg.Proof", "Pkg.Other"])),
                {Path("Pkg/Proof"), Path("Pkg/Dependency"), Path("Pkg/Other")},
            )
            standalone_scope = build_share._validated_modules(root, state, receipt(["scratch/probe.lean"]))
            self.assertEqual(standalone_scope, {Path("Pkg/Proof"), Path("Pkg/Dependency")})
            build = root / ".lake/build"
            for name in ("Pkg/Proof", "Pkg/Dependency", "scratch/probe"):
                artifact = build / f"lib/lean/{name}.olean"
                artifact.parent.mkdir(parents=True, exist_ok=True)
                artifact.write_text("old output", encoding="utf-8")
            self.assertEqual(
                build_share._module_artifacts(build, standalone_scope),
                [Path("lib/lean/Pkg/Dependency.olean"), Path("lib/lean/Pkg/Proof.olean")],
            )
            with self.assertRaisesRegex(build_share.BuildShareError, "local import has no keyed source"):
                build_share._validated_modules(root, state, receipt(["Pkg.Proof"], "src/Pkg/Dependency.lean"))
            with self.assertRaisesRegex(build_share.BuildShareError, "unsupported normalized worker option"):
                build_share._validated_modules(root, state, receipt(["--changed-from", "HEAD"]))

    def test_build_share_scope_rejects_unsupported_worker_commands(self) -> None:
        for command in (
            None, [], [sys.executable, "different.py", "--singleflight-worker"],
            [sys.executable, "scripts/lean_fast_build.py", "Pkg.Proof"],
            [sys.executable, "scripts/lean_fast_build.py", "--singleflight-worker", "--jobs"],
            [sys.executable, "scripts/lean_fast_build.py", "--singleflight-worker", "--jobs", "0"],
        ):
            with self.subTest(command=command), self.assertRaises(build_share.BuildShareError):
                build_share._worker_targets({"normalized_command": command})

    def test_build_seed_retention_is_bounded(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            state_root = Path(directory)
            for character in ("a", "b", "c"):
                build, receipt = build_share.seed_paths(state_root, character * 64)
                build.mkdir(parents=True)
                receipt.write_text(
                    json.dumps(
                        {"schema": build_share.SCHEMA, "status": "ready", "key": character * 64}
                    ),
                    encoding="utf-8",
                )
                os.utime(build.parent, ns=(ord(character), ord(character)))
            removed = build_share.prune_seeds(state_root, retain=2)
        self.assertEqual(removed, ["a" * 64])

    def test_build_hydration_uses_copy_on_write_and_preserves_extra_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            source = base / "source"
            target = base / "target"
            source.mkdir()
            target.mkdir()
            (source / "shared.olean").write_text("shared", encoding="utf-8")
            (target / "other.olean").write_text("other", encoding="utf-8")
            if build_share.package_share.copy_on_write_command(source, target) is None:
                self.skipTest("copy-on-write cloning is unavailable")
            build_share._copy_contents(source, target, [Path("shared.olean")])
            self.assertEqual((target / "shared.olean").read_text(), "shared")
            self.assertEqual((target / "other.olean").read_text(), "other")

    def test_automatic_cleanup_is_rate_limited_and_detached(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            singleflight.subprocess, "Popen"
        ) as launch:
            first = singleflight.automatic_cleanup(Path(directory))
            second = singleflight.automatic_cleanup(Path(directory))
        self.assertEqual(first["status"], "cleanup_scheduled")
        self.assertEqual(second["status"], "cleanup_recent")
        launch.assert_called_once()
        self.assertTrue(launch.call_args.kwargs["start_new_session"])

    def test_run_command_and_lean_worker_contract_are_publicly_executable(self) -> None:
        parser = singleflight.build_parser()
        parsed = parser.parse_args(["run", "--class", "lean", "--timeout-seconds", "5"])
        self.assertEqual(parsed.action, "run")
        specification = singleflight.validator_spec(
            "lean", [], None, Path("/tmp/public-lean-spec")
        )
        self.assertIn("--singleflight-worker", specification["command"])
        self.assertIn("--singleflight-state-root", specification["command"])
        completed = subprocess.run(
            [
                sys.executable,
                "scripts/lean_fast_build.py",
                "--singleflight-worker",
                "--jobs",
                "2",
                "--plan",
                "ErdosProblems.Erdos249.PeriodMultipleEscape",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("lean-fast-build: targets=", completed.stdout)

    def test_cold_clone_check_is_a_checkout_scoped_reusable_validation(self) -> None:
        specification = singleflight.validator_spec(
            "cold-clone", [], None, Path("/tmp/public-cold-clone-spec")
        )
        self.assertEqual(
            specification["command"],
            [
                sys.executable,
                "scripts/check_cold_clone_comprehension.py",
                "--singleflight-worker",
            ],
        )
        self.assertEqual(
            specification["inputs"]["repository"]["identity_policy"],
            "tree_and_dirty_content_checkout_independent",
        )
        paths = {
            row["path"] for row in specification["inputs"]["relevant_sources"]
        }
        self.assertIn("scripts/check_cold_clone_comprehension.py", paths)
        self.assertIn("scripts/query_corpus.py", paths)

        release = singleflight.validator_spec(
            "release-worktree", [], None, Path("/tmp/public-release-spec")
        )
        self.assertEqual(
            release["command"],
            [sys.executable, "scripts/check_release.py", "--singleflight-worker"],
        )
        self.assertEqual(
            release["inputs"]["repository"]["identity_policy"],
            "tree_and_dirty_content_checkout_independent",
        )

    def test_dependency_export_modes_have_distinct_shared_owner_keys(self) -> None:
        with mock.patch.object(singleflight, "worktree_fingerprint", return_value={}), \
             mock.patch.object(singleflight, "regular_digest_rows", return_value=[]):
            modes = [(False, False, False), (True, False, False),
                     (True, True, False), (True, True, True)]
            specs = [singleflight.validator_spec(
                "dependency-index", [], None, Path("/tmp/dependency-spec"), check=check,
                dependency_full_check=full, dependency_write_stale=write,
            ) for check, full, write in modes]
        self.assertEqual(len({spec["key"] for spec in specs}), 4)
        self.assertIn("--singleflight-worker", specs[-1]["command"])
        self.assertIn("--full-check", specs[-1]["command"])
        self.assertIn("--write-stale", specs[-1]["command"])
        self.assertEqual(singleflight.RESOURCE_GROUPS["dependency-index"], "lean-host")
        with self.assertRaises(singleflight.ValidationError):
            singleflight.validator_spec("dependency-index", [], None, Path("/tmp/spec"),
                                        dependency_full_check=True)

    def test_identical_jobs_join_and_distinct_lean_jobs_defer_without_queueing(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            singleflight, "automatic_cleanup", return_value={"status": "fixture"}
        ):
            state_root = Path(directory) / "state"
            interval_paths = [Path(directory) / f"interval-{index}.json" for index in range(2)]
            release_paths = [Path(directory) / f"release-{index}" for index in range(2)]
            specifications = []
            for interval_path, release_path in zip(interval_paths, release_paths):
                code = (
                    "import json,time,pathlib; "
                    f"p=pathlib.Path({str(interval_path)!r}); "
                    f"release=pathlib.Path({str(release_path)!r}); "
                    "start=time.time_ns(); p.write_text(json.dumps({'start':start})); "
                    "exec('while not release.exists():\\n    time.sleep(0.01)'); "
                    "p.write_text(json.dumps({'start':start,'end':time.time_ns()}))"
                )
                specifications.append(
                    self._safe_spec([sys.executable, "-c", code])
                )

            first = singleflight.submit(specifications[0], state_root)
            duplicate = singleflight.submit(specifications[0], state_root)
            deadline = singleflight.time.monotonic() + 2
            while not interval_paths[0].exists() and singleflight.time.monotonic() < deadline:
                singleflight.time.sleep(0.01)
            self.assertTrue(interval_paths[0].exists(), first)
            second = singleflight.submit(specifications[1], state_root)
            self.assertEqual(first["key"], duplicate["key"])
            self.assertEqual(duplicate["reuse"], "future")
            deferred, code = singleflight.collect(
                state_root, second["key"], True, 10
            )
            self.assertEqual(code, 75, deferred)
            self.assertEqual(deferred["exit_state"], "resource_busy")
            self.assertEqual(deferred["resource_group"], "lean-host")

            release_paths[0].write_text("release", encoding="utf-8")
            terminal, code = singleflight.collect(
                state_root, first["key"], True, 10
            )
            self.assertEqual(code, 0, terminal)

            retried = singleflight.submit(specifications[1], state_root)
            self.assertNotEqual(retried.get("reuse"), "terminal")
            deadline = singleflight.time.monotonic() + 2
            while not interval_paths[1].exists() and singleflight.time.monotonic() < deadline:
                singleflight.time.sleep(0.01)
            self.assertTrue(interval_paths[1].exists(), retried)
            release_paths[1].write_text("release", encoding="utf-8")
            terminal, code = singleflight.collect(
                state_root, retried["key"], True, 10
            )
            self.assertEqual(code, 0, terminal)

            intervals = [json.loads(path.read_text()) for path in interval_paths]
            self.assertTrue(
                intervals[0]["end"] <= intervals[1]["start"]
                or intervals[1]["end"] <= intervals[0]["start"],
                intervals,
            )

    def test_collect_prefers_terminal_published_during_owner_liveness_check(self) -> None:
        for exit_code in (0, 1):
            with self.subTest(exit_code=exit_code), tempfile.TemporaryDirectory() as directory:
                state_root = Path(directory) / "state"
                state = singleflight.ensure_state_root(state_root)
                specification = self._safe_spec([sys.executable, "-c", "pass"])
                running = {**specification, "state": "running"}
                terminal = {
                    **running,
                    "state": "terminal",
                    "exit_code": exit_code,
                    "exit_state": "passed" if exit_code == 0 else "failed",
                    "stdout": {"tail": "canonical validator result"},
                }
                singleflight.write_receipt(state, specification["key"], running)

                def publish_then_observe_owner_exit(receipt: dict[str, object]) -> bool:
                    self.assertEqual(receipt["state"], "running")
                    singleflight.write_receipt(state, specification["key"], terminal)
                    return False

                with (
                    mock.patch.object(singleflight, "receipt_is_live", side_effect=publish_then_observe_owner_exit) as live,
                    mock.patch.object(singleflight, "load_receipt", wraps=singleflight.load_receipt) as reads,
                    mock.patch.object(singleflight.time, "sleep", side_effect=AssertionError("collector slept")),
                ):
                    observed, code = singleflight.collect(state_root, specification["key"], True, 10)
                self.assertEqual(code, exit_code)
                self.assertEqual(observed, {**terminal, "live": False})
                self.assertNotIn("owner_unavailable", observed)
                self.assertEqual(live.call_count, 1)
                self.assertEqual(reads.call_count, 2)

    def test_receipt_only_collect_waits_without_build_materialization(self) -> None:
        for exit_code in (0, 1):
            with self.subTest(exit_code=exit_code), tempfile.TemporaryDirectory() as directory:
                state_root = Path(directory) / "state"
                specification = self._safe_spec([sys.executable, "scripts/lean_fast_build.py"])
                running = {**specification, "state": "running", "live": True}
                terminal = {
                    **specification,
                    "state": "terminal",
                    "exit_code": exit_code,
                    "exit_state": "passed" if exit_code == 0 else "failed",
                }
                with (
                    mock.patch.object(singleflight, "status", side_effect=[running, terminal]) as status,
                    mock.patch.object(singleflight.time, "sleep") as sleep,
                    mock.patch.object(build_share, "is_materialized") as materialized,
                    mock.patch.object(build_share, "hydrate") as hydrate,
                    mock.patch.object(singleflight, "open_lock") as lock,
                ):
                    observed, code = singleflight.collect(
                        state_root, specification["key"], True, 10,
                        receipt_only=True,
                    )
                self.assertEqual(code, exit_code)
                self.assertEqual(observed, terminal)
                self.assertEqual(status.call_count, 2)
                sleep.assert_called_once_with(0.05)
                materialized.assert_not_called()
                hydrate.assert_not_called()
                lock.assert_not_called()
                self.assertNotIn("build_materialization", observed)

    def test_collect_cli_receipt_only_is_explicit_and_forwarded(self) -> None:
        for receipt_only in (False, True):
            with self.subTest(receipt_only=receipt_only), tempfile.TemporaryDirectory() as directory:
                state_root = Path(directory) / "state"
                receipt = {"key": "a" * 64, "state": "terminal", "exit_code": 0}
                arguments = [
                    "--state-root", str(state_root), "collect", "--key", receipt["key"],
                    "--wait", "--timeout-seconds", "12",
                ]
                if receipt_only:
                    arguments.append("--receipt-only")
                with (
                    mock.patch.object(singleflight, "collect", return_value=(receipt, 0)) as collect,
                    mock.patch.object(singleflight, "emit") as emit,
                ):
                    self.assertEqual(singleflight.main(arguments), 0)
                collect.assert_called_once_with(
                    state_root, receipt["key"], True, 12.0,
                    receipt_only=receipt_only,
                )
                emit.assert_called_once_with(receipt)

    def test_raced_terminal_still_requires_successful_lean_materialization(self) -> None:
        for hydration_status, expected_code in (("hydrated", 0), ("missing", 75)):
            with self.subTest(hydration_status=hydration_status), tempfile.TemporaryDirectory() as directory:
                state_root = Path(directory) / "state"
                state = singleflight.ensure_state_root(state_root)
                specification = self._safe_spec([sys.executable, "scripts/lean_fast_build.py"])
                running = {**specification, "state": "running"}
                terminal = {**running, "state": "terminal", "exit_code": 0, "exit_state": "passed"}
                singleflight.write_receipt(state, specification["key"], running)

                def publish_then_observe_owner_exit(_receipt: dict[str, object]) -> bool:
                    singleflight.write_receipt(state, specification["key"], terminal)
                    return False

                materialization = {"status": hydration_status}
                with (
                    mock.patch.object(singleflight, "receipt_is_live", side_effect=publish_then_observe_owner_exit),
                    mock.patch.object(build_share, "is_materialized", return_value=False),
                    mock.patch.object(build_share, "hydrate", return_value=materialization) as hydrate,
                    mock.patch.object(singleflight.time, "sleep", side_effect=AssertionError("collector slept")),
                ):
                    observed, code = singleflight.collect(state_root, specification["key"], True, 10)
                hydrate.assert_called_once_with(singleflight.ROOT, state_root, specification["key"])
                self.assertEqual(code, expected_code)
                self.assertEqual(observed["state"], "terminal")
                self.assertEqual(observed["build_materialization"], materialization)
                self.assertNotIn("owner_unavailable", observed)
                if expected_code == 75:
                    self.assertEqual(observed["exit_state"], "build_output_unavailable")

    def test_collect_returns_promptly_when_a_nonterminal_owner_is_gone(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            state_root = Path(directory) / "state"
            state = singleflight.ensure_state_root(state_root)
            specification = self._safe_spec([sys.executable, "-c", "pass"])
            receipt = {
                **specification,
                "state": "queued",
                "created_at": singleflight.utc_now(),
                "updated_at": singleflight.utc_now(),
                "owner": {"pid": 999_999_999, "pgid": 999_999_999, "start_token": "missing"},
                "child": None,
                "artifacts": [],
            }
            singleflight.write_receipt(state, specification["key"], receipt)
            started = singleflight.time.monotonic()
            with (
                mock.patch.object(singleflight, "load_receipt", wraps=singleflight.load_receipt) as reads,
                mock.patch.object(singleflight.time, "sleep", side_effect=AssertionError("collector slept")),
            ):
                observed, code = singleflight.collect(
                    state_root, specification["key"], True, 10
                )
            self.assertEqual(reads.call_count, 2)
            self.assertEqual(singleflight.load_receipt(state, specification["key"]), receipt)
        self.assertEqual(code, 75)
        self.assertTrue(observed["owner_unavailable"])
        self.assertLess(singleflight.time.monotonic() - started, 1)

    def test_old_failed_terminal_is_retried_but_recent_failure_collapses_herd(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            singleflight, "automatic_cleanup", return_value={"status": "fixture"}
        ):
            state_root = Path(directory) / "state"
            state = singleflight.ensure_state_root(state_root)
            specification = self._safe_spec([sys.executable, "-c", "pass"])
            failed = {
                **specification,
                "state": "terminal",
                "exit_code": 1,
                "exit_state": "failed",
                "completed_at": "2000-01-01T00:00:00+00:00",
                "updated_at": "2000-01-01T00:00:00+00:00",
            }
            singleflight.write_receipt(state, specification["key"], failed)
            relaunched = {**specification, "state": "future"}
            with mock.patch.object(
                singleflight, "launch_worker", return_value=relaunched
            ) as launch:
                self.assertEqual(
                    singleflight.submit(specification, state_root), relaunched
                )
            launch.assert_called_once()

            failed["completed_at"] = singleflight.utc_now()
            failed["updated_at"] = failed["completed_at"]
            singleflight.write_receipt(state, specification["key"], failed)
            with mock.patch.object(singleflight, "launch_worker") as launch:
                reused = singleflight.submit(specification, state_root)
            launch.assert_not_called()
            self.assertEqual(reused["reuse"], "terminal")

    def test_external_sigterm_is_resumed_by_the_same_owner(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            singleflight, "automatic_cleanup", return_value={"status": "fixture"}
        ):
            marker = Path(directory) / "first-attempt"
            code = (
                "import os,pathlib,signal,sys; "
                f"assert os.environ.get({singleflight.HOST_LOCK_HELD_ENV!r}) == '1'; "
                f"p=pathlib.Path({str(marker)!r}); "
                "already=p.exists(); "
                "p.write_text('partial progress'); "
                "os.kill(os.getpid(), signal.SIGTERM) if not already else sys.exit(0)"
            )
            specification = self._safe_spec([sys.executable, "-c", code])
            submitted = singleflight.submit(
                specification, Path(directory) / "state"
            )
            terminal, exit_code = singleflight.collect(
                Path(directory) / "state", submitted["key"], True, 15
            )
        self.assertEqual(exit_code, 0, terminal)
        self.assertEqual(terminal["attempt_count"], 2)
        self.assertEqual(terminal["automatic_resume_count"], 1)
        self.assertEqual(terminal["external_termination_exits"], [-15])
        self.assertIn("automatically resuming partial build", terminal["stderr"]["tail"])

    def test_owned_cancel_stops_child_without_retry_and_releases_host_lock(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            singleflight, "automatic_cleanup", return_value={"status": "fixture"}
        ):
            state_root = Path(directory) / "state"
            marker = Path(directory) / "child-ready"
            code = (
                "import pathlib,time; "
                f"pathlib.Path({str(marker)!r}).write_text('ready'); "
                "time.sleep(60)"
            )
            specification = self._safe_spec([sys.executable, "-c", code])
            submitted = singleflight.submit(specification, state_root)
            deadline = singleflight.time.monotonic() + 10
            while not marker.exists() and singleflight.time.monotonic() < deadline:
                singleflight.time.sleep(0.02)
            self.assertTrue(marker.exists())

            result = singleflight.cancel(
                state_root, submitted["key"], "focused validation has priority", 10
            )
            terminal = singleflight.load_receipt(
                singleflight.ensure_state_root(state_root), submitted["key"]
            )
            self.assertEqual(result["status"], "cancelled", result)
            self.assertEqual(terminal["exit_state"], "cancelled")
            self.assertEqual(terminal["exit_code"], singleflight.CANCELLED_EXIT_CODE)
            self.assertEqual(terminal["attempt_count"], 1)
            self.assertEqual(terminal["automatic_resume_count"], 0)
            self.assertEqual(terminal["cancel_request"]["reason"], "focused validation has priority")

            state = singleflight.ensure_state_root(state_root)
            host_lock = singleflight.open_lock(
                singleflight.resource_lock_path(state, "lean-host"), blocking=False
            )
            self.assertIsNotNone(host_lock)
            assert host_lock is not None
            singleflight.fcntl.flock(host_lock, singleflight.fcntl.LOCK_UN)
            os.close(host_lock)

    def test_cancel_during_retry_delay_does_not_spawn_another_validator(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            singleflight, "automatic_cleanup", return_value={"status": "fixture"}
        ), mock.patch.object(
            singleflight, "EXTERNAL_TERMINATION_RETRY_DELAY_SECONDS", 1.0
        ):
            state_root = Path(directory) / "state"
            attempts = Path(directory) / "attempts"
            code = (
                "import os,pathlib,signal; "
                f"p=pathlib.Path({str(attempts)!r}); "
                "p.write_text(p.read_text() + 'x' if p.exists() else 'x'); "
                "os.kill(os.getpid(), signal.SIGTERM)"
            )
            specification = self._safe_spec([sys.executable, "-c", code])
            submitted = singleflight.submit(specification, state_root)
            state = singleflight.ensure_state_root(state_root)
            deadline = singleflight.time.monotonic() + 10
            while singleflight.time.monotonic() < deadline:
                observed = singleflight.load_receipt(state, submitted["key"])
                if observed is not None and observed.get("state") == "retrying_external_termination":
                    break
                singleflight.time.sleep(0.02)
            else:
                self.fail("worker never entered its retry delay")
            result = singleflight.cancel(
                state_root, submitted["key"], "cancel during retry delay", 10
            )
            terminal = singleflight.load_receipt(state, submitted["key"])
            self.assertEqual(result["status"], "cancelled", result)
            self.assertEqual(terminal["exit_state"], "cancelled")
            self.assertEqual(terminal["attempt_count"], 1)
            self.assertEqual(attempts.read_text(), "x")

    def test_cancel_refuses_reused_or_unverifiable_owner_identity(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            state_root = Path(directory) / "state"
            state = singleflight.ensure_state_root(state_root)
            specification = self._safe_spec([sys.executable, "-c", "pass"])
            receipt = {
                **specification,
                "state": "running",
                "launch_token": "launch",
                "owner": {"pid": 123, "pgid": 123, "start_token": "expected"},
                "child": None,
            }
            singleflight.write_receipt(state, specification["key"], receipt)
            with (
                mock.patch.object(
                    singleflight,
                    "process_identity",
                    return_value={"pid": 123, "pgid": 123, "start_token": "reused"},
                ),
                mock.patch.object(singleflight.os, "killpg") as killpg,
            ):
                result = singleflight.cancel(
                    state_root, specification["key"], "fixture", 0
                )
            self.assertEqual(result["status"], "refused_owner_identity_mismatch")
            killpg.assert_not_called()
            self.assertFalse(singleflight.cancel_request_path(state, specification["key"]).exists())

    def test_cancel_never_signals_a_replacement_launch_for_the_same_key(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            state_root = Path(directory) / "state"
            state = singleflight.ensure_state_root(state_root)
            specification = self._safe_spec([sys.executable, "-c", "pass"])
            original_owner = {
                "pid": 123,
                "pgid": 123,
                "start_token": "original-owner",
            }
            original = {
                **specification,
                "state": "running",
                "launch_token": "original-launch",
                "owner": original_owner,
                "child": None,
            }
            replacement = {
                **specification,
                "state": "running",
                "launch_token": "replacement-launch",
                "owner": {
                    "pid": 456,
                    "pgid": 456,
                    "start_token": "replacement-owner",
                },
                "child": {
                    "pid": 789,
                    "pgid": 789,
                    "start_token": "replacement-child",
                },
            }
            singleflight.write_receipt(state, specification["key"], original)
            with (
                mock.patch.object(
                    singleflight,
                    "load_receipt",
                    side_effect=[original, replacement],
                ),
                mock.patch.object(
                    singleflight,
                    "process_identity",
                    return_value=original_owner,
                ),
                mock.patch.object(singleflight.os, "killpg") as killpg,
            ):
                result = singleflight.cancel(
                    state_root, specification["key"], "fixture", 0
                )
            self.assertEqual(result["status"], "refused_launch_changed")
            killpg.assert_not_called()

    def test_cancelled_terminal_is_never_reused_as_success(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            singleflight, "automatic_cleanup", return_value={"status": "fixture"}
        ):
            state_root = Path(directory) / "state"
            state = singleflight.ensure_state_root(state_root)
            specification = self._safe_spec([sys.executable, "-c", "pass"])
            cancelled = {
                **specification,
                "state": "terminal",
                "exit_code": singleflight.CANCELLED_EXIT_CODE,
                "exit_state": "cancelled",
                "completed_at": singleflight.utc_now(),
            }
            singleflight.write_receipt(state, specification["key"], cancelled)
            relaunched = {**specification, "state": "future", "attempt": 2}
            with mock.patch.object(
                singleflight, "launch_worker", return_value=relaunched
            ) as launch:
                self.assertEqual(singleflight.submit(specification, state_root), relaunched)
            launch.assert_called_once_with(state, specification, cancelled)

    def test_public_fast_build_enters_singleflight_before_lake(self) -> None:
        specification = {"key": "f" * 64}
        terminal = {
            "state": "terminal",
            "exit_code": 0,
            "stdout": {"tail": ""},
            "stderr": {"tail": ""},
        }
        with mock.patch.object(
            fast_build.singleflight, "validator_spec", return_value=specification
        ) as make_spec, mock.patch.object(
            fast_build.singleflight,
            "submit",
            return_value={"key": "f" * 64, "reuse": "future"},
        ) as submit, mock.patch.object(
            fast_build.singleflight, "collect", return_value=(terminal, 0)
        ) as collect, mock.patch.object(
            fast_build, "run_final_authority_check", side_effect=AssertionError("Lake bypassed scheduler")
        ):
            code = fast_build.main(
                ["ErdosProblems.Erdos249.PeriodMultipleEscape", "--jobs", "2"]
            )
        self.assertEqual(code, 0)
        self.assertEqual(make_spec.call_args.kwargs["lean_jobs"], 2)
        submit.assert_called_once()
        collect.assert_called_once()

    def test_tracked_worker_commands_accept_the_internal_recursion_flag(self) -> None:
        worker_sources = (
            "scripts/check_cold_clone_comprehension.py",
            "scripts/check_release.py",
            "scripts/lean_fast_build.py",
            "scripts/build_lean_dependency_index.py",
            "scripts/historical_bridge_experiment.py",
            "scripts/dogfood_semantic_proof.py",
            "scripts/check_palomar_qualification.py",
            "docs/papers/check_paper_corpus.py",
        )
        for relative in worker_sources:
            with self.subTest(relative=relative):
                self.assertIn(
                    "--singleflight-worker",
                    (ROOT / relative).read_text(encoding="utf-8"),
                )
        dependency_builder = (
            ROOT / "scripts/build_lean_dependency_index.py"
        ).read_text(encoding="utf-8")
        self.assertIn("singleflight.HOST_LOCK_HELD_ENV", dependency_builder)
        self.assertIn('command.append("--singleflight-worker")', dependency_builder)
        self.assertNotIn("paper-render", singleflight.ROSTER_VALIDATORS)


if __name__ == "__main__":
    result = unittest.main(exit=False, verbosity=2).result
    print(
        json.dumps(
            {
                "schema": "public-validation-singleflight-tests/1",
                "tests_run": result.testsRun,
                "successful": result.wasSuccessful(),
            },
            sort_keys=True,
        )
    )
    raise SystemExit(0 if result.wasSuccessful() else 1)
