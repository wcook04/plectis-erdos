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
            / "plectis-lean-erdos249-257"
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

    def test_lean_key_ignores_whole_tree_fingerprint_and_covers_all_sources(
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
            "all_visible_lean_content_and_build_authorities_checkout_independent",
        )
        paths = {
            row["path"] for row in specification["inputs"]["relevant_sources"]
        }
        self.assertIn("Erdos249257.lean", paths)
        self.assertIn("scripts/validation_singleflight.py", paths)
        self.assertIn("scripts/lean_package_share.py", paths)
        self.assertNotIn("README.md", paths)

    def test_declared_lake_source_roots_resolve_for_singleflight(self) -> None:
        expected = {
            "Examples": "examples/Examples.lean",
            "FormalConjecturesAdapter": "adapters/FormalConjecturesAdapter.lean",
            "FormalConjecturesVariants": "adapters/FormalConjecturesVariants.lean",
            "ResidualBench": "residualbench/ResidualBench.lean",
            "ExternalVerificationPortfolio.Problem249": (
                "examples/ExternalVerificationPortfolio/Problem249.lean"
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
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            build_share.package_share, "clone_tree"
        ) as clone:
            base = Path(directory)
            producer = base / "producer"
            consumer = base / "consumer"
            state_root = base / "state"
            source = producer / ".lake/build"
            source.mkdir(parents=True)
            (source / "Erdos249257.olean").write_text("checked", encoding="utf-8")

            def clone_fixture(origin: Path, target: Path) -> None:
                shutil.copytree(origin, target)

            clone.side_effect = clone_fixture
            published = build_share.publish(producer, state_root, "a" * 64)
            with mock.patch.object(build_share, "_copy_contents") as copy_contents:
                copy_contents.side_effect = lambda _source, target: target.mkdir(
                    parents=True, exist_ok=True
                )
                hydrated = build_share.hydrate(consumer, state_root, "a" * 64)
                materialized = build_share.is_materialized(consumer, "a" * 64)

        self.assertEqual(published["status"], "ready")
        self.assertEqual(hydrated["status"], "hydrated")
        self.assertTrue(materialized)
        copy_contents.assert_called_once()

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
            build_share._copy_contents(source, target)
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
            observed, code = singleflight.collect(
                state_root, specification["key"], True, 10
            )
        self.assertEqual(code, 75)
        self.assertTrue(observed["owner_unavailable"])
        self.assertLess(singleflight.time.monotonic() - started, 1)

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
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(
        ValidationSingleflightTests
    )
    result = unittest.TextTestRunner(verbosity=2).run(suite)
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
