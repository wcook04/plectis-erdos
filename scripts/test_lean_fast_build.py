#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the public bounded Lean build planner."""

from __future__ import annotations

import os
from pathlib import Path
import re
import tempfile
import threading
import time
import tomllib
import unittest
from unittest import mock

import lean_fast_build as fast
import validation_singleflight as singleflight


class LeanFastBuildTests(unittest.TestCase):
    def test_problem_library_preserves_interpreter_stack_headroom(self) -> None:
        lakefile = tomllib.loads((fast.ROOT / "lakefile.toml").read_text(
            encoding="utf-8"
        ))
        problem_libraries = [
            library
            for library in lakefile["lean_lib"]
            if library.get("name") == "ErdosProblems"
        ]

        self.assertEqual(len(problem_libraries), 1)
        self.assertEqual(
            problem_libraries[0].get("weakLeanArgs"),
            ["--tstack=65536"],
        )

    def test_automatic_worker_default_is_memory_bounded(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(
            fast.os, "cpu_count", return_value=64
        ):
            self.assertEqual(fast.default_jobs(), 2)

    def test_ci_restores_cache_before_running_bounded_trace_aware_build(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        cache_step = workflow.index("- name: Restore project Lean cache")
        toolchain_step = workflow.index("- name: Install pinned Lean toolchain")
        dependencies_step = workflow.index(
            "- name: Fetch pinned dependency build artifacts"
        )
        bounded_build = workflow.index(
            "run: python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness"
        )

        self.assertLess(cache_step, toolchain_step)
        self.assertLess(toolchain_step, dependencies_step)
        self.assertLess(dependencies_step, bounded_build)
        self.assertIn("uses: actions/cache@", workflow)
        # The contract is that the cache action is pinned to a commit and
        # annotated with the version that commit is, so a reader can tell what
        # a forty-character hex string is without leaving the file. It is not
        # that the version is any particular number: this line asserted
        # "# v5" literally, so Dependabot bumping the cache action to v6 failed
        # four jobs with the message "Lean CI lost cache/build contract" —
        # which was not true, and pointed at the workflow rather than at the
        # assertion. Every other token in this contract describes behaviour.
        self.assertRegex(workflow, r"uses: actions/cache@[0-9a-f]{40} # v\d")
        self.assertIn("path: .lake", workflow)
        # Sibling sweep: the same supply-chain policy applies to every action
        # this workflow uses, and only the cache line was ever checked.
        for line in workflow.splitlines():
            stripped = line.strip()
            if not stripped.startswith(("- uses: actions/", "uses: actions/")):
                continue
            self.assertRegex(
                stripped,
                r"uses: actions/[\w-]+@[0-9a-f]{40} # v[\d.]+$",
                msg=(
                    "workflow action is not pinned to a commit with a version "
                    f"comment: {stripped}"
                ),
            )
        # The fetch step is a multi-line `run: |` block since #41, so pin the
        # command itself rather than one YAML rendering of it.
        self.assertIn("lake exe cache get", workflow)
        self.assertNotIn("leanprover/lean-action@", workflow)
        self.assertIn("final serialized Lake checks remain the proof-authority check", workflow)

    def test_ci_installs_lean_from_checksum_verified_primary_source(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        setup = workflow[
            workflow.index("- name: Install pinned Lean toolchain") :
            workflow.index("- name: Memory-bounded Lean build")
        ]

        self.assertIn("if: steps.lean-inputs.outputs.changed == 'true'", setup)
        self.assertIn(
            "https://github.com/leanprover/elan/releases/download/v4.2.3/"
            "elan-x86_64-unknown-linux-gnu.tar.gz",
            setup,
        )
        self.assertIn(
            "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2",
            setup,
        )
        self.assertIn("sha256sum --check -", setup)
        self.assertIn("--default-toolchain none --no-modify-path", setup)
        self.assertIn('toolchain install "$(tr -d \'\\r\\n\' < lean-toolchain)"', setup)
        self.assertIn('echo "$HOME/.elan/bin" >> "$GITHUB_PATH"', setup)

    def test_cache_warm_installs_lean_from_the_same_checksum_verified_source(self) -> None:
        lean_workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        warm_workflow = (
            fast.ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
        ).read_text(encoding="utf-8")
        lean_setup = lean_workflow[
            lean_workflow.index("- name: Install pinned Lean toolchain") :
            lean_workflow.index("- name: Memory-bounded Lean build")
        ]
        warm_setup = warm_workflow[
            warm_workflow.index("- name: Install pinned Lean toolchain") :
            warm_workflow.index("- name: Fetch pinned dependency build artifacts")
        ]

        for marker in (
            "ELAN_ARCHIVE_URL: https://github.com/leanprover/elan/releases/download/v4.2.3/",
            "ELAN_ARCHIVE_SHA256: df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2",
            "sha256sum --check -",
            'toolchain install "$(tr -d \'\\r\\n\' < lean-toolchain)"',
        ):
            self.assertIn(marker, lean_setup)
            self.assertIn(marker, warm_setup)

    def test_ci_fetches_dependency_artifacts_before_the_bounded_build(self) -> None:
        # A cold Actions cache must not fall through to compiling Mathlib from
        # source: that cannot finish inside the runner job ceiling, so the
        # required build check becomes structurally unsatisfiable. The fetch
        # uses Lake's own tooling, keeping the no-composite-action contract.
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        toolchain_step = workflow.index("- name: Install pinned Lean toolchain")
        artifact_fetch = workflow.index(
            "- name: Fetch pinned dependency build artifacts"
        )
        bounded_build = workflow.index(
            "run: python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness"
        )

        self.assertLess(toolchain_step, artifact_fetch)
        self.assertLess(artifact_fetch, bounded_build)
        self.assertIn("lake exe cache get", workflow)
        self.assertNotIn("leanprover/lean-action@", workflow)

    def test_ci_pins_external_actions_to_full_commit_shas(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        action_lines = [
            line.strip() for line in workflow.splitlines() if "uses:" in line
        ]

        self.assertTrue(action_lines)
        for line in action_lines:
            if "uses: ./" in line:
                continue
            self.assertRegex(
                line,
                re.compile(r"uses:\s+[^\s@]+@[0-9a-f]{40}(?:\s+#\s+\S+)?$"),
                f"external action is not pinned to a full commit SHA: {line}",
            )

    def test_external_verification_pins_the_go_patch_release(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )

        self.assertEqual(workflow.count("go-version:"), 1)
        self.assertIn('go-version: "1.24.12"', workflow)
        self.assertNotIn('go-version: "1.24.x"', workflow)

    def test_cache_warm_checkout_does_not_persist_credentials(self) -> None:
        workflow = (
            fast.ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
        ).read_text(encoding="utf-8")
        checkout = workflow.index("- uses: actions/checkout@")
        cache = workflow.index("- name: Restore project Lean cache")
        checkout_step = workflow[checkout:cache]

        self.assertIn(
            "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
            checkout_step,
        )
        self.assertIn("persist-credentials: false", checkout_step)
        self.assertIn("runs-on: ubuntu-24.04", workflow)
        self.assertNotIn("runs-on: ubuntu-latest", workflow)

    def test_fixed_ci_jobs_use_stable_ubuntu_image_and_keep_reader_matrix(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )

        self.assertEqual(workflow.count("runs-on: ubuntu-24.04"), 5)
        self.assertIn('os: ["macos-latest", "ubuntu-latest"]', workflow)
        self.assertNotIn("runs-on: ubuntu-latest", workflow)

    def test_every_lean_checkout_disables_credential_persistence(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        checkouts = re.findall(
            r"(?ms)^      - uses: actions/checkout@.*?(?=^      - |\Z)",
            workflow,
        )

        self.assertEqual(len(checkouts), 6)
        for checkout in checkouts:
            self.assertIn("persist-credentials: false", checkout)

    def test_ci_does_not_repeat_required_pr_checks_after_merge(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        triggers = workflow[workflow.index("on:\n") : workflow.index("concurrency:\n")]

        self.assertIn("\n  pull_request:\n", triggers)
        self.assertIn("\n  workflow_dispatch:\n", triggers)
        self.assertNotIn("\n  push:\n", triggers)
        self.assertIn("Main is protected with both jobs", workflow)
        self.assertIn("If branch protection is relaxed, restore push validation", workflow)

    def test_every_lake_library_root_is_watched_by_some_ci_gate(self) -> None:
        """A Lean library nobody watches is a Lean library CI never compiles.

        `lean.yml` decides whether to build from a pathspec, so a library whose
        source root is absent from every gate is silently exempt: its `.lean`
        files can stop compiling and every required check still reports green.
        That is how `adapters/` -- the modules an upstream `formal_proof` link
        actually resolves to -- went unbuilt while its permalinks were being
        published.

        The two gates are not interchangeable. `lean-inputs` drives the core
        build; `external-inputs` drives the Comparator packet, and
        `test_external_verification.py` requires that `ExternalVerification`
        appear only in the latter. So the contract is coverage by *some* gate,
        with that one library pinned to its own.
        """
        lakefile = tomllib.loads(
            (fast.ROOT / "lakefile.toml").read_text(encoding="utf-8")
        )
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )

        roots = [
            library.get("srcDir") or library["name"]
            for library in lakefile["lean_lib"]
        ]
        self.assertGreaterEqual(len(roots), 6, "lakefile declares too few libraries")

        core = workflow.split("- name: Detect supported-root Lean changes", 1)[1]
        core = core.split("- name: Test pinned proof-environment lock", 1)[0]
        external = workflow.split("id: external-inputs", 1)[1]
        external = external.split("- name: Initialize failure-safe", 1)[0]

        for root in roots:
            with self.subTest(root=root):
                self.assertTrue(
                    root in core or root in external,
                    f"lake library root {root!r} is in no CI gate, so changes "
                    f"to it never trigger a Lean build",
                )

        self.assertNotIn(
            "ExternalVerification",
            core,
            "ExternalVerification belongs to external-inputs; putting it in the "
            "core gate makes every packet edit a full corpus rebuild and fails "
            "test_external_verification.py",
        )
        self.assertIn("adapters", core)

    def test_a_separate_workflow_warms_the_main_cache(self) -> None:
        """`lean.yml` has no push trigger, so something else must warm main.

        `actions/cache` scopes an entry to the ref that saved it: a branch
        reads its own caches and the default branch's, never a sibling's. With
        nothing running on main, nothing saves a cache there, and every branch
        cut from main restores whatever main last managed to store. That is not
        hypothetical -- the newest `refs/heads/main` entry sat at 2026-08-03
        while main moved through six merges, and a one-module adapter change
        paid 44 minutes to rebuild the corpus and 47 more to re-export the
        dependency index.

        The warm workflow is the fix, and it is only a fix while its cache key
        still matches the one `lean.yml` restores from.
        """
        warm_path = fast.ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
        self.assertTrue(
            warm_path.exists(),
            "no workflow warms main's Lean cache; every branch will rebuild "
            "the corpus from whatever main last stored",
        )
        warm = warm_path.read_text(encoding="utf-8")
        lean = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )

        self.assertIn("\n  push:\n", warm)
        self.assertIn("- main", warm)

        key = (
            "lake-${{ runner.os }}-${{ runner.arch }}-"
            "${{ hashFiles('lean-toolchain') }}-"
            "${{ hashFiles('lake-manifest.json') }}"
        )
        self.assertIn(key, warm, "warm cache key diverged from lean.yml's")
        self.assertIn(key, lean)

        # The saved cache is only useful if it carries what the slow steps
        # consume: project OLeans and the dependency-index receipt.
        self.assertIn("lean_fast_build.py", warm)
        self.assertIn("build_lean_dependency_index.py", warm)

        # It must not become a second copy of the required PR checks, which is
        # what test_ci_does_not_repeat_required_pr_checks_after_merge forbids.
        self.assertNotIn("check_release.py", warm)

    def test_reachable_and_waves_limit_focused_target(self) -> None:
        graph = {
            "Root": {"Left", "Right"},
            "Left": {"Shared"},
            "Right": set(),
            "Shared": set(),
        }
        selected = fast.reachable(["Left"], graph)
        self.assertEqual(selected, {"Left", "Shared"})
        self.assertEqual(fast.waves(selected, graph), [["Shared"], ["Left"]])

    def test_reachable_graph_skips_unrelated_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            modules = {}
            for name, source_text in {
                "Pkg.Base": "-- base\n",
                "Pkg.Main": "import Pkg.Base\n",
                "Other.Expensive": "-- unrelated\n",
            }.items():
                source = root / Path(*name.split(".")).with_suffix(".lean")
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text(source_text, encoding="utf-8")
                modules[name] = source

            self.assertEqual(
                fast.reachable_graph(["Pkg.Main"], modules),
                {"Pkg.Main": {"Pkg.Base"}, "Pkg.Base": set()},
            )

    def test_local_imports_filters_comments_and_external_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Main.lean"
            source.write_text(
                "-- import Pkg.Commented\nimport Pkg.Local\nimport Mathlib\n",
                encoding="utf-8",
            )
            modules = {"Pkg.Local": Path(directory) / "Local.lean"}

            self.assertEqual(fast.local_imports(source, modules), {"Pkg.Local"})

    def test_local_imports_reads_only_the_lean_header(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Main.lean"
            source.write_text(
                """prelude
/- outer comment
   /- nested import Pkg.Commented -/
-/
import Pkg.Local -- retained
def marker := True
import Pkg.TooLate
""",
                encoding="utf-8",
            )
            modules = {
                "Pkg.Commented": Path(directory) / "Commented.lean",
                "Pkg.Local": Path(directory) / "Local.lean",
                "Pkg.TooLate": Path(directory) / "TooLate.lean",
            }

            self.assertEqual(fast.local_imports(source, modules), {"Pkg.Local"})

    def test_build_wave_reports_only_failed_modules(self) -> None:
        results = {
            "Pkg.Good": ("Pkg.Good", 0, 0.1),
            "Pkg.Bad": ("Pkg.Bad", 1, 0.2),
        }
        with mock.patch.object(fast, "build_batch", return_value=(1, 0.3)), mock.patch.object(
            fast, "build_one", side_effect=lambda name, root=fast.ROOT: results[name]
        ):
            self.assertEqual(
                fast.build_wave(["Pkg.Good", "Pkg.Bad"], jobs=2),
                ["Pkg.Bad"],
            )

    def test_build_wave_batches_at_the_worker_bound(self) -> None:
        batches: list[list[str]] = []

        def build_batch(names, root=fast.ROOT):
            batches.append(list(names))
            return 0, 0.02

        with mock.patch.object(fast, "build_batch", side_effect=build_batch):
            self.assertEqual(
                fast.build_wave([f"Pkg.{name}" for name in "ABCD"], jobs=2),
                [],
            )

        self.assertEqual(batches, [["Pkg.A", "Pkg.B"], ["Pkg.C", "Pkg.D"]])

    def test_partial_cache_still_uses_lake_trace_staleness(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Root.lean"
            source.parent.mkdir()
            source.write_text("-- source\n", encoding="utf-8")
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast, "lake_stale_targets", return_value=["Pkg.Root"]
            ) as stale_targets, mock.patch.object(
                fast, "build_wave", return_value=[]
            ), mock.patch.object(fast.subprocess, "run", return_value=completed):
                self.assertEqual(
                    fast.main(["Pkg.Root", "--lake-staleness"]),
                    0,
                )

            stale_targets.assert_called_once_with(["Pkg.Root"], root)

    def test_lake_stale_targets_parses_single_verbose_verdict(self) -> None:
        output = """progress\nSome required targets logged failures:\n- Pkg.A\n- Pkg.B\n"""
        completed = fast.subprocess.CompletedProcess([], 3, output, "")
        with mock.patch.object(fast.subprocess, "run", return_value=completed) as run:
            self.assertEqual(
                fast.lake_stale_targets(["Pkg.Root"], Path("/tmp/pkg")),
                ["Pkg.A", "Pkg.B"],
            )

        self.assertEqual(
            run.call_args.args[0],
            ["lake", "--rehash", "--no-build", "-v", "build", "+Pkg.Root"],
        )

    def test_stale_frontier_propagates_to_every_import_dependent(self) -> None:
        graph = {
            "Pkg.A": set(),
            "Pkg.B": {"Pkg.A"},
            "Pkg.C": set(),
            "Pkg.Root": {"Pkg.B", "Pkg.C"},
        }
        build_waves = [["Pkg.A", "Pkg.C"], ["Pkg.B"], ["Pkg.Root"]]
        self.assertEqual(
            fast.propagate_stale_targets(["Pkg.A"], build_waves, graph),
            {"Pkg.A", "Pkg.B", "Pkg.Root"},
        )

    def test_plan_lines_are_compact_unless_verbose(self) -> None:
        waves = [["Pkg.A", "Pkg.B"], ["Pkg.Root"]]

        self.assertEqual(
            fast.plan_lines(waves, verbose=False),
            ["wave 1: 2 module(s)", "wave 2: 1 module(s)"],
        )
        self.assertEqual(
            fast.plan_lines(waves, verbose=True),
            ["wave 1: Pkg.A Pkg.B", "wave 2: Pkg.Root"],
        )

    def test_discovery_ignores_ephemeral_underscore_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            source.parent.mkdir()
            source.write_text("-- source\n", encoding="utf-8")
            (root / "_axcheck.lean").write_text("#check True\n", encoding="utf-8")
            hidden = root / ".lake" / "Fake.lean"
            hidden.parent.mkdir()
            hidden.write_text("#check False\n", encoding="utf-8")

            self.assertEqual(set(fast.discover(root)), {"Pkg.Leaf"})

    def test_resolve_targets_accepts_module_and_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            source.parent.mkdir()
            source.write_text("-- test\n", encoding="utf-8")
            modules = {"Pkg.Leaf": source}
            self.assertEqual(fast.resolve_targets(["Pkg.Leaf"], modules, root), ["Pkg.Leaf"])
            self.assertEqual(fast.resolve_targets(["Pkg/Leaf.lean"], modules, root), ["Pkg.Leaf"])
            with self.assertRaisesRegex(ValueError, "unknown local Lean target"):
                fast.resolve_targets(["Pkg.Missing"], modules, root)

    def test_default_root_targets_selects_only_top_level_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = root / "Erdos249257.lean"
            second = root / "ErdosProblems.lean"
            nested = root / "ErdosProblems" / "Erdos243" / "Proof.lean"
            nested.parent.mkdir(parents=True)
            for source in (first, second, nested):
                source.write_text("-- source\n", encoding="utf-8")
            modules = {
                "Erdos249257": first,
                "ErdosProblems": second,
                "ErdosProblems.Erdos243.Proof": nested,
            }

            self.assertEqual(
                fast.resolve_targets([], modules, root),
                ["Erdos249257", "ErdosProblems"],
            )

    def test_changed_targets_combines_tracked_and_untracked_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tracked = root / "Pkg" / "Tracked.lean"
            untracked = root / "Pkg" / "Untracked.lean"
            tracked.parent.mkdir()
            tracked.write_text("-- tracked\n", encoding="utf-8")
            untracked.write_text("-- untracked\n", encoding="utf-8")
            modules = {"Pkg.Tracked": tracked, "Pkg.Untracked": untracked}
            results = [
                fast.subprocess.CompletedProcess([], 0, "Pkg/Tracked.lean\nREADME.md\n", ""),
                fast.subprocess.CompletedProcess([], 0, "Pkg/Untracked.lean\n", ""),
            ]
            with mock.patch.object(fast.subprocess, "run", side_effect=results) as run:
                self.assertEqual(
                    fast.changed_targets("HEAD~1", modules, root),
                    ["Pkg.Tracked", "Pkg.Untracked"],
                )
            self.assertEqual(run.call_count, 2)
            self.assertIn("HEAD~1", run.call_args_list[0].args[0])
            for call in run.call_args_list:
                self.assertEqual(
                    call.kwargs["env"], singleflight.command_environment()
                )
                self.assertEqual(
                    call.kwargs["timeout"], fast.GIT_COMMAND_TIMEOUT_SECONDS
                )

    def test_lake_commands_use_clean_environment_and_bounded_deadline(self) -> None:
        completed = fast.subprocess.CompletedProcess([], 0, "", "")
        with mock.patch.object(fast.subprocess, "run", return_value=completed) as run:
            self.assertTrue(fast.lake_targets_up_to_date(["Pkg.Leaf"]))

        self.assertEqual(run.call_args.kwargs["env"], singleflight.command_environment())
        self.assertEqual(
            run.call_args.kwargs["timeout"], fast.LAKE_COMMAND_TIMEOUT_SECONDS
        )

    def test_changed_targets_reports_git_failure(self) -> None:
        failed = fast.subprocess.CompletedProcess([], 128, "", "bad revision")
        with mock.patch.object(fast.subprocess, "run", return_value=failed):
            with self.assertRaisesRegex(RuntimeError, "bad revision"):
                fast.changed_targets("missing", {})

    def test_no_change_main_skips_module_discovery(self) -> None:
        with mock.patch.object(fast, "changed_lean_paths", return_value=set()), mock.patch.object(
            fast, "discover", side_effect=AssertionError("discovery should be skipped")
        ):
            self.assertEqual(fast.main(["--changed-from", "HEAD", "--plan"]), 0)

    def test_config_change_makes_module_stale(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            output = root / ".lake" / "build" / "lib" / "lean" / "Pkg" / "Leaf.olean"
            source.parent.mkdir()
            output.parent.mkdir(parents=True)
            source.write_text("-- source\n", encoding="utf-8")
            output.write_text("olean\n", encoding="utf-8")
            os.utime(source, ns=(1_000_000_000, 1_000_000_000))
            os.utime(output, ns=(2_000_000_000, 2_000_000_000))
            modules = {"Pkg.Leaf": source}
            graph = {"Pkg.Leaf": set()}
            self.assertFalse(fast.stale("Pkg.Leaf", modules, graph, root))

            config = root / "lean-toolchain"
            config.write_text("leanprover/lean4:test\n", encoding="utf-8")
            os.utime(config, ns=(3_000_000_000, 3_000_000_000))
            self.assertTrue(fast.stale("Pkg.Leaf", modules, graph, root))

    def test_stale_accepts_precomputed_build_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            source.parent.mkdir()
            source.write_text("-- source\n", encoding="utf-8")
            os.utime(source, ns=(1_000_000_000, 1_000_000_000))

            self.assertFalse(
                fast.stale(
                    "Pkg.Leaf",
                    {"Pkg.Leaf": source},
                    {"Pkg.Leaf": set()},
                    root,
                    cached_olean_mtimes={"Pkg.Leaf": 2_000_000_000},
                    cached_config_mtime_ns=1_500_000_000,
                )
            )

    def test_lake_stale_targets_falls_back_to_bisection(self) -> None:
        calls: list[tuple[list[str], bool]] = []

        def run(command, **kwargs):
            targets = [arg.removeprefix("+") for arg in command if arg.startswith("+")]
            calls.append((targets, "--rehash" in command))
            return fast.subprocess.CompletedProcess(
                command,
                3 if "Pkg.Bad" in targets else 0,
                "diagnostic without a failure summary",
                "",
            )

        with mock.patch.object(fast.subprocess, "run", side_effect=run):
            self.assertEqual(
                fast.lake_stale_targets(["Pkg.A", "Pkg.Bad", "Pkg.C"]),
                ["Pkg.Bad"],
            )

        self.assertEqual(calls[0], (["Pkg.A", "Pkg.Bad", "Pkg.C"], True))
        self.assertTrue(all(not rehash for _, rehash in calls[1:]))

    def test_lake_trace_check_uses_rehash_and_never_builds(self) -> None:
        completed = fast.subprocess.CompletedProcess([], 0, "", "")
        with mock.patch.object(fast.subprocess, "run", return_value=completed) as run:
            self.assertTrue(fast.lake_targets_up_to_date(["Pkg.Leaf"]))

        self.assertEqual(
            run.call_args.args[0],
            ["lake", "--rehash", "--no-build", "build", "+Pkg.Leaf"],
        )
        self.assertIs(run.call_args.kwargs["stdout"], fast.subprocess.DEVNULL)
        self.assertIs(run.call_args.kwargs["stderr"], fast.subprocess.DEVNULL)

    def test_current_cached_root_skips_every_prebuild_wave(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Root.lean"
            output = root / ".lake" / "build" / "lib" / "lean" / "Pkg" / "Root.olean"
            source.parent.mkdir()
            output.parent.mkdir(parents=True)
            source.write_text("-- source\n", encoding="utf-8")
            output.write_text("olean\n", encoding="utf-8")
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast, "lake_stale_targets", return_value=[]
            ) as stale_targets, mock.patch.object(
                fast, "build_wave", side_effect=AssertionError("cache hit must skip prebuild")
            ), mock.patch.object(fast.subprocess, "run", return_value=completed) as run:
                self.assertEqual(fast.main(["Pkg.Root", "--lake-staleness"]), 0)

            stale_targets.assert_called_once_with(["Pkg.Root"], root)
            self.assertEqual(
                run.call_args.args[0],
                [
                    "lake",
                    "--quiet",
                    "--no-ansi",
                    "--log-level=error",
                    "build",
                    "+Pkg.Root",
                ],
            )

    def test_default_main_serializes_every_public_root(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("Erdos249257", "ErdosProblems"):
                source = root / f"{name}.lean"
                output = root / ".lake" / "build" / "lib" / "lean" / f"{name}.olean"
                source.write_text("-- source\n", encoding="utf-8")
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_text("olean\n", encoding="utf-8")
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast, "lake_stale_targets", return_value=[]
            ) as stale_targets, mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(fast.main(["--lake-staleness"]), 0)

            stale_targets.assert_called_once_with(
                ["Erdos249257", "ErdosProblems"], root
            )
            self.assertEqual(
                [call.args[0] for call in run.call_args_list],
                [
                    [
                        "lake", "--quiet", "--no-ansi", "--log-level=error",
                        "build", "+Erdos249257",
                    ],
                    [
                        "lake", "--quiet", "--no-ansi", "--log-level=error",
                        "build", "+ErdosProblems",
                    ],
                ],
            )

    def test_cycle_is_rejected(self) -> None:
        graph = {"A": {"B"}, "B": {"A"}}
        with self.assertRaisesRegex(RuntimeError, "cycle"):
            fast.waves({"A", "B"}, graph)

    def test_focused_main_uses_focused_final_lake_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Leaf.lean"
            output = root / ".lake" / "build" / "lib" / "lean" / "Pkg" / "Leaf.olean"
            source.parent.mkdir()
            output.parent.mkdir(parents=True)
            source.write_text("-- source\n", encoding="utf-8")
            output.write_text("olean\n", encoding="utf-8")
            os.utime(source, ns=(1_000_000_000, 1_000_000_000))
            os.utime(output, ns=(2_000_000_000, 2_000_000_000))
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(fast.main(["Pkg/Leaf.lean"]), 0)

            self.assertEqual(run.call_count, 1)
            self.assertEqual(
                run.call_args.args[0],
                [
                    "lake", "--quiet", "--no-ansi", "--log-level=error",
                    "build", "+Pkg.Leaf",
                ],
            )
            self.assertEqual(run.call_args.kwargs["cwd"], root)

    def test_final_authority_checks_focused_modules_serially(self) -> None:
        completed = fast.subprocess.CompletedProcess([], 0, "", "")
        with mock.patch.object(fast.subprocess, "run", return_value=completed) as run:
            self.assertEqual(fast.run_final_authority_check(["Pkg.A", "Pkg.B"]), 0)

        self.assertEqual(
            [call.args[0] for call in run.call_args_list],
            [
                [
                    "lake", "--quiet", "--no-ansi", "--log-level=error",
                    "build", "+Pkg.A",
                ],
                [
                    "lake", "--quiet", "--no-ansi", "--log-level=error",
                    "build", "+Pkg.B",
                ],
            ],
        )


if __name__ == "__main__":
    unittest.main()
