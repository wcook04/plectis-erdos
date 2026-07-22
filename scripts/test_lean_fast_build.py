#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the public bounded Lean build planner."""

from __future__ import annotations

import os
from pathlib import Path
import tempfile
import threading
import time
import unittest
from unittest import mock

import lean_fast_build as fast


class LeanFastBuildTests(unittest.TestCase):
    def test_automatic_worker_default_is_memory_bounded(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(
            fast.os, "cpu_count", return_value=64
        ):
            self.assertEqual(fast.default_jobs(), 2)

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
        with mock.patch.object(
            fast,
            "build_one",
            side_effect=lambda name, root=fast.ROOT: results[name],
        ):
            self.assertEqual(
                fast.build_wave(["Pkg.Good", "Pkg.Bad"], jobs=2),
                ["Pkg.Bad"],
            )

    def test_build_wave_enforces_the_worker_bound(self) -> None:
        active = 0
        maximum = 0
        lock = threading.Lock()

        def build_one(name, root=fast.ROOT):
            nonlocal active, maximum
            with lock:
                active += 1
                maximum = max(maximum, active)
            time.sleep(0.02)
            with lock:
                active -= 1
            return name, 0, 0.02

        with mock.patch.object(fast, "build_one", side_effect=build_one):
            self.assertEqual(
                fast.build_wave([f"Pkg.{name}" for name in "ABCD"], jobs=2),
                [],
            )

        self.assertEqual(maximum, 2)

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

    def test_lake_stale_targets_bisects_to_only_invalid_targets(self) -> None:
        calls: list[tuple[list[str], bool]] = []

        def up_to_date(names, root=fast.ROOT, *, rehash=True):
            targets = list(names)
            calls.append((targets, rehash))
            return "Pkg.Bad" not in targets

        with mock.patch.object(fast, "lake_targets_up_to_date", side_effect=up_to_date):
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
                fast, "lake_targets_up_to_date", return_value=True
            ) as up_to_date, mock.patch.object(
                fast, "build_wave", side_effect=AssertionError("cache hit must skip prebuild")
            ), mock.patch.object(fast.subprocess, "run", return_value=completed) as run:
                self.assertEqual(fast.main(["Pkg.Root", "--lake-staleness"]), 0)

            up_to_date.assert_called_once_with(["Pkg.Root"], root)
            self.assertEqual(run.call_args.args[0], ["lake", "build", "+Pkg.Root"])

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
                fast, "lake_targets_up_to_date", return_value=True
            ) as up_to_date, mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(fast.main(["--lake-staleness"]), 0)

            up_to_date.assert_called_once_with(["Erdos249257", "ErdosProblems"], root)
            self.assertEqual(
                [call.args[0] for call in run.call_args_list],
                [
                    ["lake", "build", "+Erdos249257"],
                    ["lake", "build", "+ErdosProblems"],
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
            self.assertEqual(run.call_args.args[0], ["lake", "build", "+Pkg.Leaf"])
            self.assertEqual(run.call_args.kwargs["cwd"], root)

    def test_final_authority_checks_focused_modules_serially(self) -> None:
        completed = fast.subprocess.CompletedProcess([], 0, "", "")
        with mock.patch.object(fast.subprocess, "run", return_value=completed) as run:
            self.assertEqual(fast.run_final_authority_check(["Pkg.A", "Pkg.B"]), 0)

        self.assertEqual(
            [call.args[0] for call in run.call_args_list],
            [["lake", "build", "+Pkg.A"], ["lake", "build", "+Pkg.B"]],
        )


if __name__ == "__main__":
    unittest.main()
