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


LAKE = str(fast.TOOLCHAIN_BIN / "lake")


LAKE = str(fast.TOOLCHAIN_BIN / "lake")


class LeanFastBuildTests(unittest.TestCase):
    def test_discovery_uses_declared_lake_source_roots(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "examples").mkdir()
            (root / "examples" / "Examples.lean").write_text(
                "-- example\n", encoding="utf-8"
            )
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "Examples"\nsrcDir = "examples"\n',
                encoding="utf-8",
            )

            self.assertEqual(
                fast.discover(root),
                {"Examples": root / "examples" / "Examples.lean"},
            )

    def test_changed_targets_use_discovered_names_under_srcdir(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "lean" / "Pkg" / "Proof.lean"
            source.parent.mkdir(parents=True)
            source.write_text("-- proof\n", encoding="utf-8")
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "Pkg"\nsrcDir = "lean"\n', encoding="utf-8"
            )
            modules = fast.discover(root)
            self.assertEqual(
                fast.changed_targets_from_paths([source, root / "unknown.lean"], modules, root),
                ["Pkg.Proof"],
            )

    def test_changed_targets_exclude_only_stored_workbench_probes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            registered = root / "lean" / "Pkg" / "Proof.lean"
            scratch = root / "scratch" / "Trial.lean"
            session = root / "research" / "workbench" / "sessions" / "replay-case"
            rejected_probe = session / "probes" / "m003.lean"
            standalone_near_probe = session / "probes" / "Draft.lean"
            standalone_other_tree = root / "research" / "experiments" / "probes" / "m003.lean"
            sources = [registered, scratch, rejected_probe, standalone_near_probe,
                       standalone_other_tree]
            for source in sources:
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("example : True := True.intro\n", encoding="utf-8")
            rejected_probe.write_text(
                "example : False := True.intro\n", encoding="utf-8"
            )
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "Pkg"\nsrcDir = "lean"\n', encoding="utf-8"
            )
            modules = fast.discover(root)
            names = {source: name for name, source in modules.items()}
            results = [
                fast.subprocess.CompletedProcess(
                    [], 0, "\n".join(str(p.relative_to(root)) for p in sources[:3]), ""
                ),
                fast.subprocess.CompletedProcess(
                    [], 0, "\n".join(str(p.relative_to(root)) for p in sources[3:]), ""
                ),
            ]
            with mock.patch.object(fast.subprocess, "run", side_effect=results):
                self.assertEqual(
                    fast.changed_targets("HEAD", modules, root),
                    sorted(names[p] for p in sources if p != rejected_probe),
                )
            # The exclusion belongs only to changed-from discovery. A user
            # may still explicitly select a stored probe or a standalone file.
            self.assertEqual(
                fast.resolve_targets(
                    [str(p.relative_to(root)) for p in (rejected_probe, scratch)],
                    modules,
                    root,
                ),
                [names[rejected_probe], names[scratch]],
            )
            self.assertTrue(fast.is_registered_lake_module(names[registered], root))

    def test_declared_defaults_resolve_roots_under_srcdir(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            (root / "examples").mkdir()
            for relative in ("lean/Main.lean", "examples/Examples.lean"):
                (root / relative).write_text("-- root\n", encoding="utf-8")
            (root / "lakefile.toml").write_text(
                'defaultTargets = ["Main"]\n'
                '[[lean_lib]]\nname = "Main"\nsrcDir = "lean"\n'
                '[[lean_lib]]\nname = "Examples"\nsrcDir = "examples"\n',
                encoding="utf-8",
            )
            self.assertEqual(fast.resolve_targets([], fast.discover(root), root), ["Main"])

    def test_missing_declared_default_does_not_silently_skip_build(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text('defaultTargets = ["Missing"]\n')
            with self.assertRaisesRegex(ValueError, "declared default Lean roots not found"):
                fast.default_root_targets({}, root)

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
                r"uses: actions/[\w-]+(?:/[\w-]+)*@[0-9a-f]{40} # v[\d.]+$",
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

    def test_ci_and_cache_warm_use_one_complete_wrapper_owner(self) -> None:
        targets = (
            "Erdos249257",
            "ErdosProblems",
            "Examples",
            "FormalConjecturesAdapter",
            "FormalConjecturesVariants",
            "ResidualBench",
        )
        for relative in (
            ".github/workflows/lean.yml",
            ".github/workflows/lean-cache-warm.yml",
        ):
            workflow = (fast.ROOT / relative).read_text(encoding="utf-8")
            commands = re.findall(
                r"(?m)^\s*run:\s*(python3 scripts/lean_fast_build\.py[^\n]*)$",
                workflow,
            )
            self.assertNotRegex(workflow, r"(?m)^\s*run:\s*lake build\b")
            # Exactly one invocation owns the complete supported-root build.
            # Any other wrapper call must be focused on a library outside
            # that set, such as the external-verification job building the
            # solved-families library its axiom audit imports: a second call
            # naming a supported root would be a duplicate build owner.
            owners = [
                command
                for command in commands
                if all(target in command for target in targets)
            ]
            self.assertEqual(len(owners), 1, f"{relative} has duplicate build owners")
            for command in commands:
                if command in owners:
                    continue
                for target in targets:
                    self.assertNotRegex(
                        command,
                        rf"(?<![A-Za-z0-9_.]){re.escape(target)}(?![A-Za-z0-9_])",
                        f"{relative} builds supported root {target} outside its owner",
                    )

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

    def test_full_history_checkouts_defer_unneeded_historical_blobs(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        checkouts = re.findall(
            r"(?ms)^      - uses: actions/checkout@.*?(?=^      - |\Z)",
            workflow,
        )
        full_history = [row for row in checkouts if "fetch-depth: 0" in row]

        self.assertEqual(len(full_history), 5)
        for checkout in full_history:
            self.assertIn("filter: blob:none", checkout)

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

    def test_paper_only_skip_cannot_stand_in_for_unverified_layout_inputs(self):
        """GitHub reports a skipped required Lean job as success.

        A layout/source change that never completed Lean work, followed by a
        paper-only child, therefore looks green while the intervening inputs
        remain unverified. The required escape hatch is workflow_dispatch with
        scope=all, which forces changed=true on the dispatched ref. Cache-warm
        must not cancel an applicable in-flight producer when a later docs
        push arrives.
        """
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        detect = workflow.split("- name: Detect supported-root Lean changes", 1)[1]
        detect = detect.split("- name: Test pinned proof-environment lock", 1)[0]
        self.assertIn('EVENT_NAME" == "workflow_dispatch"', detect)
        self.assertIn('echo "changed=true" >> "$GITHUB_OUTPUT"', detect)
        self.assertIn("PR_BASE_SHA", detect)
        cache_warm = (
            fast.ROOT / ".github" / "workflows" / "lean-cache-warm.yml"
        ).read_text(encoding="utf-8")
        self.assertIn("cancel-in-progress: false", cache_warm)
        lean_diff = detect.split("git diff --quiet", 1)[1].split("then", 1)[0]
        warm_diff = cache_warm.split("git diff --quiet", 1)[1].split("then", 1)[0]
        def pathspec(block: str) -> list[str]:
            return [
                token
                for line in block.splitlines()
                for token in line.replace("\\", " ").split()
                if token.startswith(("lean/", "verification/", "research/", "docs/", "scripts/", "lakefile", "lake-manifest", "lean-toolchain"))
                or token.startswith("'lean/")
                or token.startswith("'verification/")
                or token.startswith("'research/")
            ]

        self.assertEqual(pathspec(lean_diff), pathspec(warm_diff))

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

    def test_core_gate_watches_every_declared_dependency_index_input(self) -> None:
        """An unwatched index input is an index verification that never runs.

        `lean-inputs` gates "Verify elaborated dependency index" as well as the
        build, so a file that can change the committed index but is absent from
        the pathspec makes that step skip on exactly the commit that broke it.
        `build_lean_dependency_index.CHECK_INPUT_FILES` is the builder's own
        list of what can change its output; this pins the gate to it.

        Not hypothetical. `docs/declaration_atlas.json` is where the index gets
        both its source coordinates and the `source_fingerprint` that
        `query_corpus.lean_dependency_index` requires it to share with the
        atlas, and it was missing from this pathspec. On 2026-08-30 four
        atlas-only commits (e75afbb3, 53db1318, 0d188b6d, 1169acce) moved that
        fingerprint with `changed=false`; the verification never ran, and every
        formal dependency neighbourhood, path, cone and proof plan in the
        corpus reported itself `unavailable_or_stale` from then on.
        """
        import build_lean_dependency_index as index_builder

        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        core = workflow.split("- name: Detect supported-root Lean changes", 1)[1]
        core = core.split("- name: Test pinned proof-environment lock", 1)[0]

        # Read the pathspec itself, not the surrounding prose: a path named
        # only in a comment would satisfy a whole-block substring search while
        # the gate stayed blind to it.
        self.assertIn('git diff --quiet "$base" "$head" -- ', core)
        pathspec = core.split('git diff --quiet "$base" "$head" -- ', 1)[1]
        pathspec = pathspec.split("; then", 1)[0]
        self.assertIn("lean-toolchain", pathspec, "the pathspec parse drifted")

        # Six authority inputs. The Python wrappers are deliberately absent:
        # editing orchestration must re-run the CI gate, but must not invalidate
        # a semantic projection receipt when no Lean statement or exporter
        # input moved. The workflow pathspec below therefore still names the
        # wrappers separately from this exact input list.
        self.assertGreaterEqual(len(index_builder.CHECK_INPUT_FILES), 6)
        for declared in index_builder.CHECK_INPUT_FILES:
            with self.subTest(input=declared):
                self.assertIn(
                    declared,
                    pathspec,
                    f"{declared} can change the committed dependency index but "
                    "is not in the lean-inputs pathspec, so a commit that "
                    "touches only it skips 'Verify elaborated dependency "
                    "index' and can land a stale docs/lean_dependency_index"
                    ".json",
                )

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

    def test_ci_does_not_reexport_dependency_index_after_full_check(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        # A current tracked receipt must not launch the 90-minute exporter.
        # The exporter remains the fallback when --check is stale.
        self.assertIn(
            "if python3 scripts/build_lean_dependency_index.py --check; then",
            workflow,
        )
        self.assertIn(
            "python3 scripts/build_lean_dependency_index.py --check --full-check --write-stale",
            workflow,
        )
        bare_exports = re.findall(
            r"(?m)^\s*run:\s*python3 scripts/build_lean_dependency_index\.py\s*$",
            workflow,
        )
        self.assertEqual(
            bare_exports,
            [],
            "Lean CI launched a second unbounded dependency-index export after --full-check",
        )

    def test_ci_does_not_upload_tracked_index_as_fresh_on_incomplete_export(self) -> None:
        workflow = (fast.ROOT / ".github" / "workflows" / "lean.yml").read_text(
            encoding="utf-8"
        )
        self.assertIn("fresh_export_written == 'true'", workflow)
        self.assertIn("--report-ci-outcome --fail-ci-outcome", workflow)
        self.assertIn("PLECTIS_PR_HEAD_SHA", workflow)
        self.assertNotIn(
            "the tracked dependency index is stale; download artifact",
            workflow,
        )

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
                (
                    "-- import Pkg.Commented\n"
                    "import\tPkg.Local\tPkg.Second\tMathlib\n"
                    "public import Pkg.Public\n"
                ),
                encoding="utf-8",
            )
            modules = {
                "Pkg.Local": Path(directory) / "Local.lean",
                "Pkg.Second": Path(directory) / "Second.lean",
                "Pkg.Public": Path(directory) / "Public.lean",
            }

            self.assertEqual(
                fast.local_imports(source, modules),
                {"Pkg.Local", "Pkg.Second", "Pkg.Public"},
            )

    def test_local_imports_fails_closed_on_unknown_import_header_syntax(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Main.lean"
            modules = {"Pkg.Local": Path(directory) / "Local.lean"}
            cases = {
                "punctuated": "import Pkg.Local, Pkg.Other\n",
                "bare_split": "import\n  Pkg.Local\n",
                "public_bare_split": "public import\n  Pkg.Local\n",
            }
            for name, text in cases.items():
                with self.subTest(name=name):
                    source.write_text(text, encoding="utf-8")
                    with self.assertRaisesRegex(RuntimeError, "unsupported Lean import header"):
                        fast.local_imports(source, modules)

    def test_local_imports_fails_closed_on_module_header_before_imports(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Main.lean"
            source.write_text("module Pkg.Main\nimport Pkg.Local\n", encoding="utf-8")
            modules = {"Pkg.Local": Path(directory) / "Local.lean"}
            with self.assertRaisesRegex(RuntimeError, "unsupported Lean module header"):
                fast.local_imports(source, modules)

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

    def test_failed_batch_is_not_replayed_to_isolate_diagnostics(self) -> None:
        with mock.patch.object(fast, "build_batch", return_value=(1, 0.3)) as batch, mock.patch.object(
            fast, "build_one", side_effect=AssertionError("unchanged failure must not be replayed")
        ) as single:
            self.assertEqual(
                fast.build_wave(["Pkg.Good", "Pkg.Bad"], jobs=2),
                ["Pkg.Good", "Pkg.Bad"],
            )
            batch.assert_called_once()
            single.assert_not_called()

    def test_failed_batch_does_not_skip_independent_ready_batches(self) -> None:
        with mock.patch.object(fast, "build_batch", side_effect=[(1, 0.3), (0, 0.2)]) as batch:
            self.assertEqual(
                fast.build_wave(["Pkg.A", "Pkg.B", "Pkg.C"], jobs=2),
                ["Pkg.A", "Pkg.B"],
            )
            self.assertEqual([call.args[0] for call in batch.call_args_list],
                             [["Pkg.A", "Pkg.B"], ["Pkg.C"]])

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

    def test_failure_blocks_only_its_dependents_and_preserves_independent_work(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {"A": "", "B": "import A\n", "C": "", "D": "import C\n",
                       "E": "import B\n", "Root": "import E\nimport D\n"}
            for name, text in sources.items():
                (root / (name + ".lean")).write_text(text, encoding="utf-8")
            built = []
            def wave(names, jobs, root):
                built.extend(names)
                return [name for name in names if name == "A"]
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast, "build_wave", side_effect=wave
            ), mock.patch.object(fast, "run_final_authority_check") as final:
                with self.assertRaisesRegex(RuntimeError, "module batch prebuild failed"):
                    fast.main(["Root", "--lake-staleness"])
            self.assertEqual(built, ["A", "C", "D"])
            final.assert_not_called()

    def test_partial_cache_starts_from_missing_outputs_before_final_lake(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Root.lean"
            source.parent.mkdir()
            source.write_text("-- source\n", encoding="utf-8")
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast,
                "lake_stale_targets",
                side_effect=AssertionError("missing output must not pay for rehash"),
            ) as stale_targets, mock.patch.object(
                fast, "build_wave", return_value=[]
            ), mock.patch.object(fast.subprocess, "run", return_value=completed):
                self.assertEqual(
                    fast.main(["Pkg.Root", "--lake-staleness"]),
                    0,
                )

            stale_targets.assert_not_called()

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
            [LAKE, "--rehash", "--no-build", "-v", "build", "+Pkg.Root"],
        )

    def test_config_trace_batches_rehash_once(self) -> None:
        calls: list[tuple[list[str], bool]] = []

        def trace(names, root=fast.ROOT, *, rehash=True):
            calls.append((list(names), rehash))
            return [name for name in names if name == "Pkg.C"]

        with mock.patch.object(fast, "lake_stale_targets", side_effect=trace):
            self.assertEqual(
                fast.lake_stale_targets_batched(
                    ["Pkg.A", "Pkg.B", "Pkg.C"],
                    Path("/tmp/pkg"),
                    batch_size=2,
                ),
                ["Pkg.C"],
            )

        self.assertEqual(
            calls,
            [(["Pkg.A", "Pkg.B"], True), (["Pkg.C"], False)],
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

    def test_lake_command_uses_canonical_path_under_hostile_path(self) -> None:
        completed = fast.subprocess.CompletedProcess([], 0, "", "")
        with mock.patch.dict(
            os.environ, {"PATH": "/private/wrong-bin"}, clear=False
        ), mock.patch.object(
            fast.subprocess, "run", return_value=completed
        ) as run:
            self.assertTrue(fast.lake_targets_up_to_date(["Pkg.Leaf"]))

        command = run.call_args.args[0]
        self.assertEqual(command[0], LAKE)
        self.assertNotEqual(command[0], "lake")
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

    def test_config_timestamp_only_uses_trace_and_preserves_final_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Root.lean"
            output = root / ".lake" / "build" / "lib" / "lean" / "Pkg" / "Root.olean"
            source.parent.mkdir()
            output.parent.mkdir(parents=True)
            source.write_text("-- source\n", encoding="utf-8")
            output.write_text("olean\n", encoding="utf-8")
            os.utime(source, ns=(1_000_000_000, 1_000_000_000))
            os.utime(output, ns=(2_000_000_000, 2_000_000_000))
            (root / "lean-toolchain").write_text(
                "leanprover/lean4:test\n", encoding="utf-8"
            )
            os.utime(
                root / "lean-toolchain",
                ns=(3_000_000_000, 3_000_000_000),
            )
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast, "lake_stale_targets_batched", return_value=[]
            ) as traced, mock.patch.object(
                fast, "build_wave", side_effect=AssertionError(
                    "content-current config timestamp must not rebuild"
                )
            ), mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(fast.main(["Pkg.Root"]), 0)

            traced.assert_called_once_with(["Pkg.Root"], root)
            self.assertEqual(
                run.call_args.args[0],
                [
                    LAKE,
                    "--quiet",
                    "--no-ansi",
                    "--log-level=error",
                    "build",
                    "+Pkg.Root",
                ],
            )

    def test_config_content_trace_stale_module_is_prebuilt_before_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Pkg" / "Root.lean"
            output = root / ".lake" / "build" / "lib" / "lean" / "Pkg" / "Root.olean"
            source.parent.mkdir()
            output.parent.mkdir(parents=True)
            source.write_text("-- source\n", encoding="utf-8")
            output.write_text("olean\n", encoding="utf-8")
            os.utime(source, ns=(1_000_000_000, 1_000_000_000))
            os.utime(output, ns=(2_000_000_000, 2_000_000_000))
            (root / "lakefile.toml").write_text("[[lean_lib]]\nname = \"Pkg\"\n")
            os.utime(root / "lakefile.toml", ns=(3_000_000_000, 3_000_000_000))
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast, "lake_stale_targets_batched", return_value=["Pkg.Root"]
            ), mock.patch.object(
                fast, "build_wave", return_value=[]
            ) as build, mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(fast.main(["Pkg.Root"]), 0)

            build.assert_called_once_with(["Pkg.Root"], fast.default_jobs(), root)
            self.assertEqual(run.call_count, 1)

    def test_source_and_missing_outputs_still_prebuild_before_authority(self) -> None:
        for changed in ("source", "missing"):
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                source = root / "Pkg" / "Root.lean"
                output = (
                    root / ".lake" / "build" / "lib" / "lean" / "Pkg" / "Root.olean"
                )
                source.parent.mkdir()
                output.parent.mkdir(parents=True)
                source.write_text("-- source\n", encoding="utf-8")
                output.write_text("olean\n", encoding="utf-8")
                os.utime(source, ns=(1_000_000_000, 1_000_000_000))
                os.utime(output, ns=(2_000_000_000, 2_000_000_000))
                if changed == "source":
                    os.utime(source, ns=(3_000_000_000, 3_000_000_000))
                else:
                    output.unlink()
                completed = fast.subprocess.CompletedProcess([], 0, "", "")
                with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                    fast, "lake_stale_targets_batched"
                ) as traced, mock.patch.object(
                    fast, "build_wave", return_value=[]
                ) as build, mock.patch.object(
                    fast.subprocess, "run", return_value=completed
                ) as run:
                    self.assertEqual(fast.main(["Pkg.Root"]), 0)

                traced.assert_not_called()
                build.assert_called_once_with(["Pkg.Root"], fast.default_jobs(), root)
                self.assertEqual(run.call_count, 1)

    def test_source_change_prebuilds_import_dependents_before_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base = root / "Pkg" / "Base.lean"
            consumer = root / "Pkg" / "Consumer.lean"
            base.parent.mkdir()
            base.write_text("-- base\n", encoding="utf-8")
            consumer.write_text("import Pkg.Base\n", encoding="utf-8")
            for name, source in (("Base", base), ("Consumer", consumer)):
                output = (
                    root
                    / ".lake"
                    / "build"
                    / "lib"
                    / "lean"
                    / "Pkg"
                    / f"{name}.olean"
                )
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_text("olean\n", encoding="utf-8")
                os.utime(source, ns=(1_000_000_000, 1_000_000_000))
                os.utime(output, ns=(2_000_000_000, 2_000_000_000))
            os.utime(base, ns=(3_000_000_000, 3_000_000_000))
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            built: list[list[str]] = []
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast,
                "build_wave",
                side_effect=lambda names, jobs, root: built.append(list(names)) or [],
            ), mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(fast.main(["Pkg.Consumer"]), 0)

            self.assertEqual(built, [["Pkg.Base"], ["Pkg.Consumer"]])
            self.assertEqual(run.call_count, 1)

    def test_cached_import_depth_does_not_serialize_independent_rebuilds(self) -> None:
        # A and B are independent stale modules; B happens to import a deeper
        # current chain. C really depends on B and must remain a later batch.
        for lake_staleness in (False, True):
            with self.subTest(lake_staleness=lake_staleness), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                sources = {
                    "A": "-- independent stale root\n",
                    "Cached0": "-- current dependency\n",
                    "Cached1": "import Pkg.Cached0\n",
                    "B": "import Pkg.Cached1\n",
                    "C": "import Pkg.B\n",
                }
                for name, content in sources.items():
                    source = root / "Pkg" / f"{name}.lean"
                    source.parent.mkdir(exist_ok=True)
                    source.write_text(content, encoding="utf-8")
                    output = fast.olean(f"Pkg.{name}", root)
                    output.parent.mkdir(parents=True, exist_ok=True)
                    output.write_text("cached\n", encoding="utf-8")
                    os.utime(source, ns=(1_000_000_000, 1_000_000_000))
                    os.utime(output, ns=(2_000_000_000, 2_000_000_000))
                for name in ("A", "B"):
                    os.utime(root / "Pkg" / f"{name}.lean", ns=(3_000_000_000, 3_000_000_000))
                built: list[list[str]] = []
                with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                    fast, "lake_stale_targets", return_value=["Pkg.A", "Pkg.B"]
                ), mock.patch.object(
                    fast, "build_wave",
                    side_effect=lambda names, jobs, root: built.append(list(names)) or [],
                ), mock.patch.object(fast, "run_final_authority_check", return_value=0) as authority:
                    args = ["--jobs", "2", "Pkg.A", "Pkg.C"]
                    if lake_staleness:
                        args.insert(0, "--lake-staleness")
                    self.assertEqual(fast.main(args), 0)
                self.assertEqual(built, [["Pkg.A", "Pkg.B"], ["Pkg.C"]])
                authority.assert_called_once_with(["Pkg.A", "Pkg.C"], root)

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
            [LAKE, "--rehash", "--no-build", "build", "+Pkg.Leaf"],
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
                    LAKE,
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
                        LAKE, "--quiet", "--no-ansi", "--log-level=error",
                        "build", "+Erdos249257",
                    ],
                    [
                        LAKE, "--quiet", "--no-ansi", "--log-level=error",
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
                    LAKE, "--quiet", "--no-ansi", "--log-level=error",
                    "build", "+Pkg.Leaf",
                ],
            )
            self.assertEqual(run.call_args.kwargs["cwd"], root)

    def test_registered_and_unregistered_sources_use_their_real_authority_commands(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            registered = root / "Pkg" / "Leaf.lean"
            unregistered = root / "examples" / "Examples.lean"
            registered.parent.mkdir(parents=True)
            unregistered.parent.mkdir(parents=True)
            registered.write_text("-- registered\n", encoding="utf-8")
            unregistered.write_text("-- unregistered\n", encoding="utf-8")
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "Pkg"\n', encoding="utf-8"
            )
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast, "lake_stale_targets", return_value=[]
            ) as stale_targets, mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(
                    fast.main(
                        [
                            "Pkg/Leaf.lean",
                            "examples/Examples.lean",
                            "--lake-staleness",
                        ]
                    ),
                    0,
                )

            stale_targets.assert_not_called()
            self.assertEqual(
                [call.args[0] for call in run.call_args_list],
                [
                    fast.lake_command(
                        "--quiet",
                        "--no-ansi",
                        "--log-level=error",
                        "build",
                        "+Pkg.Leaf",
                    ),
                    # The missing registered output is prebuilt under the
                    # bounded scheduler, then checked again at the serialized
                    # Lake authority boundary before the direct source runs.
                    fast.lake_command(
                        "--quiet",
                        "--no-ansi",
                        "--log-level=error",
                        "build",
                        "+Pkg.Leaf",
                    ),
                    fast.lake_command("env", "lean", "examples/Examples.lean"),
                ],
            )
            for call in run.call_args_list:
                self.assertEqual(
                    call.kwargs["env"], singleflight.command_environment()
                )
                self.assertEqual(
                    call.kwargs["timeout"], fast.LAKE_COMMAND_TIMEOUT_SECONDS
                )

    def test_clean_cache_direct_source_rebuilds_registered_import_at_final_boundary(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            dependency = root / "Pkg" / "Dependency.lean"
            consumer = root / "examples" / "Consumer.lean"
            dependency.parent.mkdir(parents=True)
            consumer.parent.mkdir(parents=True)
            dependency.write_text("-- dependency\n", encoding="utf-8")
            consumer.write_text("import Pkg.Dependency\n", encoding="utf-8")
            (root / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "Pkg"\n', encoding="utf-8"
            )
            completed = fast.subprocess.CompletedProcess([], 0, "", "")
            with mock.patch.object(fast, "ROOT", root), mock.patch.object(
                fast.subprocess, "run", return_value=completed
            ) as run:
                self.assertEqual(
                    fast.main(["examples/Consumer.lean", "--jobs", "2"]),
                    0,
                )

            commands = [call.args[0] for call in run.call_args_list]
            self.assertEqual(
                commands,
                [
                    fast.lake_command(
                        "--quiet",
                        "--no-ansi",
                        "--log-level=error",
                        "build",
                        "+Pkg.Dependency",
                    ),
                    fast.lake_command(
                        "--quiet",
                        "--no-ansi",
                        "--log-level=error",
                        "build",
                        "+Pkg.Dependency",
                    ),
                    fast.lake_command("env", "lean", "examples/Consumer.lean"),
                ],
            )
            for call in run.call_args_list:
                self.assertEqual(
                    call.kwargs["env"], singleflight.command_environment()
                )
                self.assertEqual(
                    call.kwargs["timeout"], fast.LAKE_COMMAND_TIMEOUT_SECONDS
                )

    def test_portfolio_direct_sources_finalize_source_current_shared_imports(
        self,
    ) -> None:
        modules = fast.discover()
        targets = fast.resolve_targets(
            [
                "research/examples/ExternalVerificationPortfolio/Problem249.lean",
                "research/examples/ExternalVerificationPortfolio/Problem251.lean",
                "research/examples/ExternalVerificationPortfolio/Problem269.lean",
            ],
            modules,
        )
        graph = fast.reachable_graph(targets, modules)
        direct = fast.direct_source_targets(targets, modules)

        self.assertEqual(set(direct), set(targets))
        self.assertEqual(
            fast.direct_source_lake_imports(direct, graph),
            ["Erdos249257", "ExternalVerification.Solution"],
        )
        self.assertIn(
            "ErdosProblems.Erdos249.TotientStrictPrimeEscape",
            fast.reachable(["ExternalVerification.Solution"], graph),
        )

    def test_final_authority_checks_focused_modules_serially(self) -> None:
        completed = fast.subprocess.CompletedProcess([], 0, "", "")
        with mock.patch.object(fast.subprocess, "run", return_value=completed) as run:
            self.assertEqual(fast.run_final_authority_check(["Pkg.A", "Pkg.B"]), 0)

        self.assertEqual(
            [call.args[0] for call in run.call_args_list],
            [
                [
                    LAKE, "--quiet", "--no-ansi", "--log-level=error",
                    "build", "+Pkg.A",
                ],
                [
                    LAKE, "--quiet", "--no-ansi", "--log-level=error",
                    "build", "+Pkg.B",
                ],
            ],
        )


if __name__ == "__main__":
    unittest.main()
