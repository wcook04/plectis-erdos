#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for release-gate subprocess environment isolation."""

from __future__ import annotations

import inspect
import ast
import json
import os
import subprocess
import sys
import tempfile
import threading
from pathlib import Path
from unittest.mock import patch

import check_release


def require(condition: bool, message: str) -> None:
    """Keep environment-isolation failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def check_markdown_render_gate() -> None:
    """Run the CI render command through the release collector on small inputs."""
    command = check_release.late_check_commands().get("markdown_table_render")
    require(
        command == [
            sys.executable,
            str(check_release.ROOT / "scripts" / "check_markdown_table_render.py"),
            "--fail-on", "overflow", ".",
        ],
        "release gate must schedule CI's fatal Markdown overflow check",
    )
    with tempfile.TemporaryDirectory(prefix="release-markdown-gate-") as temporary:
        fixture_root = Path(temporary)
        fixture = fixture_root / "render.md"
        for token, expected_code in (("fits", 0), ("x" * 150, 1)):
            fixture.write_text(f"| Result |\n| --- |\n| `{token}` |\n", encoding="utf-8")
            with (
                patch.object(check_release, "ROOT", fixture_root),
                patch.object(check_release, "ERRORS", []),
                patch.object(check_release, "CHECKS", 0),
            ):
                executor, futures = check_release.start_independent_checks(
                    {"markdown_table_render": command}, max_workers=2
                )
                results = check_release.finish_independent_checks(executor, futures)
                result = results["markdown_table_render"]
                require(result.returncode == expected_code, result.stdout + result.stderr)
                if expected_code:
                    require(len(check_release.ERRORS) == 1, "Markdown overflow escaped the release gate")
                    require(
                        all(text in check_release.ERRORS[0] for text in (
                            "markdown_table_render", "exit 1", "render.md", "[overflow]",
                        )),
                        "release failure lost the Markdown overflow diagnosis",
                    )
                else:
                    require(not check_release.ERRORS, "readable Markdown failed the release gate")


def main() -> int:
    check_markdown_render_gate()
    source = inspect.getsource(check_release)
    require(
        "primary_source_disposition_check = subprocess.run(" not in source,
        "primary-source disposition gate invokes raw subprocess.run",
    )
    require(
        "proof_cockpit_check = subprocess.run(" not in source,
        "proof-cockpit gate invokes raw subprocess.run",
    )
    require(
        "_read_safe_bytes" in inspect.getsource(check_release.read)
        and "_read_safe_bytes" in inspect.getsource(check_release.file_digest)
        and "safe_release_path" in inspect.getsource(check_release._read_safe_bytes),
        "release artifact readers bypass the in-checkout path guard",
    )
    check_release.read.cache_clear()
    cached_path = check_release.ROOT / "README.md"
    with patch.object(
        check_release,
        "_read_safe_bytes",
        wraps=check_release._read_safe_bytes,
    ) as admitted_read:
        first = check_release.read(cached_path)
        second = check_release.read(cached_path)
    require(first == second, "release snapshot cache changed decoded content")
    require(
        admitted_read.call_count == 1,
        "release snapshot cache repeated path admission for one input",
    )
    check_release.read.cache_clear()
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_WORK_TREE": "/private/wrong-work-tree",
        "GIT_INDEX_FILE": "/private/wrong-index",
        "GIT_NAMESPACE": "wrong-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
        "GIT_OBJECT_DIRECTORY": "/private/wrong-objects",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES": "/private/wrong-alternates",
        "GIT_COMMON_DIR": "/private/wrong-common",
        "PYTHONHOME": "/private/wrong-python-home",
        "PYTHONPATH": "/private/wrong-python-path",
        "PYTHONOPTIMIZE": "2",
        "LC_ALL": "C",
        "LANG": "C",
        "LANGUAGE": "C",
        "PATH": "/private/wrong-bin",
    }
    with tempfile.TemporaryDirectory() as raw:
        with patch.dict(os.environ, hostile_environment, clear=False):
            sanitized = check_release.clean_environment()
            for key in (
                "GIT_DIR",
                "GIT_WORK_TREE",
                "GIT_INDEX_FILE",
                "GIT_NAMESPACE",
                "GIT_REPLACE_REF_BASE",
                "GIT_OBJECT_DIRECTORY",
                "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                "GIT_COMMON_DIR",
                "PYTHONHOME",
                "PYTHONPATH",
                "PYTHONOPTIMIZE",
            ):
                require(key not in sanitized, f"release environment retained {key}")
            require(sanitized["PATH"] == os.defpath, "release environment did not pin PATH")
            require(sanitized["LC_ALL"] == "C.UTF-8", "release environment did not pin LC_ALL")
            require(sanitized["LANG"] == "C.UTF-8", "release environment did not pin LANG")
            require(sanitized["LANGUAGE"] == "C.UTF-8", "release environment did not pin LANGUAGE")
            require(sanitized["GIT_CONFIG_NOSYSTEM"] == "1", "system Git configuration was not disabled")
            require(sanitized["GIT_ASKPASS"] == "/bin/false", "Git credential prompting was not disabled")
            child = check_release.run(
                [
                    sys.executable,
                    "-c",
                    "import json, os; print(json.dumps({k: os.environ[k] for k in "
                    "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE', "
                    "'PYTHONPATH', 'PYTHONHOME', 'PYTHONOPTIMIZE', 'LC_ALL', "
                    "'LANG', 'LANGUAGE', 'PATH') "
                    "if k in os.environ}))",
                ],
                cwd=Path(raw),
                capture_output=True,
                text=True,
                check=False,
            )
            require(child.returncode == 0, "sanitized release child process failed")
            require(
                json.loads(child.stdout)
                == {
                    "LC_ALL": "C.UTF-8",
                    "LANG": "C.UTF-8",
                    "LANGUAGE": "C.UTF-8",
                    "PATH": os.defpath,
                },
                "sanitized release child inherited ambient execution state",
            )

        private = Path(raw) / "private"
        private.mkdir()
        (private / "secret.txt").write_text("outside release\n", encoding="utf-8")
        docs = Path(raw) / "docs"
        docs.mkdir()
        (docs / "linked").symlink_to(private, target_is_directory=True)
        fifo = Path(raw) / "release.fifo"
        os.mkfifo(fifo)
        original_root = check_release.ROOT
        check_release.ROOT = Path(raw)
        try:
            try:
                check_release.safe_release_path(docs / "linked" / "secret.txt")
            except check_release.UnsafeReleasePath:
                pass
            else:
                require(
                    False,
                    "release gate followed a symlinked parent directory",
                )
            require(
                not check_release.release_file_exists(
                    docs / "linked" / "secret.txt"
                ),
                "metadata-only release file checks followed a symlink",
            )
            require(
                check_release.release_file_exists(private / "secret.txt"),
                "metadata-only release file check rejected a regular file",
            )
            with patch.object(check_release, "safe_release_path", return_value=fifo):
                try:
                    check_release.read_bytes(fifo)
                except check_release.UnsafeReleasePath as error:
                    require(
                        "regular file" in str(error),
                        f"special release reader returned an unexpected error: {error}",
                    )
                else:
                    require(False, "special release reader was accepted")

            raced_parent = Path(raw) / "input-parent"
            raced_parent.mkdir()
            original_parent = Path(raw) / "input-parent-original"
            outside = Path(raw) / "outside"
            outside.mkdir()
            raced_input = raced_parent / "descriptor.json"
            raced_input.write_text("inside\n", encoding="utf-8")
            (outside / raced_input.name).write_text("outside\n", encoding="utf-8")
            original_open = check_release.os.open

            def swap_parent(
                path: Path,
                flags: int,
                mode: int = 0o777,
                *,
                dir_fd: int | None = None,
            ) -> int:
                if dir_fd is not None and Path(path).name == raced_input.name:
                    raced_parent.rename(original_parent)
                    raced_parent.symlink_to(outside, target_is_directory=True)
                if dir_fd is not None:
                    return original_open(path, flags, mode, dir_fd=dir_fd)
                return original_open(path, flags, mode)

            with patch.object(check_release.os, "open", side_effect=swap_parent):
                observed = check_release.read_bytes(raced_input)
            require(
                observed == b"inside\n",
                "release reader followed a swapped parent directory",
            )
            require(
                (original_parent / raced_input.name).is_file(),
                "release reader did not use the held parent descriptor",
            )
        finally:
            check_release.ROOT = original_root

        with patch.object(
            check_release,
            "_SUBPROCESS_RUN",
            return_value=subprocess.CompletedProcess(
                ["fixture"], returncode=0, stdout="", stderr=""
            ),
        ) as runner:
            check_release.run(
                ["fixture"],
                cwd=Path(raw),
                capture_output=True,
                text=True,
                check=False,
            )
        require(runner.call_args is not None, "release wrapper did not invoke its subprocess")
        require(
            runner.call_args.kwargs["timeout"] == check_release.SUBPROCESS_TIMEOUT_SECONDS,
            "release wrapper omitted its default subprocess timeout",
        )

    dispatched: list[tuple[str, ...]] = []

    def record_projection(
        args: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        dispatched.append(tuple(args))
        return subprocess.CompletedProcess(args, returncode=0, stdout="current", stderr="")

    check_release._PROJECTION_CHECK_RESULTS = None
    first_builder = check_release.refresh_projections.BUILDERS[0]
    last_builder = check_release.refresh_projections.BUILDERS[-1]
    try:
        with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=record_projection):
            first = check_release.run(
                [sys.executable, str(check_release.ROOT / first_builder), "--check"],
                cwd=check_release.ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            last = check_release.run(
                [sys.executable, str(check_release.ROOT / last_builder), "--check"],
                cwd=check_release.ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
        require(first.returncode == 0 and last.returncode == 0, "projection batch failed")
        require(
            sorted(Path(args[1]).relative_to(check_release.ROOT).as_posix() for args in dispatched)
            == sorted(check_release.refresh_projections.BUILDERS),
            "release projection batch did not dispatch each authoritative builder once",
        )
        require(
            len(dispatched) == len(check_release.refresh_projections.BUILDERS),
            "release projection result cache repeated a builder",
        )
    finally:
        check_release._PROJECTION_CHECK_RESULTS = None

    independent_dispatches: list[tuple[str, ...]] = []

    def record_independent(
        args: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        independent_dispatches.append(tuple(args))
        return subprocess.CompletedProcess(args, returncode=0, stdout="ok", stderr="")

    independent_commands = {
        "one": [sys.executable, "one.py"],
        "two": [sys.executable, "two.py"],
    }
    with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=record_independent):
        independent_results = check_release.run_independent_checks(independent_commands)
    require(
        set(independent_results) == set(independent_commands),
        "independent release batch lost a named result",
    )
    require(
        sorted(independent_dispatches)
        == sorted(tuple(argv) for argv in independent_commands.values()),
        "independent release batch dropped or repeated a command",
    )

    combined_dispatches: list[tuple[str, ...]] = []

    def record_combined(
        args: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        combined_dispatches.append(tuple(args))
        return subprocess.CompletedProcess(args, returncode=0, stdout="ok", stderr="")

    check_release._PROJECTION_CHECK_RESULTS = None
    with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=record_combined):
        publication_results = check_release.publication_stage_check_results()
    require(
        len(combined_dispatches) == len(check_release.refresh_projections.BUILDERS) + 5,
        "publication-stage pool dropped or repeated a check",
    )
    require(
        len(check_release._PROJECTION_CHECK_RESULTS or {})
        == len(check_release.refresh_projections.BUILDERS),
        "publication-stage pool did not populate the projection result cache",
    )
    require(
        {
            "external_verification_release",
            "note_source",
            "paper_corpus",
            "publication_taxonomy",
            "publication_archive_versions",
        }
        <= publication_results.keys(),
        "publication-stage pool lost a named diagnostic result",
    )
    check_release._PROJECTION_CHECK_RESULTS = None

    release_deferred = threading.Event()
    both_started = threading.Event()
    dispatch_count = 0
    dispatch_lock = threading.Lock()

    def hold_independent(
        args: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        nonlocal dispatch_count
        with dispatch_lock:
            dispatch_count += 1
            if dispatch_count == len(independent_commands):
                both_started.set()
        release_deferred.wait(timeout=2)
        return subprocess.CompletedProcess(args, returncode=0, stdout="ok", stderr="")

    with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=hold_independent):
        executor, futures = check_release.start_independent_checks(independent_commands)
        require(both_started.wait(timeout=2), "deferred checks did not start concurrently")
        require(
            not any(future.done() for future in futures.values()),
            "deferred check launch waited for a result",
        )
        release_deferred.set()
        deferred_results = check_release.finish_independent_checks(executor, futures)
    require(
        set(deferred_results) == set(independent_commands),
        "deferred release batch lost a named result",
    )

    # Exercise the actual scheduled key universe without running the expensive
    # validators. A future unknown key must also fail the gate automatically.
    main_tree = ast.parse(inspect.getsource(check_release.main))
    mid_batch = next(
        node.value.args[0]
        for node in ast.walk(main_tree)
        if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Name) and target.id == "mid_checks" for target in node.targets)
    )
    mid_commands = eval(
        compile(ast.Expression(mid_batch), "release-mid-command-fixture", "eval"),
        vars(check_release),
    )
    scheduled_keys = set(publication_results) | set(mid_commands) | set(check_release.late_check_commands())
    scheduled_keys.add("future_check_without_a_named_main_lookup")
    saved_errors, saved_checks = check_release.ERRORS, check_release.CHECKS
    try:
        for failed_key in sorted(scheduled_keys):
            check_release.ERRORS = []
            commands = {key: [sys.executable, key] for key in scheduled_keys}

            def injected_result(argv: list[str]) -> subprocess.CompletedProcess[str]:
                return subprocess.CompletedProcess(
                    argv, 17 if argv[-1] == failed_key else 0,
                    "injected stdout", "injected stderr",
                )

            with patch.object(check_release, "_run_independent_check", side_effect=injected_result):
                results = check_release.run_independent_checks(commands)
            require(set(results) == scheduled_keys, "collector lost a scheduled result")
            require(len(check_release.ERRORS) == 1, f"scheduled failure {failed_key} escaped the gate")
            failure = check_release.ERRORS[0]
            require(
                all(value in failure for value in (failed_key, "exit 17", "injected stdout", "injected stderr")),
                f"collector lost failure diagnostics for {failed_key}",
            )

        check_release.ERRORS = []
        check_release._PROJECTION_CHECK_RESULTS = None
        failed_builder = check_release.refresh_projections.BUILDERS[-1]

        def failed_projection(argv: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
            code = 17 if argv[1] == str(check_release.ROOT / failed_builder) else 0
            return subprocess.CompletedProcess(argv, code, "projection failure", "")

        with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=failed_projection) as runner:
            check_release.projection_check_results()
            check_release.projection_check_results()
        require(runner.call_count == len(check_release.refresh_projections.BUILDERS), "cached projections reran")
        require(
            len(check_release.ERRORS) == 1 and failed_builder in check_release.ERRORS[0],
            "standalone projection collector ignored a scheduled failure",
        )
        require("agent_skill_catalog" not in mid_commands, "skill catalog was scheduled in two pools")
    finally:
        check_release.ERRORS, check_release.CHECKS = saved_errors, saved_checks
        check_release._PROJECTION_CHECK_RESULTS = None

    require(
        check_release.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "release environment contract identifier drifted",
    )
    require(
        "GIT_NAMESPACE" in check_release.SANITIZED_GIT_ENVIRONMENT_KEYS,
        "release environment omitted GIT_NAMESPACE sanitization",
    )
    require(
        "GIT_REPLACE_REF_BASE" in check_release.SANITIZED_GIT_ENVIRONMENT_KEYS,
        "release environment omitted GIT_REPLACE_REF_BASE sanitization",
    )
    require(
        check_release.SUBPROCESS_TIMEOUT_SECONDS
        == check_release.singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
        "release subprocess timeout drifted from the shared worker boundary",
    )
    require(
        check_release.PROJECTION_CHECK_WORKERS
        == check_release.refresh_projections.CHECK_WORKERS,
        "release projection batch drifted from the aggregate freshness worker bound",
    )
    require(
        1 <= check_release.RELEASE_CHECK_WORKERS <= 4,
        "release suite batch exceeds its bounded worker policy",
    )
    require(
        tuple(check_release.late_check_commands())[:2]
        == ("query", "cold_clone_adversarial"),
        "release late pool no longer starts both long readers first",
    )
    require(
        check_release.late_check_commands().get("release_environment")
        == [sys.executable, str(Path(__file__).resolve())],
        "release gate no longer schedules its environment and result-consumption regressions",
    )
    main_source = inspect.getsource(check_release.main)
    require(
        main_source.index("formal_source_identity_errors(")
        < main_source.index("publication_stage_results =")
        < main_source.index("start_independent_checks("),
        "release identity no longer fails before expensive projection and late pools",
    )
    require("formal_source_matches_current_lean_tree(" in inspect.getsource(check_release.formal_source_identity_errors),
            "shared source-identity helper omitted the actual Lean-tree comparison")
    check_preflight_projection_reuse()
    check_dependency_preflight()
    check_empty_selection_is_not_a_pass()
    print(
        "test_check_release_environment: release-gate child processes cannot "
        "inherit caller Git, Python, locale, or PATH state"
    )
    return 0


def check_preflight_projection_reuse() -> None:
    """Reuse exact base results once while retaining variants and all failures."""
    saved_errors, saved_checks = check_release.ERRORS, check_release.CHECKS
    saved_results = check_release._PROJECTION_CHECK_RESULTS
    saved_context = check_release._PREFLIGHT_PROJECTION_CONTEXT
    calls = []
    environment = {"PATH": "fixture-bin", "LANG": "C.UTF-8"}
    context = {
        "cwd": str(check_release.ROOT), "producer_cwd": str(check_release.ROOT),
        "environment": environment, "producer_environment": environment,
        "timeout": 900, "producer_timeout": 900,
        "commands": {b: tuple(check_release.refresh_projections.check_command(b))
                     for b in check_release.refresh_projections.BUILDERS},
        "source": {"tree": "fixture-immutable-tree", "dirty": False},
    }
    def fake_run(argv, **kwargs):
        calls.append(tuple(argv))
        return subprocess.CompletedProcess(argv, 0, "records" if "--records" in argv else "base", "")
    try:
        check_release.ERRORS, check_release.CHECKS = [], 0
        base_results = {}
        with patch.object(check_release.refresh_projections, "run", side_effect=fake_run), \
             patch.object(check_release, "preflight_projection_context", return_value=context):
            require(check_release.refresh_projections.preflight(base_results=base_results) == 0,
                    "mock preflight failed")
            require(set(base_results) == set(check_release.refresh_projections.BUILDERS),
                    "preflight did not capture every current base builder")
            for builder, result in base_results.items():
                require(calls.count(tuple(result.args)) == 1, f"base builder repeated: {builder}")
            require(any("--records" in argv for argv in calls), "preflight dropped records")
            require(check_release.seed_preflight_projection_results(base_results, context),
                    "exact successful preflight results were refused")
            calls.clear()
            before_checks = check_release.CHECKS
            with patch.object(check_release, "_SUBPROCESS_RUN", side_effect=fake_run):
                results = check_release.publication_stage_check_results()
            require(len(calls) == 5, "publication repeated projections or lost a diagnostic")
            require(len(results) == len(base_results) + 5, "combined result coverage changed")
            require(check_release.CHECKS == before_checks + 1,
                    "merged publication results changed the aggregate check-count contribution")
            for builder, result in base_results.items():
                require(results[f"projection:{builder}"] is result,
                        "publication replaced the actual base result")

            for invalid in (
                {k: v for k, v in base_results.items() if k != next(iter(base_results))},
                {**base_results, "scripts/unknown_builder.py": subprocess.CompletedProcess([], 0)},
                {**base_results, next(iter(base_results)): subprocess.CompletedProcess(
                    list(context["commands"][next(iter(base_results))]), 17, "out", "err")},
                {**base_results, "scripts/build_reading_edition.py": subprocess.CompletedProcess(
                    [sys.executable, str(check_release.ROOT / "scripts/build_reading_edition.py"), "--records", "--check"], 0)},
            ):
                check_release._PROJECTION_CHECK_RESULTS = None
                check_release._PREFLIGHT_PROJECTION_CONTEXT = None
                require(not check_release.seed_preflight_projection_results(invalid, context),
                        "incomplete/unknown/failed/wrong-family preflight was admitted")
                require(check_release._PROJECTION_CHECK_RESULTS is None, "invalid preflight populated cache")

            for field, replacement in (
                ("cwd", "another-root"), ("environment", {"PATH": "other-bin"}),
                ("source", {"tree": "changed-tree", "dirty": False}),
                ("timeout", 901), ("commands", {**context["commands"], "new-builder": ("fixture",)}),
            ):
                changed = {**context, field: replacement}
                with patch.object(check_release, "preflight_projection_context", return_value=changed):
                    require(not check_release.seed_preflight_projection_results(base_results, context),
                            f"changed {field} was reused")

            require(check_release.seed_preflight_projection_results(base_results, context), "reseed failed")
            new_builder = "scripts/new_projection_fixture.py"
            new_context = {**context, "commands": {
                **context["commands"], new_builder: (sys.executable, str(check_release.ROOT / new_builder), "--check")}}
            with patch.object(check_release.refresh_projections, "BUILDERS",
                              (*check_release.refresh_projections.BUILDERS, new_builder)), \
                 patch.object(check_release, "preflight_projection_context", return_value=new_context):
                require(not check_release.seed_preflight_projection_results(base_results, new_context),
                        "new registered builder escaped preflight coverage")
            require(check_release._PROJECTION_CHECK_RESULTS is None,
                    "failed new-builder admission retained previous results")
            require(check_release.seed_preflight_projection_results(base_results, context), "reseed failed")
            with patch.object(check_release, "preflight_projection_context",
                              return_value={**context, "source": {"tree": "later-source"}}):
                try:
                    check_release.publication_stage_check_results()
                except RuntimeError:
                    pass
                else:
                    raise AssertionError("publication reused a changed source snapshot")

        # A failed mandatory preflight must stop before seeding/release work,
        # and each main invocation must begin with a distinct empty result set.
        sinks = []
        def failed_preflight(*, base_results):
            require(not base_results, "new main invocation retained prior preflight results")
            sinks.append(base_results)
            return 1
        for _ in range(2):
            check_release._PROJECTION_CHECK_RESULTS = base_results
            check_release._PREFLIGHT_PROJECTION_CONTEXT = context
            with patch.object(check_release, "missing_release_dependencies", return_value=[]), \
                 patch.object(check_release, "preflight_projection_context", return_value=context), \
                 patch.object(check_release.refresh_projections, "preflight", side_effect=failed_preflight), \
                 patch.object(check_release, "seed_preflight_projection_results",
                              side_effect=AssertionError("failed preflight seeded cache")), \
                 patch.object(check_release, "check_proof_trust",
                              side_effect=AssertionError("failed preflight continued")):
                require(check_release.main(["--singleflight-worker"]) == 1, "failed preflight released")
            require(check_release._PROJECTION_CHECK_RESULTS is None
                    and check_release._PREFLIGHT_PROJECTION_CONTEXT is None,
                    "main retained a cross-run projection cache")
        require(sinks[0] is not sinks[1], "main invocations shared a preflight sink")
    finally:
        check_release.ERRORS, check_release.CHECKS = saved_errors, saved_checks
        check_release._PROJECTION_CHECK_RESULTS = saved_results
        check_release._PREFLIGHT_PROJECTION_CONTEXT = saved_context


def check_dependency_preflight() -> None:
    """A direct call without the pinned dependencies stops before any check."""
    saved_errors, saved_checks = check_release.ERRORS, check_release.CHECKS
    check_release.ERRORS, check_release.CHECKS = [], 0
    try:
        with patch("importlib.util.find_spec", return_value=None), patch.object(
            check_release.singleflight, "submit"
        ) as submit, patch("sys.stderr") as stderr:
            code = check_release.main([])
        written = "".join(call.args[0] for call in stderr.write.call_args_list)
        require(code == 2, "missing release dependency did not stop the gate")
        require(not submit.called, "gate queued validation without its dependencies")
        require(check_release.CHECKS == 0, "gate ran checks without its dependencies")
        require(
            "scripts/run_release_check.py" in written,
            "dependency stop does not name the supported release entry",
        )
    finally:
        check_release.ERRORS, check_release.CHECKS = saved_errors, saved_checks


def check_empty_selection_is_not_a_pass() -> None:
    """A test selector that matches nothing must not report success."""
    completed = subprocess.run(
        [
            sys.executable,
            str(check_release.ROOT / "scripts" / "test_validation_singleflight.py"),
            "-k",
            "selector_that_matches_no_test",
        ],
        cwd=check_release.ROOT,
        capture_output=True,
        text=True,
        check=False,
        timeout=120,
    )
    verdict = json.loads(completed.stdout.strip().splitlines()[-1])
    require(completed.returncode == 5, "empty test selection exited as a pass")
    require(
        verdict["status"] == "no_tests_ran" and verdict["successful"] is False,
        "empty test selection reported success",
    )


if __name__ == "__main__":
    raise SystemExit(main())
