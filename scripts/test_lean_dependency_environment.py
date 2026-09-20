#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regression contract for dependency-bootstrap subprocess environment isolation."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import build_lean_dependency_index
import validation_singleflight


def require(condition: bool, message: str) -> None:
    """Keep dependency-environment failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def main() -> int:
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_WORK_TREE": "/private/wrong-work-tree",
        "GIT_INDEX_FILE": "/private/wrong-index",
        "GIT_NAMESPACE": "wrong-namespace",
        "GIT_REPLACE_REF_BASE": "refs/replacements/wrong",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "en_US.UTF-8",
        "LANGUAGE": "fr_FR",
    }
    with tempfile.TemporaryDirectory() as raw:
        with patch.dict(os.environ, hostile_environment, clear=False):
            sanitized = validation_singleflight.command_environment()
            require(
                all(
                    key not in sanitized
                    for key in hostile_environment
                    if key not in {"LC_ALL", "LANG", "LANGUAGE"}
                ),
                "dependency environment retained a hostile selector",
            )
            require(
                sanitized["LC_ALL"] == "C.UTF-8",
                "dependency environment lost canonical LC_ALL",
            )
            require(
                sanitized["LANG"] == "C.UTF-8",
                "dependency environment lost canonical LANG",
            )
            child = build_lean_dependency_index.run(
                [
                    sys.executable,
                    "-c",
                    "import json, os; print(json.dumps({k: os.environ[k] for k in "
                    "('GIT_DIR', 'GIT_NAMESPACE', 'GIT_REPLACE_REF_BASE', 'PYTHONPATH', "
                    "'LC_ALL', 'LANG', 'LANGUAGE', 'PATH') "
                    "if k in os.environ}))",
                ],
                cwd=Path(raw),
                capture_output=True,
                text=True,
                check=False,
            )
            require(child.returncode == 0, "dependency child process failed")
            child_environment = json.loads(child.stdout)
            require(
                child_environment == {
                    "LC_ALL": "C.UTF-8",
                    "LANG": "C.UTF-8",
                    "LANGUAGE": "C.UTF-8",
                    "PATH": os.pathsep.join(
                        (str(build_lean_dependency_index.TOOLCHAIN_BIN), os.defpath)
                    ),
                },
                "dependency child process inherited a hostile selector or lost elan",
            )
            with patch.object(
                build_lean_dependency_index.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(["fixture"], 0),
            ) as runner:
                observed = build_lean_dependency_index.run(
                    ["fixture"], cwd=Path(raw), check=False
                )
            require(observed.returncode == 0, "dependency run helper failed")
            kwargs = runner.call_args.kwargs
            expected_environment = validation_singleflight.command_environment()
            expected_environment["PATH"] = os.pathsep.join(
                (str(build_lean_dependency_index.TOOLCHAIN_BIN), os.defpath)
            )
            require(
                kwargs["env"] == expected_environment,
                "dependency run helper drifted from the canonical environment",
            )
            # The worker budget, not the Git one. Both callers of this helper
            # elaborate Lean state, and GIT_COMMAND_TIMEOUT_SECONDS is 30s --
            # the bound for metadata-only Git queries. Asserting it here would
            # demand that a cold dependency build finish inside half a minute,
            # which is why build_lean_dependency_index.run defaults to the
            # worker timeout and says so.
            require(
                kwargs["timeout"]
                == validation_singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
                "dependency run helper lost its bounded timeout",
            )

            export_file = Path(raw) / "graph.tsv"
            with patch.object(
                build_lean_dependency_index.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(["fixture"], 0),
            ) as runner:
                build_lean_dependency_index.run(
                    ["fixture"],
                    cwd=Path(raw),
                    check=False,
                    lean_dependency_export_file=export_file,
                )
            require(
                runner.call_args.kwargs["env"][
                    build_lean_dependency_index.LEAN_DEPENDENCY_EXPORT_FILE_ENV
                ]
                == str(export_file),
                "dependency exporter path was not passed through the clean child environment",
            )

        diagnostic_log = Path(raw) / "diagnostics.log"
        observed_export_path: Path | None = None

        def successful_export(*_args: object, **kwargs: object):
            nonlocal observed_export_path
            observed_export_path = Path(str(kwargs["lean_dependency_export_file"]))
            observed_export_path.write_text(
                "AIW_NODE\tExample.source\tErdosProblems.Example\n"
                "AIW_INTERNAL_OMISSION\tExample.source\t0\n",
                encoding="utf-8",
            )
            return subprocess.CompletedProcess(
                ["fixture"], 0, stdout="compiler diagnostic\n", stderr=""
            )

        with patch.object(build_lean_dependency_index, "run", successful_export), patch.object(
            build_lean_dependency_index, "EXPORT_DIAGNOSTIC_LOG", diagnostic_log
        ):
            nodes, relations, omissions, shapes = (
                build_lean_dependency_index.export_environment()
            )
        require(
            nodes == {"Example.source": "ErdosProblems.Example"},
            "file-backed dependency export lost its node",
        )
        require(not relations and not shapes, "minimal export grew invented rows")
        require(omissions == {"Example.source": 0}, "omission row was not parsed")
        require(
            observed_export_path is not None and not observed_export_path.exists(),
            "unique dependency export file survived its temporary lifetime",
        )
        require(
            diagnostic_log.read_text(encoding="utf-8") == "compiler diagnostic\n",
            "compiler stdout was not retained as diagnostics",
        )

        rejected_export_paths: list[Path] = []
        for mode, expected in (
            ("missing", "readable UTF-8 export"),
            ("empty", "empty export"),
            ("whitespace", "empty export"),
            ("malformed", "malformed export"),
        ):
            def rejected_export(*_args: object, **kwargs: object):
                path = Path(str(kwargs["lean_dependency_export_file"]))
                rejected_export_paths.append(path)
                if mode == "empty":
                    path.write_text("", encoding="utf-8")
                elif mode == "whitespace":
                    path.write_text("\n", encoding="utf-8")
                elif mode == "malformed":
                    path.write_text("not an exporter row\n", encoding="utf-8")
                return subprocess.CompletedProcess(
                    ["fixture"], 0, stdout="", stderr=""
                )

            with patch.object(build_lean_dependency_index, "run", rejected_export):
                try:
                    build_lean_dependency_index.export_environment()
                except build_lean_dependency_index.ClassifiedExportError as exc:
                    require(exc.outcome == "export_crash", f"{mode} export misclassified")
                    require(expected in exc.detail, f"{mode} export detail was not concrete")
                else:
                    raise AssertionError(f"{mode} export was accepted")
        require(
            len(set(rejected_export_paths)) == len(rejected_export_paths),
            "dependency exporter reused a previous temporary output path",
        )

        failed_export_path: Path | None = None

        def failed_export(*_args: object, **kwargs: object):
            nonlocal failed_export_path
            failed_export_path = Path(str(kwargs["lean_dependency_export_file"]))
            failed_export_path.write_text("stale partial row", encoding="utf-8")
            return subprocess.CompletedProcess(
                ["fixture"], 7, stdout="compiler stdout\n", stderr="compiler stderr\n"
            )

        with patch.object(build_lean_dependency_index, "run", failed_export), patch.object(
            build_lean_dependency_index, "EXPORT_DIAGNOSTIC_LOG", diagnostic_log
        ):
            try:
                build_lean_dependency_index.export_environment()
            except build_lean_dependency_index.ClassifiedExportError as exc:
                require(exc.outcome == "export_crash", "failed export misclassified")
                require("exited 7" in exc.detail, "failed export lost its exit status")
            else:
                raise AssertionError("failed dependency export was accepted")
        require(
            failed_export_path is not None and not failed_export_path.exists(),
            "failed dependency export left its partial output behind",
        )
        failed_diagnostics = diagnostic_log.read_text(encoding="utf-8")
        require(
            "compiler stdout" in failed_diagnostics
            and "compiler stderr" in failed_diagnostics,
            "failed dependency export dropped compiler diagnostics",
        )

    require(
        build_lean_dependency_index.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "dependency environment contract drifted",
    )
    print(
        "test_lean_dependency_environment: dependency-bootstrap child processes "
        "cannot inherit caller Git or Python selectors"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
