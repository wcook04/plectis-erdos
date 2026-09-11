#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial checks for the exact Lean dependency-index check receipt."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch

from lean_source import library_dir, library_root_file


ROOT = Path(__file__).resolve().parent.parent
MODULE_PATH = ROOT / "scripts" / "build_lean_dependency_index.py"


def require(condition: bool, message: str) -> None:
    """Keep dependency-index assertions active when Python runs with -O."""
    if not condition:
        raise AssertionError(message)


SPEC = importlib.util.spec_from_file_location(
    "build_lean_dependency_index",
    MODULE_PATH,
)
require(SPEC is not None and SPEC.loader is not None, "dependency-index module loader is unavailable")
builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(builder)


def sha256_text(content: str) -> str:
    return f"sha256:{hashlib.sha256(content.encode('utf-8')).hexdigest()}"


def check_exact_receipt_contract() -> None:
    input_fingerprint = "sha256:input"
    output_digest = "sha256:output"
    receipt = {
        "schema": builder.CHECK_RECEIPT_SCHEMA,
        "builder_schema": builder.SCHEMA,
        "input_fingerprint": input_fingerprint,
        "output_digest": output_digest,
    }
    require(
        builder.receipt_matches(
            receipt,
            input_fingerprint=input_fingerprint,
            output_digest=output_digest,
        ),
        "canonical dependency-index receipt was rejected",
    )
    mutations = (
        ("schema", "wrong"),
        ("builder_schema", "wrong"),
        ("input_fingerprint", "sha256:changed"),
        ("output_digest", "sha256:changed"),
    )
    for field, value in mutations:
        changed = {**receipt, field: value}
        require(
            not builder.receipt_matches(
                changed,
                input_fingerprint=input_fingerprint,
                output_digest=output_digest,
            ),
            f"dependency-index receipt mutation was accepted: {field}",
        )


def check_live_input_surface() -> None:
    paths = builder.check_input_paths()
    relative = {path.relative_to(ROOT).as_posix() for path in paths}
    require(
        set(builder.CHECK_INPUT_FILES).issubset(relative),
        "dependency-index input file set is incomplete",
    )
    for library_root in builder.LEAN_ROOT_TARGETS:
        root_file = library_root_file(ROOT, library_root).relative_to(ROOT).as_posix()
        descendant_prefix = (
            library_dir(ROOT, library_root).relative_to(ROOT).as_posix() + "/"
        )
        require(
            root_file in relative,
            f"dependency-index root is missing: {root_file}",
        )
        require(
            any(
                name.startswith(descendant_prefix) and name.endswith(".lean")
                for name in relative
            ),
            f"dependency-index root has no public Lean descendants: {library_root}",
        )
    require(
        len(paths) == len(set(paths)),
        "dependency-index input paths are duplicated",
    )
    require(
        "docs/claims.json" not in relative,
        "dependency-index unexpectedly includes the claims projection",
    )
    require(
        "scripts/query_corpus.py" not in relative,
        "dependency-index unexpectedly includes the query corpus",
    )
    require(
        "scripts/build_lean_dependency_index.py" not in relative
        and "scripts/lean_fast_build.py" not in relative
        and "scripts/build_declaration_atlas.py" not in relative,
        "operational wrapper churn invalidates the semantic projection receipt",
    )
    require(
        "docs/declaration_atlas.json" in relative,
        "dependency index lost its authoritative upstream atlas artifact",
    )
    semantic_identities = {
        identity for identity, _payload in builder.semantic_check_inputs()
    }
    require(
        semantic_identities == {
            "docs/claims.json::release.formal_source",
            "scripts/query_corpus.py::dependency_helpers",
        },
        "dependency-index semantic input identities drifted",
    )
    require(
        builder.check_input_fingerprint().startswith("sha256:"),
        "dependency-index input fingerprint is not a SHA-256 digest",
    )
    require(
        builder.ENVIRONMENT_VALIDATION_COMMAND
        == (
            "python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness "
            "Erdos249257 ErdosProblems"
        ),
        "dependency-index metadata bypasses the coordinated Lean build owner",
    )
    committed = json.loads(builder.OUTPUT.read_text(encoding="utf-8"))
    require(
        committed["environment_validation"]["command"]
        == builder.ENVIRONMENT_VALIDATION_COMMAND,
        "committed dependency-index build guidance drifted from its producer",
    )


def check_cached_output_rejection() -> None:
    with tempfile.TemporaryDirectory() as directory:
        temporary_root = Path(directory)
        output = temporary_root / "index.json"
        receipt_path = temporary_root / "receipt.json"
        output.write_text('{"current":true}\n', encoding="utf-8")
        fingerprint = builder.check_input_fingerprint()
        receipt = {
            "schema": builder.CHECK_RECEIPT_SCHEMA,
            "builder_schema": builder.SCHEMA,
            "input_fingerprint": fingerprint,
            "output_digest": sha256_text(output.read_text(encoding="utf-8")),
        }
        receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
        require(
            builder.load_cached_check(
                root=ROOT,
                output=output,
                receipt_path=receipt_path,
            )
            == receipt,
            "valid dependency-index cache receipt was not loaded",
        )
        output.write_text('{"current":false}\n', encoding="utf-8")
        require(
            builder.load_cached_check(
                root=ROOT,
                output=output,
                receipt_path=receipt_path,
            )
            is None,
            "stale dependency-index cache output was accepted",
        )
        linked = temporary_root / "linked-index.json"
        linked.symlink_to(output)
        require(
            builder.load_cached_check(
                root=ROOT,
                output=linked,
                receipt_path=receipt_path,
            )
            is None,
            "symlinked dependency-index cache output was accepted",
        )


def check_tracked_cold_clone_receipt() -> None:
    require(
        builder.TRACKED_CHECK_RECEIPT.is_file(),
        "tracked cold-clone receipt is missing",
    )
    receipt = json.loads(
        builder.TRACKED_CHECK_RECEIPT.read_text(encoding="utf-8")
    )
    require(
        receipt.get("schema") == builder.CHECK_RECEIPT_SCHEMA
        and receipt.get("builder_schema") == builder.SCHEMA,
        "tracked cold-clone receipt schema drifted",
    )
    require(
        receipt.get("output_digest")
        == sha256_text(builder.OUTPUT.read_text(encoding="utf-8")),
        "tracked cold-clone receipt no longer owns the committed index",
    )
    require(
        receipt["verification_posture"].startswith("tracked_receipt_from_full_"),
        "tracked receipt lost its full-export provenance boundary",
    )
    cached = builder.load_cached_check(
        receipt_path=builder.TRACKED_CHECK_RECEIPT,
    )
    if cached is not None:
        require(
            cached == receipt,
            "exact tracked cache lookup returned a different receipt",
        )


def check_safe_dependency_input_boundary() -> None:
    with tempfile.TemporaryDirectory(prefix="dependency-input-") as directory:
        workspace = Path(directory)
        regular = workspace / "regular.txt"
        regular.write_text("dependency input\n", encoding="utf-8")
        require(
            builder.safe_dependency_text(regular, root=workspace)
            == "dependency input\n",
            "safe dependency input reader rejected a regular file",
        )

        directory_input = workspace / "directory"
        directory_input.mkdir()
        try:
            builder.safe_dependency_text(directory_input, root=workspace)
        except builder.UnsafeDependencyInput:
            pass
        else:
            raise AssertionError("dependency directory input escaped the regular-file boundary")

        symlink = workspace / "symlink.txt"
        symlink.symlink_to(regular)
        try:
            builder.safe_dependency_text(symlink, root=workspace)
        except builder.UnsafeDependencyInput:
            pass
        else:
            raise AssertionError("dependency symlink input escaped the no-follow boundary")

        if hasattr(os, "mkfifo"):
            fifo = workspace / "fifo"
            os.mkfifo(fifo)
            try:
                builder.safe_dependency_text(fifo, root=workspace)
            except builder.UnsafeDependencyInput:
                pass
            else:
                raise AssertionError("dependency FIFO input escaped the non-blocking boundary")


def check_safe_dependency_output_boundary() -> None:
    with tempfile.TemporaryDirectory(prefix="dependency-output-") as directory:
        workspace = Path(directory)
        regular = workspace / "regular.json"
        builder.safe_output_text(regular, '{"safe":true}\n', root=workspace)
        require(
            regular.read_text(encoding="utf-8") == '{"safe":true}\n',
            "regular dependency output was not written through the safe descriptor",
        )

        private = workspace / "private.json"
        private.write_text('{"private":true}\n', encoding="utf-8")
        linked = workspace / "linked.json"
        linked.symlink_to(private)
        try:
            builder.safe_output_text(linked, '{"public":true}\n', root=workspace)
        except builder.UnsafeDependencyInput:
            pass
        else:
            raise AssertionError("dependency output followed a final-component symlink")
        require(
            private.read_text(encoding="utf-8") == '{"private":true}\n',
            "dependency output symlink target was modified",
        )

        if hasattr(os, "mkfifo"):
            fifo = workspace / "output.fifo"
            os.mkfifo(fifo)
            try:
                builder.safe_output_text(fifo, "blocked\n", root=workspace)
            except builder.UnsafeDependencyInput:
                pass
            else:
                raise AssertionError("dependency output accepted a special file")


def check_receipt_uses_verified_snapshot() -> None:
    with tempfile.TemporaryDirectory() as directory:
        receipt_path = Path(directory) / "receipt.json"
        packet = {
            "source_fingerprint": "sha256:source",
            "coverage": {
                "source_resolved_node_count": 2,
                "source_resolved_direct_edge_count": 3,
            },
        }
        builder.write_check_receipt(
            '{"packet":true}\n',
            packet,
            input_fingerprint="sha256:verified-at-start",
            receipt_path=receipt_path,
        )
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        require(
            receipt["input_fingerprint"] == "sha256:verified-at-start",
            "dependency-index receipt did not retain its verified snapshot input",
        )


def check_guarded_metadata_refresh() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        docs = root / "docs"
        local = root / ".lake" / "aiw"
        docs.mkdir()
        local.mkdir(parents=True)
        output = docs / "lean_dependency_index.json"
        tracked = docs / "lean_dependency_index_check.json"
        local_receipt = local / "lean_dependency_index_check.json"
        packet = {
            "kind": "lean_dependency_index",
            "schema_version": builder.SCHEMA,
            "source_fingerprint": "sha256:source",
            "environment_validation": {
                "command": "lake build Erdos249257 ErdosProblems",
                "posture": builder.ENVIRONMENT_VALIDATION_POSTURE,
            },
            "coverage": {
                "loaded_library_roots": list(builder.LEAN_ROOT_TARGETS),
                "source_resolved_node_count": 2,
                "source_resolved_direct_edge_count": 3,
            },
        }
        original = builder.encoded(packet)
        output.write_text(original, encoding="utf-8")
        (docs / "declaration_atlas.json").write_text(
            json.dumps({"source_fingerprint": "sha256:source"}),
            encoding="utf-8",
        )
        tracked.write_text(
            json.dumps(
                {
                    "schema": builder.CHECK_RECEIPT_SCHEMA,
                    "builder_schema": builder.SCHEMA,
                    "output_digest": sha256_text(original),
                    "source_fingerprint": "sha256:source",
                    "source_resolved_node_count": 2,
                    "source_resolved_direct_edge_count": 3,
                    "verification_posture": "tracked_receipt_from_full_export",
                }
            ),
            encoding="utf-8",
        )
        with patch.object(
            builder,
            "check_input_fingerprint",
            return_value="sha256:current-input",
        ):
            refreshed = builder.refresh_environment_validation_metadata(
                root=root,
                output=output,
                tracked_receipt_path=tracked,
                local_receipt_path=local_receipt,
            )
        require(
            refreshed["environment_validation"]["command"]
            == builder.ENVIRONMENT_VALIDATION_COMMAND,
            "metadata refresh did not install coordinated build guidance",
        )
        for receipt_path in (tracked, local_receipt):
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            require(
                receipt["input_fingerprint"] == "sha256:current-input"
                and receipt["output_digest"]
                == sha256_text(output.read_text(encoding="utf-8")),
                "metadata refresh did not bind the migrated output receipt",
            )

        packet["source_fingerprint"] = "sha256:changed"
        output.write_text(builder.encoded(packet), encoding="utf-8")
        try:
            builder.refresh_environment_validation_metadata(
                root=root,
                output=output,
                tracked_receipt_path=tracked,
                local_receipt_path=local_receipt,
            )
        except RuntimeError:
            pass
        else:
            raise AssertionError("metadata refresh accepted a changed source identity")


def check_environment_build_is_bounded() -> None:
    hostile_environment = {
        "GIT_DIR": "/private/wrong-git-dir",
        "GIT_NAMESPACE": "refs/namespaces/wrong-dependency",
        "GIT_REPLACE_REF_BASE": "refs/replace/",
        "PYTHONPATH": "/private/wrong-python-path",
        "LC_ALL": "C",
        "LANG": "C",
        "PATH": "/private/wrong-bin",
    }
    with patch.dict(os.environ, hostile_environment, clear=False):
        with patch.object(builder.subprocess, "run") as run:
            run.return_value.returncode = 0
            builder.ensure_elaborated_environment()
    require(
        run.call_args.args[0]
        == [
            builder.sys.executable,
            str(builder.LEAN_FAST_BUILD),
            "--lake-staleness",
            *builder.LEAN_ROOT_TARGETS,
        ],
        "direct dependency bootstrap bypassed the shared Lean owner",
    )
    require(run.call_args.kwargs["cwd"] == builder.ROOT, "bootstrap cwd drifted")
    sanitized = run.call_args.kwargs["env"]
    for key in (
        "GIT_DIR",
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "PYTHONPATH",
    ):
        require(key not in sanitized, f"ambient {key} leaked into bootstrap")
    require(sanitized["LC_ALL"] == "C.UTF-8", "canonical locale missing")
    require(sanitized["LANG"] == "C.UTF-8", "canonical LANG missing")
    require(
        sanitized["PATH"]
        == os.pathsep.join((str(builder.TOOLCHAIN_BIN), os.defpath)),
        "bootstrap lost the documented elan toolchain or admitted ambient PATH",
    )
    require(
        run.call_args.kwargs["timeout"]
        == builder.LEAN_ROOT_BUILD_TIMEOUT_SECONDS,
        "Lean root build lost its distinct cold-bootstrap timeout budget",
    )
    require(
        builder.LEAN_ROOT_BUILD_TIMEOUT_SECONDS
        > builder.singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
        "Lean root build collapsed back onto the generic worker timeout",
    )
    require(
        builder.ENVIRONMENT_CONTRACT
        == "clean_committed_snapshot_subprocess_environment_v1",
        "dependency-index environment contract drifted",
    )

    with patch.dict(
        os.environ,
        {builder.singleflight.HOST_LOCK_HELD_ENV: "1"},
        clear=False,
    ):
        with patch.object(builder.subprocess, "run") as run:
            run.return_value.returncode = 0
            builder.ensure_elaborated_environment()
    require(
        run.call_args.args[0]
        == [
            builder.sys.executable,
            str(builder.LEAN_FAST_BUILD),
            "--singleflight-worker",
            "--lake-staleness",
            *builder.LEAN_ROOT_TARGETS,
        ],
        "dependency bootstrap tried to reacquire its already-held Lean lock",
    )

    for observed, expected in ((-15, 143), (143, 143)):
        killed = builder.subprocess.CompletedProcess([], observed, "partial build\n")
        with patch.object(builder, "run", return_value=killed):
            try:
                builder.ensure_elaborated_environment()
            except SystemExit as exc:
                require(exc.code == expected, "external signal exit was not preserved")
            else:
                raise AssertionError("external signal exit became a successful build")


def check_plain_check_never_builds() -> None:
    """A read-looking cache check must not acquire the Lean build owner."""
    with patch.object(builder, "load_cached_check", return_value=None):
        with patch.object(builder, "build_packet") as build_packet:
            with patch.object(
                builder.sys,
                "argv",
                ["build_lean_dependency_index.py", "--check"],
            ):
                require(
                    builder.main() == 1,
                    "stale ordinary dependency-index check did not fail fast",
                )
    require(
        not build_packet.called,
        "ordinary dependency-index --check unexpectedly launched Lean export",
    )


def check_write_stale_requires_full_check() -> None:
    with patch.object(
        builder.sys,
        "argv",
        ["build_lean_dependency_index.py", "--check", "--write-stale"],
    ):
        try:
            builder.main()
        except SystemExit as exc:
            require(
                exc.code == 2,
                "--write-stale without --full-check did not fail at parse",
            )
            return
    raise AssertionError("--write-stale without --full-check was accepted")


def check_export_timeout_does_not_rewrite_tracked_index() -> None:
    """A 5400s exporter timeout must not relabel the committed index as fresh."""
    with tempfile.TemporaryDirectory() as directory:
        tracked = Path(directory) / "lean_dependency_index.json"
        tracked.write_text("tracked-not-fresh\n", encoding="utf-8")
        diagnostic = Path(directory) / "diagnostics.log"
        with patch.object(builder, "OUTPUT", tracked):
            with patch.object(builder, "EXPORT_DIAGNOSTIC_LOG", diagnostic):
                with patch.object(
                    builder,
                    "run",
                    side_effect=subprocess.TimeoutExpired(
                        ["lake", "env", "lean"],
                        5400,
                        output=b"partial exporter output",
                    ),
                ):
                    try:
                        builder.export_environment()
                    except builder.ClassifiedExportError as exc:
                        require(
                            exc.outcome == "export_timeout",
                            "export timeout was not classified",
                        )
                        require(
                            exc.exit_code == builder.EXIT_TIMEOUT,
                            "export timeout exit drifted",
                        )
                    else:
                        raise AssertionError("export timeout was not classified")
        require(
            tracked.read_text(encoding="utf-8") == "tracked-not-fresh\n",
            "export timeout rewrote the tracked dependency index",
        )
        require(
            diagnostic.is_file()
            and "partial exporter output" in diagnostic.read_text(encoding="utf-8"),
            "export timeout dropped diagnostics",
        )


def check_main_classifies_export_timeout_without_fresh_upload() -> None:
    with tempfile.TemporaryDirectory() as directory:
        github_output = Path(directory) / "github_output"
        outcome = Path(directory) / "outcome.json"
        tracked = Path(directory) / "tracked.json"
        tracked.write_text("tracked-not-fresh\n", encoding="utf-8")
        with patch.dict(
            os.environ,
            {
                "GITHUB_OUTPUT": str(github_output),
                "GITHUB_SHA": "merge-sha",
                "PLECTIS_PR_HEAD_SHA": "head-sha",
            },
            clear=False,
        ):
            with patch.object(builder, "OUTPUT", tracked):
                with patch.object(builder, "CI_OUTCOME_PATH", outcome):
                    with patch.object(
                        builder, "check_input_fingerprint", return_value="stable"
                    ):
                        with patch.object(
                            builder,
                            "build_packet",
                            side_effect=builder.ClassifiedExportError(
                                "export_timeout",
                                builder.EXIT_TIMEOUT,
                                "timed out",
                            ),
                        ):
                            with patch.object(
                                builder.sys,
                                "argv",
                                [
                                    "build_lean_dependency_index.py",
                                    "--check",
                                    "--full-check",
                                    "--write-stale",
                                ],
                            ):
                                code = builder.main()
        require(code == builder.EXIT_TIMEOUT, "timeout did not return classified exit")
        require(
            tracked.read_text(encoding="utf-8") == "tracked-not-fresh\n",
            "timeout rewrote the tracked dependency index",
        )
        payload = json.loads(outcome.read_text(encoding="utf-8"))
        require(payload["outcome"] == "export_timeout", "timeout outcome drifted")
        require(
            payload["fresh_export_written"] is False,
            "timeout labeled tracked files as a fresh export",
        )
        emitted = github_output.read_text(encoding="utf-8")
        require(
            "fresh_export_written=false" in emitted,
            "timeout did not tell Actions to skip the fresh-export upload",
        )
        require("head-sha" in emitted, "timeout receipt dropped the PR head SHA")


def check_unfinished_outcome_refuses_fresh_export_label() -> None:
    with tempfile.TemporaryDirectory() as directory:
        missing = Path(directory) / "missing.json"
        with patch.object(builder, "CI_OUTCOME_PATH", missing):
            with patch.object(
                builder.sys,
                "argv",
                [
                    "build_lean_dependency_index.py",
                    "--report-ci-outcome",
                    "--fail-ci-outcome",
                ],
            ):
                code = builder.main()
        require(
            code == builder.EXIT_CRASH,
            "a missing outcome file was treated as a stale export",
        )


def main() -> int:
    check_safe_dependency_input_boundary()
    check_safe_dependency_output_boundary()
    check_exact_receipt_contract()
    check_live_input_surface()
    check_cached_output_rejection()
    check_tracked_cold_clone_receipt()
    check_receipt_uses_verified_snapshot()
    check_guarded_metadata_refresh()
    check_environment_build_is_bounded()
    check_plain_check_never_builds()
    check_write_stale_requires_full_check()
    check_export_timeout_does_not_rewrite_tracked_index()
    check_main_classifies_export_timeout_without_fresh_upload()
    check_unfinished_outcome_refuses_fresh_export_label()
    print("lean dependency index cache: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
