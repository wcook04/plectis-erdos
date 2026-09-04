#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Run or validate a source-bound reproduction in an isolated tree.

The source identity is computed without version-control metadata.  Execution
copies the identified source files to a temporary directory, runs a declared
command plan there, and writes a receipt only after confirming that the copied
source files still have the same identity.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import platform
import re
import resource
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable

import validation_singleflight as singleflight


SCHEMA = "erdos249257-source-bound-reproduction/1"
ENVIRONMENT_CONTRACT = "clean_reproduction_subprocess_environment_v1"
COMMAND_TIMEOUT_SECONDS = singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS
TOOLCHAIN_BIN = Path.home() / ".elan" / "bin"
TOOLCHAIN_COMMANDS = frozenset({"elan", "lake", "lean"})
TAIL_BYTES = 16_000
DEFAULT_MAX_AGE_SECONDS = 30 * 24 * 60 * 60
CANONICAL_RECEIPT_PATH = "docs/measurements/source_bound_reproduction_receipt.json"
EXCLUSION_POLICY = {
    "version": 1,
    "excluded_directory_names": [
        ".git",
        ".lake",
        ".mypy_cache",
        ".pytest_cache",
        "__pycache__",
    ],
    "excluded_file_names": [".DS_Store"],
    "excluded_file_suffixes": [".pyc", ".pyo"],
    "excluded_relative_paths": [CANONICAL_RECEIPT_PATH],
}


def command(
    command_id: str,
    argv: list[str],
    *,
    expect_empty_stdout: bool = False,
    expect_empty_stderr: bool = False,
    requires_git: bool = False,
) -> dict[str, Any]:
    return {
        "id": command_id,
        "argv": argv,
        "expect_empty_stdout": expect_empty_stdout,
        "expect_empty_stderr": expect_empty_stderr,
        "requires_git": requires_git,
    }


DEFAULT_PLAN = [
    command("mathlib_cache", ["lake", "exe", "cache", "get"]),
    command("root_build", ["lake", "build"]),
    command("downstream_example", ["lake", "build", "Examples"]),
    # The release gate owns projection freshness and semantic consistency.
    # Running its constituent checks here first used to pay the same
    # source scans twice without adding an independent authority boundary.
    command(
        "declaration_head_contract",
        ["python3", "scripts/test_declaration_head_contract.py"],
    ),
    command(
        "projection_checkout_independence",
        ["python3", "scripts/test_projection_checkout_independence.py"],
    ),
    command(
        "release",
        ["python3", "scripts/check_release.py"],
        requires_git=True,
    ),
    command(
        "dependency_lift",
        [
            "lake",
            "build",
            "ErdosProblems.Lift.Recon67",
            "ErdosProblems.Lift.CertT67",
        ],
    ),
    command(
        "focused_recon67",
        ["lake", "env", "lean", "ErdosProblems/Lift/Recon67.lean"],
        expect_empty_stdout=True,
        expect_empty_stderr=True,
    ),
    command(
        "focused_cert_t67",
        ["lake", "env", "lean", "ErdosProblems/Lift/CertT67.lean"],
        expect_empty_stdout=True,
        expect_empty_stderr=True,
    ),
    command(
        "dependency_three",
        [
            "lake",
            "build",
            "ErdosProblems.Three.T1",
            "ErdosProblems.Decl.D4",
        ],
    ),
    command(
        "focused_ladder",
        ["lake", "env", "lean", "ErdosProblems/Skip/LadderT67.lean"],
        expect_empty_stdout=True,
        expect_empty_stderr=True,
    ),
    command(
        "focused_free_position",
        [
            "lake",
            "env",
            "lean",
            "ErdosProblems/FreePosition/FreeKill64OneHundredFifteenDI.lean",
        ],
        expect_empty_stdout=True,
        expect_empty_stderr=True,
    ),
    command(
        "focused_three",
        ["lake", "env", "lean", "ErdosProblems/Three/T1.lean"],
        expect_empty_stdout=True,
        expect_empty_stderr=True,
    ),
    command(
        "focused_decl",
        ["lake", "env", "lean", "ErdosProblems/Decl/D4.lean"],
        expect_empty_stdout=True,
        expect_empty_stderr=True,
    ),
    command(
        "focused_hlow",
        ["lake", "env", "lean", "ErdosProblems/Hlow/H2.lean"],
        expect_empty_stdout=True,
        expect_empty_stderr=True,
    ),
]


class ReproductionError(RuntimeError):
    """Raised when preparation, execution, or validation fails."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _path_has_symlink_component(path: Path) -> bool:
    """Reject a file path whose bytes could be substituted through a link."""
    current = Path(os.path.abspath(path))
    while True:
        if current.is_symlink():
            if current == Path("/var") and current.resolve(strict=True) == Path("/private/var"):
                current = current.resolve(strict=True)
                continue
            if current == Path("/tmp") and current.resolve(strict=True) == Path("/private/tmp"):
                current = current.resolve(strict=True)
                continue
            return True
        if current.parent == current:
            return False
        current = current.parent


def _read_regular_json(path: Path, label: str) -> Any:
    """Read JSON only from a regular, non-symlinked file descriptor."""
    if _path_has_symlink_component(path):
        raise ReproductionError(f"{label} path contains a symlink: {path}")
    flags = os.O_RDONLY
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ReproductionError(f"{label} path is not a regular file: {path}")
        with os.fdopen(descriptor, "r", encoding="utf-8") as stream:
            descriptor = -1
            return json.load(stream)
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def _check_receipt_destination(path: Path) -> None:
    """Reject symlinked or special receipt destinations before opening them."""
    if _path_has_symlink_component(path):
        raise ReproductionError(f"receipt destination contains a symlink: {path}")
    try:
        mode = os.lstat(path).st_mode
    except FileNotFoundError:
        return
    if not stat.S_ISREG(mode):
        raise ReproductionError(f"receipt destination is not a regular file: {path}")


def _write_regular_receipt(path: Path, payload: str, *, overwrite: bool) -> None:
    """Write a receipt through a regular, no-following file descriptor."""
    _check_receipt_destination(path)
    if path.exists() and not overwrite:
        raise ReproductionError(
            f"receipt already exists; pass --overwrite to replace it: {path}"
        )
    path.parent.mkdir(parents=True, exist_ok=True)
    _check_receipt_destination(path)
    flags = os.O_WRONLY | os.O_CREAT
    flags |= getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    flags |= os.O_TRUNC if overwrite else os.O_EXCL
    descriptor = os.open(path, flags, 0o644)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ReproductionError(f"receipt destination is not a regular file: {path}")
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            descriptor = -1
            stream.write(payload)
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def canonical_json(value: Any) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def is_excluded(relative: Path) -> bool:
    if relative.as_posix() in EXCLUSION_POLICY["excluded_relative_paths"]:
        return True
    directory_names = set(EXCLUSION_POLICY["excluded_directory_names"])
    if any(part in directory_names for part in relative.parts[:-1]):
        return True
    if relative.name in EXCLUSION_POLICY["excluded_file_names"]:
        return True
    return relative.suffix in EXCLUSION_POLICY["excluded_file_suffixes"]


def source_manifest(root: Path) -> list[dict[str, Any]]:
    root = root.resolve()
    if not root.is_dir():
        raise ReproductionError(f"source root is not a directory: {root}")
    rows: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if is_excluded(relative):
            continue
        if path.is_symlink():
            raise ReproductionError(f"source manifest rejects symlink: {relative}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise ReproductionError(f"source manifest rejects special file: {relative}")
        data = path.read_bytes()
        rows.append(
            {
                "path": relative.as_posix(),
                "size_bytes": len(data),
                "sha256": sha256_bytes(data),
            }
        )
    return rows


def source_identity(root: Path) -> dict[str, Any]:
    manifest = source_manifest(root)
    identity_payload = {
        "exclusion_policy": EXCLUSION_POLICY,
        "files": manifest,
    }
    return {
        "source_digest": sha256_bytes(canonical_json(identity_payload)),
        "manifest_digest": sha256_bytes(canonical_json(manifest)),
        "file_count": len(manifest),
        "exclusion_policy": EXCLUSION_POLICY,
    }


def copy_source(source_root: Path, destination: Path) -> None:
    source_root = source_root.resolve()
    destination.mkdir(parents=True, exist_ok=False)
    for row in source_manifest(source_root):
        relative = Path(row["path"])
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_root / relative, target)


def copy_version_control_metadata(source_root: Path, destination: Path) -> None:
    """Copy ``.git`` only for an explicitly authorised Git-capable plan."""
    source = source_root.resolve() / ".git"
    target = destination / ".git"
    if source.is_dir():
        shutil.copytree(source, target, symlinks=True)
    elif source.is_file():
        shutil.copy2(source, target)
    else:
        raise ReproductionError(
            "Git-capable plan requested, but the source root has no .git metadata"
        )


def load_plan(path: Path | None) -> list[dict[str, Any]]:
    value = DEFAULT_PLAN if path is None else _read_regular_json(path, "command plan")
    if not isinstance(value, list) or not value:
        raise ReproductionError("command plan must be a nonempty JSON list")
    result: list[dict[str, Any]] = []
    ids: set[str] = set()
    for index, item in enumerate(value):
        if not isinstance(item, dict):
            raise ReproductionError(f"command plan row {index} is not an object")
        command_id = item.get("id")
        argv = item.get("argv")
        if not isinstance(command_id, str) or not command_id or command_id in ids:
            raise ReproductionError(f"command plan row {index} has an invalid id")
        if (
            not isinstance(argv, list)
            or not argv
            or not all(isinstance(part, str) and part for part in argv)
        ):
            raise ReproductionError(f"command plan row {index} has invalid argv")
        ids.add(command_id)
        result.append(
            command(
                command_id,
                argv,
                expect_empty_stdout=bool(item.get("expect_empty_stdout", False)),
                expect_empty_stderr=bool(item.get("expect_empty_stderr", False)),
                requires_git=bool(item.get("requires_git", False)),
            )
        )
    return result


def bounded_tail(data: bytes) -> str:
    return data[-TAIL_BYTES:].decode("utf-8", errors="replace")


def execution_environment(argv: list[str]) -> dict[str, str]:
    """Remove ambient configuration while retaining the pinned tool path."""
    environment = singleflight.command_environment()
    if argv and Path(argv[0]).name in TOOLCHAIN_COMMANDS:
        tool_directory = str(TOOLCHAIN_BIN)
        path = environment.get("PATH", os.defpath).split(os.pathsep)
        if tool_directory not in path:
            environment["PATH"] = os.pathsep.join([tool_directory, *path])
    return environment


def run_command(spec: dict[str, Any], cwd: Path) -> dict[str, Any]:
    started_at = utc_now()
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    completed = subprocess.run(
        spec["argv"],
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        env=execution_environment(spec["argv"]),
        timeout=COMMAND_TIMEOUT_SECONDS,
    )
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    stdout = completed.stdout
    stderr = completed.stderr
    stdout_tail = stdout[-TAIL_BYTES:]
    stderr_tail = stderr[-TAIL_BYTES:]
    return {
        **spec,
        "started_at": started_at,
        "completed_at": utc_now(),
        "exit_code": completed.returncode,
        "wall_time_seconds": round(time.monotonic() - started, 6),
        "user_time_seconds": round(after.ru_utime - before.ru_utime, 6),
        "sys_time_seconds": round(after.ru_stime - before.ru_stime, 6),
        "stdout_bytes": len(stdout),
        "stderr_bytes": len(stderr),
        "stdout_sha256": sha256_bytes(stdout),
        "stderr_sha256": sha256_bytes(stderr),
        "stdout_tail": bounded_tail(stdout),
        "stderr_tail": bounded_tail(stderr),
        "stdout_tail_bytes": len(stdout_tail),
        "stderr_tail_bytes": len(stderr_tail),
        "stdout_tail_sha256": sha256_bytes(stdout_tail),
        "stderr_tail_sha256": sha256_bytes(stderr_tail),
        "stdout_tail_base64": base64.b64encode(stdout_tail).decode("ascii"),
        "stderr_tail_base64": base64.b64encode(stderr_tail).decode("ascii"),
    }


def host_facts() -> dict[str, Any]:
    uname = platform.uname()
    return {
        "system": uname.system,
        "release": uname.release,
        "machine": uname.machine,
        "python": platform.python_version(),
        "logical_cpu_count": os.cpu_count(),
    }


def execute(
    source_root: Path,
    plan: list[dict[str, Any]],
    *,
    allow_git: bool = False,
) -> dict[str, Any]:
    git_rows = [spec["id"] for spec in plan if spec.get("requires_git")]
    if git_rows and not allow_git:
        raise ReproductionError(
            "plan contains command(s) tagged requires_git; explicit --allow-git "
            "is required: " + ", ".join(git_rows)
        )
    source_root = source_root.resolve()
    identity = source_identity(source_root)
    started_at = utc_now()
    with tempfile.TemporaryDirectory(prefix="plectis-source-repro-") as temp:
        isolated = Path(temp) / "source"
        copy_source(source_root, isolated)
        if git_rows:
            copy_version_control_metadata(source_root, isolated)
        if source_identity(isolated) != identity:
            raise ReproductionError("isolated source identity differs from source root")
        results = [run_command(spec, isolated) for spec in plan]
        if source_identity(isolated) != identity:
            raise ReproductionError("a reproduction command changed identified source files")
    return {
        "schema": SCHEMA,
        "source": identity,
        "source_root_label": source_root.name,
        "snapshot_posture": "isolated_copy_excludes_runtime_and_version_control_state",
        "environment_contract": ENVIRONMENT_CONTRACT,
        "host": host_facts(),
        "started_at": started_at,
        "completed_at": utc_now(),
        "required_command_plan": plan,
        "command_results": results,
    }


def parse_utc(value: Any, field: str) -> datetime:
    if not isinstance(value, str):
        raise ReproductionError(f"{field} must be a UTC timestamp")
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError as error:
        raise ReproductionError(f"{field} is malformed") from error
    if parsed.tzinfo is None or parsed.utcoffset() != timedelta(0):
        raise ReproductionError(f"{field} must carry UTC offset")
    return parsed


def require_nonnegative_number(value: Any, field: str) -> None:
    if isinstance(value, bool) or not isinstance(value, (int, float)) or value < 0:
        raise ReproductionError(f"{field} must be a nonnegative number")


def require_sha256(value: Any, field: str) -> None:
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ReproductionError(f"{field} must be a lowercase SHA-256 digest")


def validate_stream_result(
    result: dict[str, Any],
    spec: dict[str, Any],
    stream: str,
) -> None:
    byte_count = result.get(f"{stream}_bytes")
    if not isinstance(byte_count, int) or isinstance(byte_count, bool) or byte_count < 0:
        raise ReproductionError(f"{spec['id']}.{stream}_bytes is malformed")
    digest = result.get(f"{stream}_sha256")
    require_sha256(digest, f"{spec['id']}.{stream}_sha256")
    tail_text = result.get(f"{stream}_tail")
    if not isinstance(tail_text, str):
        raise ReproductionError(f"{spec['id']}.{stream}_tail is malformed")
    tail_byte_count = result.get(f"{stream}_tail_bytes")
    if (
        not isinstance(tail_byte_count, int)
        or isinstance(tail_byte_count, bool)
        or tail_byte_count < 0
        or tail_byte_count > TAIL_BYTES
        or tail_byte_count > byte_count
    ):
        raise ReproductionError(f"{spec['id']}.{stream}_tail_bytes is malformed")
    tail_digest = result.get(f"{stream}_tail_sha256")
    require_sha256(tail_digest, f"{spec['id']}.{stream}_tail_sha256")
    tail_base64 = result.get(f"{stream}_tail_base64")
    if not isinstance(tail_base64, str):
        raise ReproductionError(f"{spec['id']}.{stream}_tail_base64 is malformed")
    try:
        raw_tail = base64.b64decode(tail_base64, validate=True)
    except (ValueError, base64.binascii.Error) as error:
        raise ReproductionError(
            f"{spec['id']}.{stream}_tail_base64 is malformed"
        ) from error
    if len(raw_tail) != tail_byte_count:
        raise ReproductionError(f"{spec['id']}.{stream} tail length mismatch")
    if sha256_bytes(raw_tail) != tail_digest:
        raise ReproductionError(f"{spec['id']}.{stream} tail digest mismatch")
    if raw_tail.decode("utf-8", errors="replace") != tail_text:
        raise ReproductionError(f"{spec['id']}.{stream} tail text mismatch")
    if byte_count <= TAIL_BYTES and tail_digest != digest:
        raise ReproductionError(f"{spec['id']}.{stream} full digest mismatch")
    if spec[f"expect_empty_{stream}"]:
        if (
            byte_count != 0
            or digest != sha256_bytes(b"")
            or tail_byte_count != 0
            or raw_tail != b""
            or tail_text != ""
        ):
            raise ReproductionError(
                f"command violated empty-{stream} expectation: {spec['id']}"
            )


def validate_receipt(
    receipt: dict[str, Any],
    source_root: Path,
    required_plan: list[dict[str, Any]],
    *,
    max_age_seconds: int = DEFAULT_MAX_AGE_SECONDS,
    now: datetime | None = None,
) -> None:
    if receipt.get("schema") != SCHEMA:
        raise ReproductionError("receipt schema is missing or unsupported")
    if receipt.get("environment_contract") != ENVIRONMENT_CONTRACT:
        raise ReproductionError("receipt environment contract is missing or unsupported")
    started_at = parse_utc(receipt.get("started_at"), "started_at")
    completed_at = parse_utc(receipt.get("completed_at"), "completed_at")
    if completed_at < started_at:
        raise ReproductionError("receipt completion precedes its start")
    current_time = now or datetime.now(timezone.utc)
    if max_age_seconds < 0:
        raise ReproductionError("maximum receipt age must be nonnegative")
    if completed_at > current_time + timedelta(minutes=5):
        raise ReproductionError("receipt completion is implausibly in the future")
    if current_time - completed_at > timedelta(seconds=max_age_seconds):
        raise ReproductionError("receipt is stale")

    source = receipt.get("source")
    if not isinstance(source, dict):
        raise ReproductionError("receipt source identity is malformed")
    current_identity = source_identity(source_root)
    for field in ("source_digest", "manifest_digest", "file_count", "exclusion_policy"):
        if source.get(field) != current_identity[field]:
            raise ReproductionError(f"source identity mismatch at {field}")

    recorded_plan = receipt.get("required_command_plan")
    if recorded_plan != required_plan:
        raise ReproductionError("receipt command plan does not match the required plan")
    results = receipt.get("command_results")
    if not isinstance(results, list):
        raise ReproductionError("receipt command results are malformed")
    by_id: dict[str, dict[str, Any]] = {}
    for result in results:
        if not isinstance(result, dict) or not isinstance(result.get("id"), str):
            raise ReproductionError("receipt contains a malformed command result")
        if result["id"] in by_id:
            raise ReproductionError(f"duplicate command result: {result['id']}")
        by_id[result["id"]] = result

    for spec in required_plan:
        result = by_id.get(spec["id"])
        if result is None:
            raise ReproductionError(f"missing required command result: {spec['id']}")
        for field in (
            "id",
            "argv",
            "expect_empty_stdout",
            "expect_empty_stderr",
            "requires_git",
        ):
            if result.get(field) != spec[field]:
                raise ReproductionError(f"command result contract mismatch: {spec['id']}")
        if result.get("exit_code") != 0:
            raise ReproductionError(f"command exited nonzero: {spec['id']}")
        command_started = parse_utc(
            result.get("started_at"), f"{spec['id']}.started_at"
        )
        command_completed = parse_utc(
            result.get("completed_at"), f"{spec['id']}.completed_at"
        )
        if command_completed < command_started:
            raise ReproductionError(
                f"command completion precedes its start: {spec['id']}"
            )
        if command_started < started_at or command_completed > completed_at:
            raise ReproductionError(
                f"command timestamps exceed receipt bounds: {spec['id']}"
            )
        for field in ("wall_time_seconds", "user_time_seconds", "sys_time_seconds"):
            require_nonnegative_number(result.get(field), f"{spec['id']}.{field}")
        for stream in ("stdout", "stderr"):
            validate_stream_result(result, spec, stream)
    unexpected = sorted(set(by_id) - {spec["id"] for spec in required_plan})
    if unexpected:
        raise ReproductionError(
            "receipt contains unexpected command result(s): " + ", ".join(unexpected)
        )


def write_receipt(path: Path, receipt: dict[str, Any], *, overwrite: bool) -> None:
    _write_regular_receipt(
        path,
        json.dumps(receipt, ensure_ascii=False, indent=2) + "\n",
        overwrite=overwrite,
    )


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "mode",
        choices=("plan", "run", "validate"),
        help="print the plan, execute it in isolation, or validate a receipt",
    )
    parser.add_argument(
        "--source-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--plan-json", type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--overwrite", action="store_true")
    parser.add_argument(
        "--allow-git",
        action="store_true",
        help="allow plan rows explicitly tagged requires_git",
    )
    parser.add_argument(
        "--max-age-seconds",
        type=int,
        default=DEFAULT_MAX_AGE_SECONDS,
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        plan = load_plan(args.plan_json)
        if args.mode == "plan":
            print(json.dumps(plan, ensure_ascii=False, indent=2))
            return 0
        if args.receipt is None:
            parser.error("--receipt is required for run and validate")
        if args.mode == "run":
            receipt = execute(
                args.source_root,
                plan,
                allow_git=args.allow_git,
            )
            validate_receipt(
                receipt,
                args.source_root,
                plan,
                max_age_seconds=args.max_age_seconds,
            )
            write_receipt(args.receipt, receipt, overwrite=args.overwrite)
            print(
                f"source-bound reproduction passed: "
                f"{len(receipt['command_results'])} commands; "
                f"source={receipt['source']['source_digest'][:12]}"
            )
            return 0
        receipt = _read_regular_json(args.receipt, "receipt")
        if not isinstance(receipt, dict):
            raise ReproductionError("receipt root must be an object")
        validate_receipt(
            receipt,
            args.source_root,
            plan,
            max_age_seconds=args.max_age_seconds,
        )
        print(
            f"source-bound reproduction receipt valid: "
            f"{len(receipt['command_results'])} commands; "
            f"source={receipt['source']['source_digest'][:12]}"
        )
        return 0
    except (
        ReproductionError,
        OSError,
        json.JSONDecodeError,
        subprocess.SubprocessError,
    ) as error:
        print(f"source-bound reproduction failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
